#!/usr/bin/env python3
"""Collect the material for an upstream overlap scan of LMLExplore.

Run after a dependency sync has landed and the dependencies are checked out at their new pins
(for example after `scripts/build.sh`). See `scripts/overlap/README.md` for the procedure.

The scan looks in two directions:

1. what each upstream with `overlap = true` in `tauceti.toml` (Mathlib, Tau Ceti, LML) added or
   changed between its previous pin and its current one, to be compared against LMLExplore;
2. what LMLExplore added or changed since the previous sync, to be compared against the
   current pinned upstreams. This catches duplicates that review could not see.

The previous pins are read from `lake-manifest.json` at the `--since` commit, by default the
previous commit that changed `lake-manifest.json`. With no previous sync, direction 1 is empty
and direction 2 covers all of LMLExplore.

The output is a bundle directory under `.lake/overlap-scan/`, holding plain-text declaration
lists and `scan.json`. Nothing is written outside it, and nothing is sent anywhere.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import pathlib
import re
import subprocess
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parents[2]

# A declaration header at the start of a line, possibly after attributes and modifiers.
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|public|scoped|local)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|class|inductive|irreducible_def|opaque|alias)"
    r"\b\s*(.*)$"
)
HUNK_RE = re.compile(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,\d+)? @@")


def git(*args: str, cwd: pathlib.Path) -> str:
    return subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True,
                          text=True).stdout


def decl(line: str) -> tuple[str, str] | None:
    """The kind and name of a declaration header line, or None. Anonymous instances get `_`."""
    m = DECL_RE.match(line)
    if not m:
        return None
    kind, rest = m.group(1), m.group(2).strip()
    if kind == "class" and rest.startswith("inductive"):
        kind, rest = "class inductive", rest[len("inductive"):].strip()
    name = rest.split()[0] if rest else ""
    if not name or name[0] in ":([{⦃" or name == "where":
        name = "_"
    return kind, name.rstrip(":")


def diff_decls(repo: pathlib.Path, old: str, new: str, pathspec: str) -> list[dict]:
    """Declarations added or changed in `old..new`, ignoring pure moves.

    A header line removed and re-added verbatim is a move. A name removed with one header and
    added with another is a changed statement. Any other added header is new."""
    out = git("diff", "-U0", "--no-color", "--no-ext-diff", old, new, "--", pathspec, cwd=repo)
    added: list[dict] = []
    removed_lines: set[str] = set()
    removed_names: set[tuple[str, str]] = set()
    path, line_no = "", 0
    for raw in out.splitlines():
        if raw.startswith("+++ "):
            path = raw[6:] if raw.startswith("+++ b/") else ""
            continue
        if raw.startswith("--- "):
            continue
        hunk = HUNK_RE.match(raw)
        if hunk:
            line_no = int(hunk.group(1))
            continue
        if raw.startswith("-"):
            text = raw[1:].rstrip()
            d = decl(text)
            if d:
                removed_lines.add(text)
                removed_names.add(d)
        elif raw.startswith("+"):
            text = raw[1:].rstrip()
            d = decl(text)
            if d and path:
                added.append({"file": path, "line": line_no, "kind": d[0], "name": d[1],
                              "header": text})
            line_no += 1
    result = []
    for a in added:
        if a["header"] in removed_lines:
            continue
        a["status"] = "changed" if (a["kind"], a["name"]) in removed_names else "new"
        result.append(a)
    return result


def tree_decls(directory: pathlib.Path, root: pathlib.Path) -> list[dict]:
    """Every declaration header in the `.lean` files under `directory`."""
    result = []
    for file in sorted(directory.rglob("*.lean")):
        for i, text in enumerate(file.read_text(encoding="utf-8").splitlines(), start=1):
            d = decl(text)
            if d:
                result.append({"file": str(file.relative_to(root)), "line": i, "kind": d[0],
                               "name": d[1], "header": text.rstrip(), "status": "current"})
    return result


def write_list(path: pathlib.Path, title: str, decls: list[dict]) -> None:
    lines = [f"# {title}", f"# {len(decls)} declarations; format: file:line: [status] kind name | header"]
    folders: dict[str, int] = {}
    for d in decls:
        folder = "/".join(d["file"].split("/")[:3])
        folders[folder] = folders.get(folder, 0) + 1
    if len(folders) > 1:
        lines.append("# Declarations per folder:")
        lines += [f"#   {n:6} {folder}" for folder, n in sorted(folders.items(), key=lambda x: -x[1])]
    lines.append("")
    lines += [f"{d['file']}:{d['line']}: [{d['status']}] {d['kind']} {d['name']} | {d['header']}"
              for d in decls]
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def manifest_revs(text: str) -> dict[str, str]:
    return {p["name"]: p["rev"] for p in json.loads(text)["packages"]}


def ensure_commit(repo: pathlib.Path, rev: str) -> None:
    if subprocess.run(["git", "cat-file", "-e", f"{rev}^{{commit}}"], cwd=repo,
                      capture_output=True).returncode != 0:
        git("fetch", "-q", "origin", rev, cwd=repo)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--since", help="LMLExplore commit of the previous sync "
                        "(default: the previous commit that changed lake-manifest.json)")
    parser.add_argument("--old", action="append", default=[], metavar="PACKAGE=REV",
                        help="override the previous pin of one upstream package")
    parser.add_argument("--out", type=pathlib.Path, help="bundle directory to create")
    args = parser.parse_args()

    config = tomllib.loads((ROOT / "tauceti.toml").read_text())
    lean_root = config["lean"]["roots"][0]
    upstreams = [u["package"] for u in config.get("upstreams", []) if u.get("overlap")]
    new_pins = manifest_revs((ROOT / "lake-manifest.json").read_text())

    since = args.since
    if since is None:
        syncs = git("log", "--format=%H", "--", "lake-manifest.json", cwd=ROOT).split()
        since = syncs[1] if len(syncs) > 1 else None
    old_pins = (manifest_revs(git("show", f"{since}:lake-manifest.json", cwd=ROOT))
                if since else {})
    for override in args.old:
        package, _, rev = override.partition("=")
        if package not in upstreams or not rev:
            parser.error(f"--old expects PACKAGE=REV with PACKAGE among {upstreams}")
        old_pins[package] = rev

    stamp = dt.datetime.now().strftime("%Y%m%d-%H%M%S")
    bundle = (args.out or ROOT / ".lake" / "overlap-scan" / stamp).resolve()
    bundle.mkdir(parents=True, exist_ok=False)
    head = git("rev-parse", "HEAD", cwd=ROOT).strip()
    meta: dict = {"lmlexplore": {"head": head, "since": since}, "upstreams": {},
                  "bundle": str(bundle), "result": str(bundle / "result.json")}

    for package in upstreams:
        repo = ROOT / ".lake" / "packages" / package
        new = new_pins[package]
        checked_out = git("rev-parse", "HEAD", cwd=repo).strip()
        if checked_out != new:
            print(f"error: .lake/packages/{package} is at {checked_out[:12]}, but the manifest pins "
                  f"{new[:12]}; run scripts/build.sh first", file=sys.stderr)
            return 1
        old = old_pins.get(package)
        entry = {"source": f".lake/packages/{package}", "through": new, "from": old}
        if old and old != new:
            ensure_commit(repo, old)
            # Private upstream declarations cannot be reused, so they cannot supersede anything.
            decls = [d for d in diff_decls(repo, old, new, "*.lean")
                     if not re.search(r"\bprivate\b", d["header"].split(d["kind"])[0])]
            entry["commits"] = int(git("rev-list", "--count", f"{old}..{new}", cwd=repo))
        else:
            decls = []
            entry["commits"] = 0
        entry["declarations"] = len(decls)
        entry["list"] = f"upstream-{package}.txt"
        write_list(bundle / entry["list"],
                   f"{package}: declarations added or changed in {(old or new)[:12]}..{new[:12]}",
                   decls)
        meta["upstreams"][package] = entry

    if since:
        own_new = diff_decls(ROOT, since, "HEAD", f"{lean_root}/")
        own_title = f"LMLExplore: declarations added or changed in {since[:12]}..{head[:12]}"
    else:
        own_new = tree_decls(ROOT / lean_root, ROOT)
        own_title = "LMLExplore: all declarations (no previous sync)"
    write_list(bundle / "lmlexplore-new.txt", own_title, own_new)
    own_all = tree_decls(ROOT / lean_root, ROOT)
    write_list(bundle / "lmlexplore-all.txt", f"LMLExplore: all declarations at {head[:12]}",
               own_all)
    meta["lmlexplore"].update({"new": len(own_new), "all": len(own_all)})
    (bundle / "scan.json").write_text(json.dumps(meta, indent=2) + "\n")

    print(f"Bundle: {bundle}")
    for package, entry in meta["upstreams"].items():
        span = (f"{entry['from'][:12]}..{entry['through'][:12]}, {entry['commits']} commits"
                if entry["from"] and entry["from"] != entry["through"] else "no change")
        print(f"  {package}: {span}, {entry['declarations']} declarations to compare")
    print(f"  LMLExplore: {len(own_new)} new or changed declarations, {len(own_all)} in total")
    print("Next: have an agent follow scripts/overlap/scan.md with this bundle, for example\n"
          f"  claude \"Follow scripts/overlap/scan.md with the bundle {bundle}\"")
    return 0


if __name__ == "__main__":
    sys.exit(main())
