#!/usr/bin/env python3
"""Open one GitHub issue per finding of an upstream overlap scan.

Usage: scripts/overlap/publish.py BUNDLE [--apply]

Reads BUNDLE/result.json, written by an agent following scripts/overlap/scan.md. Without
`--apply` it only prints what it would do. Each issue gets the `upstream-overlap` label and a
marker identifying its finding, so a finding that already has an issue (open or closed) is skipped.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import subprocess
import sys
import tempfile
import tomllib

ROOT = pathlib.Path(__file__).resolve().parents[2]
LABEL = "upstream-overlap"
MARKER = "lmlexplore-overlap:v1"
FIELDS = ("upstream", "direction", "upstream_declarations", "lmlexplore_declarations",
          "classification", "title", "body")


def gh(*args: str) -> str:
    return subprocess.run(["gh", *args], check=True, capture_output=True, text=True).stdout


def key(finding: dict) -> str:
    ident = [finding["upstream"], sorted(finding["upstream_declarations"]),
             sorted(finding["lmlexplore_declarations"])]
    return hashlib.sha256(json.dumps(ident).encode()).hexdigest()[:16]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("bundle", type=pathlib.Path)
    parser.add_argument("--apply", action="store_true", help="create the issues")
    parser.add_argument("--allow-incomplete", action="store_true",
                        help="publish the findings of a scan marked incomplete")
    args = parser.parse_args()

    repo = tomllib.loads((ROOT / "tauceti.toml").read_text())["repositories"]["content"]
    scan = json.loads((args.bundle / "scan.json").read_text())
    result = json.loads((args.bundle / "result.json").read_text())
    if not result.get("complete") and not args.allow_incomplete:
        print(f"error: the scan is incomplete: {result.get('obstruction', 'no reason given')}",
              file=sys.stderr)
        return 1
    findings = result.get("findings", [])
    for i, finding in enumerate(findings):
        missing = [f for f in FIELDS if not finding.get(f)]
        if missing:
            print(f"error: finding {i} lacks {', '.join(missing)}", file=sys.stderr)
            return 1
    if not findings:
        print("No findings.")
        return 0

    existing = json.loads(gh("issue", "list", "--repo", repo, "--label", LABEL, "--state", "all",
                             "--limit", "1000", "--json", "number,body"))
    if args.apply and not existing:
        labels = json.loads(gh("label", "list", "--repo", repo, "--search", LABEL, "--json", "name"))
        if not any(label["name"] == LABEL for label in labels):
            gh("label", "create", LABEL, "--repo", repo, "--color", "5319e7", "--description",
               "LMLExplore material that a dependency now provides")

    for finding in findings:
        k = key(finding)
        duplicate = next((issue["number"] for issue in existing if k in (issue["body"] or "")), None)
        if duplicate:
            print(f"skip   {finding['title']} (already #{duplicate})")
            continue
        upstream = scan["upstreams"].get(finding["upstream"], {})
        marker = {"key": k, "upstream": finding["upstream"],
                  "upstream_declarations": finding["upstream_declarations"],
                  "lmlexplore_declarations": finding["lmlexplore_declarations"]}
        body = (f"{finding['body'].rstrip()}\n\n---\n"
                f"Found by the upstream overlap scan (`scripts/overlap/`): {finding['upstream']} "
                f"`{(upstream.get('from') or '')[:12]}..{(upstream.get('through') or '')[:12]}`, "
                f"LMLExplore `{scan['lmlexplore']['head'][:12]}`, {finding['classification']}, "
                f"{finding['direction']}. Resolve it with `scripts/overlap/fix.md`.\n\n"
                f"<!--{MARKER} {json.dumps(marker)}-->\n")
        if not args.apply:
            print(f"would create: {finding['title']}")
            continue
        with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False) as f:
            f.write(body)
        url = gh("issue", "create", "--repo", repo, "--title", finding["title"],
                 "--label", LABEL, "--body-file", f.name).strip()
        pathlib.Path(f.name).unlink()
        print(f"created {url}")
    if not args.apply:
        print("Dry run; add --apply to create these issues.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
