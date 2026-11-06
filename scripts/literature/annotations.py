#!/usr/bin/env python3
"""Literature Links annotations for LMLExplore, and the page that lists them.

Reads the dataset (S2) that the referee site workflow extracts. In each declaration's docstring,
and in the `## Main ...` lists of the module docstrings, it finds the citations of numbered results
of the literature, such as `[GK16, Theorem 14]`, `[LS, Lemmas 8.2, 8.3]` or `[P, proof of
Theorem 6.2.2]`, and writes to the output folder:

* `annotations.jsonl`: one annotation per declaration and cited result, in the format of
  https://github.com/mathlib-initiative/literature-links. The subject is the result, as a part of
  the work that `bibliography.json` describes; the object is the declaration at the dataset's
  commit. The annotations have no `relation`: they claim that the two sides correspond, not how.
* `index.html`: a page listing, for each work, its cited results and the declarations that cite
  them, with links to the referee site and to the sources.

A citation key that `bibliography.json` does not describe falls back to the text that the modules'
`## References` sections give for it. A citation whose key appears in neither is reported and left
out.

usage: annotations.py --dataset DIR --bibliography FILE --out DIR
"""
from __future__ import annotations

import argparse
import html
import json
import re
import sys
import urllib.parse
from collections import Counter, defaultdict
from pathlib import Path

#: The location convention of a numbered result of a work, defined on the page this script writes.
PROFILE = "https://leanmachinelearning.org/LMLExplore/literature/#numbered-item"

#: The words that introduce a numbered result, in the singular, and the `kind` of an annotation
#: about such a result.
KINDS = {
    "theorem": "theorem", "lemma": "lemma", "proposition": "proposition", "corollary": "corollary",
    "definition": "definition", "example": "example", "exercise": "exercise", "remark": "remark",
    "algorithm": "algorithm", "section": "section", "chapter": "chapter", "note": "note",
    "appendix": "appendix", "equation": "equation", "fact": "fact", "claim": "claim",
    "assumption": "assumption", "problem": "problem", "table": "table", "figure": "figure",
}
PLURALS = {"corollaries": "corollary", "appendices": "appendix"}

CITATION = re.compile(r"\[([A-Z][A-Za-z]*\d*[a-z]?), ([^\[\]]+)\]")
TOKEN = re.compile(
    r"(?P<proof>(?i:proofs? of))"
    r"|(?P<number>[A-Z]?\d+(?:\.\d+)*[a-z]?|[A-Z](?:\.\d+)+|[A-Z](?![A-Za-z]))"
    r"|(?P<kind>§|[A-Za-z]+\.?)"
    r"|(?P<eq>\((?:\d+[.\d]*[a-z]?)\))"
    r"|(?P<part>\([a-z]{1,4}\))"
    r"|(?P<sep>[,;–—-]|\s+)"
    r"|(?P<other>.)")


def kind_of(word: str) -> str | None:
    """The kind of result that a word introduces (`Lemmas` → `lemma`), or None."""
    w = word.lower().rstrip(".")
    if word == "§":
        return "section"
    if w in ("eq", "eqs"):
        return "equation"
    w = PLURALS.get(w, w[:-1] if w.endswith("s") and w[:-1] in KINDS else w)
    return w if w in KINDS else None


def items(locator: str) -> list[tuple[str, str, str | None]]:
    """The numbered results a locator names, as (kind, number, part): `Lemmas 8, 15` gives two
    lemmas, `proof of Theorem 14` the theorem with the part `proof`, `Theorem 6.2.2 (a)` and
    `Lemma 3.4 (1)` the parts `(a)` and `(1)`, and `(8.2)` or `Theorem 20.5 and (20.9)` the equation
    `(8.2)` or `(20.9)`. A word that is not a kind ends a list of numbers."""
    out: list[tuple[str, str, str | None]] = []
    kind: str | None = None
    proof = False
    expecting = False  # numbers follow a kind word, separated by commas and `and`
    previous = None  # the last token that is not a space
    for m in TOKEN.finditer(locator):
        group, text = m.lastgroup, m.group()
        after_number, previous = previous == "number", (previous if text.isspace() else group)
        if group in ("eq", "part") and after_number and out and out[-1][2] is None:
            out[-1] = (out[-1][0], out[-1][1], text)  # `Theorem 6.2.2 (a)`, `Lemma 3.4 (1)`
        elif group == "proof":
            proof, expecting = True, False
        elif group == "kind":
            k = kind_of(text)
            if k is not None:
                kind, expecting = k, True
            elif text.lower() not in ("and", "or"):
                expecting, proof = False, False
        elif group == "number" and expecting and kind is not None:
            out.append((kind, text, "proof" if proof else None))
        elif group == "eq":
            out.append(("equation", text, None))
        elif group == "other":
            expecting, proof = False, False
    return out


def label(kind: str, number: str) -> str:
    """How the work prints the result: `Theorem 14`, `Section 4.3`, `(8.2)`."""
    return number if kind == "equation" else f"{kind.capitalize()} {number}"


#: The order of the kinds of results on the page.
KIND_ORDER = ["definition", "theorem", "proposition", "lemma", "corollary", "fact", "claim", "assumption",
              "algorithm", "example", "exercise", "problem", "remark", "note", "table", "figure", "section",
              "chapter", "appendix", "equation"]


def sort_key(lab: str) -> tuple:
    """Results in reading order: by kind, then by the numbers of their label."""
    head, _, number = lab.partition(" ")
    if lab.startswith("("):
        head, number = "Equation", lab.strip("()")
    kind = head.lower()
    rank = KIND_ORDER.index(kind) if kind in KIND_ORDER else len(KIND_ORDER)
    parts = [(0, int(p), "") if p.isdigit() else (1, 0, p) for p in re.split(r"[.]", number)]
    return (rank, kind, parts)


# --- the dataset ---------------------------------------------------------------------------------

def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


REFERENCE = re.compile(
    r"^\*\s*(?:\[([A-Z][A-Za-z]*\d*[a-z]?)\]\s*(.+?)|\[(.+?)\]\[([A-Z][A-Za-z]*\d*[a-z]?)\].*?)"
    r"(?=^\*|\Z)", re.M | re.S)


def references(blocks: list[str]) -> dict[str, str]:
    """The reference texts of the `## References` sections of a module's docstrings, by key, in
    either form: `* [KEY] text` or `* [text][KEY]`."""
    out = {}
    for block in blocks:
        if "## References" not in block:
            continue
        section = re.split(r"^## ", block.split("## References", 1)[1], flags=re.M)[0]
        for m in REFERENCE.finditer(section):
            key, text = (m.group(1), m.group(2)) if m.group(1) else (m.group(4), m.group(3))
            out[key] = " ".join(text.split()).rstrip(".")
    return out


def main_entries(blocks: list[str]) -> list[tuple[list[str], str]]:
    """The entries of the `## Main ...` lists of a module's docstrings: the names in backquotes before
    the entry's first colon, and the entry's text."""
    out = []
    for block in blocks:
        for section in re.split(r"^## ", block, flags=re.M)[1:]:
            if not section.startswith("Main "):
                continue
            for entry in re.split(r"^\* ", section, flags=re.M)[1:]:
                head = entry.split(":", 1)[0]
                names = [n for n in re.findall(r"`([^`\s]+)`", head)]
                if names:
                    out.append((names, " ".join(entry.split())))
    return out


def readable(name: str) -> str:
    """A declaration's name as Lean prints it in its own module: a private declaration's internal
    name `_private.Module.0.Name` is `Name`."""
    m = re.fullmatch(r"_private\.(?:[^.]+\.)*?0\.(.+)", name)
    return m.group(1) if m else name


def resolve(name: str, decls: list[str]) -> str | None:
    """The declaration of a module that a name in its docstring refers to: the declaration itself,
    or the only one whose full name ends with `.name`."""
    if name in decls:
        return name
    matches = [d for d in decls if readable(d) == name or readable(d).endswith("." + name)]
    return matches[0] if len(matches) == 1 else None


# --- the annotations -----------------------------------------------------------------------------

def end_type(uri: str) -> str:
    if uri.lower().endswith(".pdf"):
        return "pdf"
    return "html" if uri.startswith(("https://", "http://")) else "generic"


def build(dataset: Path, bibliography: dict, out: Path) -> dict:
    meta = json.loads((dataset / "meta.json").read_text(encoding="utf-8"))
    library = meta["library"]
    repo, commit, package = library["repo"], library["commit"], library["package"]
    decls = {d["name"]: d for d in read_jsonl(dataset / "decls.jsonl") if d["package"] == package}
    docstrings = {r["decl"]: r["text"] for r in read_jsonl(dataset / "facets" / "docstring.jsonl")
                  if r["decl"] in decls}
    sources = {r["decl"]: r for r in read_jsonl(dataset / "facets" / "source.jsonl") if r["decl"] in decls}
    modules = read_jsonl(dataset / "modules.jsonl")
    by_module: dict[str, list[str]] = defaultdict(list)
    for name, d in decls.items():
        by_module[d["module"]].append(name)

    texts: dict[str, Counter] = defaultdict(Counter)
    for m in modules:
        for key, text in references(m["doc"]).items():
            texts[key][text] += 1

    # (declaration, key, label) → the part, if any, and where the citation was found
    found: dict[tuple[str, str, str], dict] = {}
    unknown: Counter = Counter()
    unparsed: Counter = Counter()

    def cite(decl: str, text: str, origin: str) -> None:
        for key, locator in CITATION.findall(text):
            if key not in bibliography and key not in texts:
                unknown[key] += 1
                continue
            parsed = items(locator)
            if not parsed:
                unparsed[f"[{key}, {locator}]"] += 1
            for kind, number, part in parsed:
                entry = found.setdefault((decl, key, label(kind, number)),
                                         {"kind": kind, "parts": set(), "origins": set()})
                if part:
                    entry["parts"].add(part)
                entry["origins"].add(origin)

    for name, text in docstrings.items():
        cite(name, text, "docstring")
    for m in modules:
        for names, text in main_entries(m["doc"]):
            for n in names:
                decl = resolve(n, by_module.get(m["name"], []))
                if decl is not None:
                    cite(decl, text, "module docstring")

    def work(key: str) -> dict:
        if key in bibliography:
            return bibliography[key]
        text = texts[key].most_common(1)[0][0]
        return {"uri": f"urn:lmlexplore:reference:{key}",
                "citation": {"id": key, "type": "document", "title": text}}

    annotations = []
    internal = []  # each annotation's declaration, by its name in the dataset
    for (decl, key, lab), entry in sorted(found.items(), key=lambda kv: (kv[0][1], sort_key(kv[0][2]), kv[0][0])):
        w = work(key)
        parts = sorted(entry["parts"])
        proof = parts == ["proof"]
        location = {"profile": PROFILE, "label": lab}
        if parts and not proof:
            location["part"] = ", ".join(parts)
        subject = {"type": end_type(w["uri"]), "uri": w["uri"]}
        if "version" in w:
            subject["version"] = w["version"]
        subject.update({"location": location,
                        "title": f"Proof of {lab}" if proof else lab + (f" {location['part']}" if "part" in location else ""),
                        "citation": w["citation"]})
        if "identifiers" in w:
            subject["identifiers"] = w["identifiers"]
        annotations.append({
            "subject": [subject],
            "object": [{"type": "lean", "uri": f"https://github.com/{repo}", "version": commit,
                        "location": {"declaration": readable(decl), "module": decls[decl]["module"]}}],
            "kind": "proof" if proof else KINDS[entry["kind"]],
            "id": f"{key}:{lab}",
        })
        internal.append(decl)

    out.mkdir(parents=True, exist_ok=True)
    (out / "annotations.jsonl").write_text(
        "".join(json.dumps(a, ensure_ascii=False, separators=(",", ":")) + "\n" for a in annotations),
        encoding="utf-8")
    page = render(list(zip(annotations, internal)), sources, repo, commit,
                  {k: work(k) for k in {a["id"].split(":")[0] for a in annotations}})
    (out / "index.html").write_text(page, encoding="utf-8")
    return {"annotations": len(annotations), "declarations": len({a["object"][0]["location"]["declaration"] for a in annotations}),
            "results": len({a["id"] for a in annotations}), "works": len({a["id"].split(":")[0] for a in annotations}),
            "unknown": unknown, "unparsed": unparsed}


# --- the page ------------------------------------------------------------------------------------

def authors(citation: dict) -> str:
    names = [" ".join(filter(None, [a.get("given"), a.get("family")])) for a in citation.get("author", [])]
    return names[0] if len(names) == 1 else ", ".join(names[:-1]) + " and " + names[-1] if names else ""


def reference(w: dict) -> str:
    """A work, as a line of HTML: authors, title, where it appeared, year, and its links."""
    c = w["citation"]
    if c.get("type") == "document" and "author" not in c:  # a fallback: the modules' own text
        return html.escape(c["title"]).replace("*", "")
    year = c.get("issued", {}).get("date-parts", [[None]])[0][0]
    where = c.get("container-title") or c.get("publisher") or ""
    parts = [html.escape(authors(c)), f"<em>{html.escape(c['title'])}</em>", html.escape(where), str(year or "")]
    links = []
    if w["uri"].startswith("http"):
        links.append(f'<a href="{html.escape(w["uri"])}">link</a>')
    arxiv = w.get("identifiers", {}).get("arxiv")
    if arxiv:
        links.append(f"arXiv:{html.escape(arxiv)}{html.escape(w.get('version', ''))}")
    if c.get("DOI"):
        links.append(f"doi:{html.escape(c['DOI'])}")
    return ", ".join(p for p in parts if p) + (" · " + " · ".join(links) if links else "")


def render(records: list[tuple[dict, str]], sources: dict, repo: str, commit: str, works: dict) -> str:
    """The page: the works by number of cited results, each result with the declarations citing it."""
    by_work: dict[str, dict[str, list[tuple[dict, str]]]] = defaultdict(lambda: defaultdict(list))
    for a, decl in records:
        key, lab = a["id"].split(":", 1)
        by_work[key][lab].append((a, decl))
    order = sorted(by_work, key=lambda k: (-len(by_work[k]), k))
    rows = []
    for key in order:
        results = by_work[key]
        items_html = []
        for lab in sorted(results, key=sort_key):
            decls = []
            for a, decl in sorted(results[lab], key=lambda r: r[0]["object"][0]["location"]["declaration"]):
                name = a["object"][0]["location"]["declaration"]
                private = " <span class=part>private</span>" if name != decl else ""
                s = sources.get(decl)
                src = (f' <a class="src" href="https://github.com/{repo}/blob/{commit}/{s["path"]}#L{s["start"][0]}">source</a>'
                       if s else "")
                extra = a["subject"][0]["title"][len(lab):].strip() if a["subject"][0]["title"].startswith(lab) else "proof"
                decls.append(f'<li><a href="../#/d/{urllib.parse.quote(decl, safe="")}"><code>{html.escape(name)}</code></a>'
                             f'{private}{" <span class=part>" + html.escape(extra) + "</span>" if extra else ""}{src}</li>')
            names = " ".join(a["object"][0]["location"]["declaration"] for a, _ in results[lab])
            items_html.append(f'<li class="result" data-text="{html.escape((key + " " + lab + " " + names).lower())}">'
                              f'<span class="label">{html.escape(lab)}</span><ul>{"".join(decls)}</ul></li>')
        rows.append(f'<section class="work" id="{html.escape(key)}"><h2><span class="key">[{html.escape(key)}]</span> '
                    f'{reference(works[key])}</h2><p class="count">{len(results)} result{"s" * (len(results) != 1)}</p>'
                    f'<ul class="results">{"".join(items_html)}</ul></section>')
    n_decls = len({decl for _, decl in records})
    n_results = len({a["id"] for a, _ in records})
    template = (Path(__file__).with_name("page.html")).read_text(encoding="utf-8")
    return (template.replace("{{works}}", "\n".join(rows))
            .replace("{{summary}}", f"{n_results} results of {len(by_work)} works, cited by {n_decls} declarations "
                     f"({len(records)} annotations)")
            .replace("{{commit}}", html.escape(commit)).replace("{{commit12}}", html.escape(commit[:12]))
            .replace("{{repo}}", html.escape(repo)).replace("{{profile}}", html.escape(PROFILE)))


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--dataset", type=Path, required=True, help="the S2 dataset extracted by trust-extract")
    p.add_argument("--bibliography", type=Path, required=True, help="the works, by citation key")
    p.add_argument("--out", type=Path, required=True, help="the folder to write to")
    args = p.parse_args()
    bibliography = json.loads(args.bibliography.read_text(encoding="utf-8"))
    stats = build(args.dataset, bibliography, args.out)
    print(f"{stats['annotations']} annotations: {stats['results']} results of {stats['works']} works, "
          f"cited by {stats['declarations']} declarations")
    for key, n in stats["unknown"].most_common():
        print(f"::warning::citation key {key} ({n} citations) is in neither bibliography.json nor a "
              f"`## References` section", file=sys.stderr)
    if stats["unparsed"]:
        print(f"{sum(stats['unparsed'].values())} citations name no numbered result, e.g. "
              + "; ".join(k for k, _ in stats["unparsed"].most_common(5)), file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
