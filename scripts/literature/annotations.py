#!/usr/bin/env python3
"""Literature Links annotations for LMLExplore, and the page that lists them.

Reads the dataset (S2) that the referee site workflow extracts, and a checkout of LMLRoadmaps. It
finds the citations of numbered results of the literature, such as `[GK16, Theorem 14]`,
`[LS, Lemmas 12.2–12.4]` or `[P, proof of Theorem 6.2.2]`:

* in each declaration's docstring, and in the `## Main ...` lists of the module docstrings: the
  declarations that cite each result;
* in the roadmaps: the results that LMLExplore aims at, and the roadmap items that cite them.

It writes to the output folder:

* `annotations.jsonl`, in the format of https://github.com/mathlib-initiative/literature-links:
  one annotation per declaration and result it cites, whose object is the declaration at the
  dataset's commit; and one per result that the roadmaps cite and no declaration does, whose object
  is empty (not linked yet). In both, the subject is the result, as a part of its work. The
  annotations have no `relation`: they claim that the two sides correspond, not how. The extension
  `org.leanmachinelearning.lmlroadmaps` of an annotation names the roadmap items that cite its
  result.
* `index.html`: a page listing, for each work, its results, the declarations and the roadmap items
  that cite them, and how many of the results that the roadmaps cite have a declaration.

A key that `bibliography.json` maps to another one with `{"same": KEY}` is that work: two roadmaps or
modules may cite one work under two keys. A citation key that `bibliography.json` does not describe
falls back to the text that the modules' `## References` sections, then the roadmaps' References,
give for it. A citation whose key appears
in none of them is reported and left out.

usage: annotations.py --dataset DIR --bibliography FILE --out DIR [--roadmaps DIR]
       [--roadmaps-commit SHA]
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
#: The extension naming the roadmap items that cite an annotation's result.
ROADMAPS = "org.leanmachinelearning.lmlroadmaps"
ROADMAPS_REPO = "LeanMachineLearning/LMLRoadmaps"

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
#: Places in a work rather than results: cited by the roadmaps, they count in no coverage.
PLACES = {"section", "chapter", "appendix", "figure", "table"}
#: The most results a range such as `Lemmas 24–27` expands to.
MAX_RANGE = 30

CITATION = re.compile(r"\[([A-Z][A-Za-z]*\d*[a-z]?), ([^\[\]]+)\]")
TOKEN = re.compile(
    r"(?P<proof>(?i:proofs? of))"
    r"|(?P<number>[A-Z]?\d+(?:\.\d+)*[a-z]?|[A-Z](?:\.\d+)+|[A-Z](?![A-Za-z]))"
    r"|(?P<kind>§|[A-Za-z]+\.?)"
    r"|(?P<eq>\((?:\d+[.\d]*[a-z]?)\))"
    r"|(?P<part>\([a-z]{1,4}\))"
    r"|(?P<dash>[–—-])"
    r"|(?P<sep>[,;]|\s+)"
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


def expand(first: str, last: str) -> list[str]:
    """The numbers of a range, `first` excluded: `28`–`30` gives `29`, `30`, and `12.2`–`12.4`
    gives `12.3`, `12.4`. A range of other numbers, or a longer one, gives its last number only."""
    a, b = first.rsplit(".", 1) if "." in first else ("", first), last.rsplit(".", 1) if "." in last else ("", last)
    if a[0] == b[0] and a[1].isdigit() and b[1].isdigit() and 0 < int(b[1]) - int(a[1]) <= MAX_RANGE:
        prefix = a[0] + "." if a[0] else ""
        return [f"{prefix}{n}" for n in range(int(a[1]) + 1, int(b[1]) + 1)]
    return [last]


def items(locator: str) -> list[tuple[str, str, str | None]]:
    """The numbered results a locator names, as (kind, number, part): `Lemmas 8, 15` gives two
    lemmas, `Lemmas 12.2–12.4` three, `proof of Theorem 14` the theorem with the part `proof`,
    `Theorem 6.2.2 (a)` and `Lemma 3.4 (1)` the parts `(a)` and `(1)`, and `(8.2)` or
    `Theorem 20.5 and (20.9)` the equation `(8.2)` or `(20.9)`. A word that is not a kind ends a list
    of numbers."""
    out: list[tuple[str, str, str | None]] = []
    kind: str | None = None
    proof = False
    expecting = False  # numbers follow a kind word, separated by commas, dashes and `and`
    in_range = False  # the last number was followed by a dash
    previous = None  # the last token that is not a space
    for m in TOKEN.finditer(" ".join(locator.split())):
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
            numbers = expand(out[-1][1], text) if in_range and out and out[-1][0] == kind else [text]
            out.extend((kind, n, "proof" if proof else None) for n in numbers)
        elif group == "eq":
            out.append(("equation", text, None))
        elif group == "other":
            expecting, proof = False, False
        in_range = group == "dash" and after_number or (in_range and text.isspace())
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


# --- reference texts -----------------------------------------------------------------------------

REFERENCE = re.compile(
    r"^[*-]\s*(?:\[([A-Z][A-Za-z]*\d*[a-z]?)\]\s*(.+?)|\[(.+?)\]\[([A-Z][A-Za-z]*\d*[a-z]?)\].*?)"
    r"(?=^[*-]|^\s*$|\Z)", re.M | re.S)


def references(text: str) -> dict[str, str]:
    """The reference texts of the `## References` section of a docstring or a roadmap, by key, in
    either form: `* [KEY] text` or `* [text][KEY]` (or with `-` bullets)."""
    if "## References" not in text:
        return {}
    section = re.split(r"^## ", text.split("## References", 1)[1], flags=re.M)[0]
    out = {}
    for m in REFERENCE.finditer(section):
        key, value = (m.group(1), m.group(2)) if m.group(1) else (m.group(4), m.group(3))
        out[key] = " ".join(value.split()).rstrip(".")
    return out


# --- the dataset ---------------------------------------------------------------------------------

def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


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


# --- the roadmaps --------------------------------------------------------------------------------

def slug(heading: str) -> str:
    """The anchor GitHub gives a Markdown heading."""
    return re.sub(r"\s", "-", re.sub(r"[^\w\s-]", "", heading.strip().lower()))


def roadmaps(root: Path, commit: str) -> tuple[list[tuple[str, str, str]], dict[str, str], dict[str, str]]:
    """The citations in the roadmaps as (key, locator, item), their reference texts by key, and the
    link of each item. An item is `Area N.k`, the `k`-th target of the layer `N` of the roadmap of
    `Area`, or `Area` for a citation outside the layers. The References sections cite nothing."""
    citations: list[tuple[str, str, str]] = []
    texts: dict[str, str] = {}
    links: dict[str, str] = {}
    for path in sorted(root.rglob("README.md")):
        if path.parent == root:
            continue
        rel = path.relative_to(root).as_posix()
        area = path.parent.name
        text = path.read_text(encoding="utf-8")
        texts.update(references(text))
        body = text.split("\n## References", 1)[0]
        # the headings and the numbered targets, by position
        marks = [(m.start(), "h", m.group(1)) for m in re.finditer(r"^## (.+)$", body, re.M)]
        marks += [(m.start(), "i", m.group(1)) for m in re.finditer(r"^(\d+)\. ", body, re.M)]
        marks.sort()
        for m in CITATION.finditer(body):
            heading, item = None, None
            for pos, what, value in marks:
                if pos > m.start():
                    break
                if what == "h":
                    heading, item = value, None
                else:
                    item = value
            layer = re.match(r"Layer (\d+)\b", heading or "")
            ref = f"{area} {layer.group(1)}.{item}" if layer and item else area
            links.setdefault(ref, f"https://github.com/{ROADMAPS_REPO}/blob/{commit}/{rel}"
                             + (f"#{slug(heading)}" if layer else ""))
            citations.append((m.group(1), m.group(2), ref))
    return citations, texts, links


# --- the annotations -----------------------------------------------------------------------------

def end_type(uri: str) -> str:
    if uri.lower().endswith(".pdf"):
        return "pdf"
    return "html" if uri.startswith(("https://", "http://")) else "generic"


def item_sort(ref: str) -> tuple:
    area, _, number = ref.partition(" ")
    return (area, [int(n) for n in number.split(".")] if number else [])


def build(dataset: Path, bibliography: dict, out: Path, roadmap_root: Path | None, roadmap_commit: str) -> dict:
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

    module_texts: dict[str, Counter] = defaultdict(Counter)
    for m in modules:
        for block in m["doc"]:
            for key, text in references(block).items():
                module_texts[key][text] += 1
    roadmap_citations, roadmap_texts, item_links = (
        roadmaps(roadmap_root, roadmap_commit) if roadmap_root else ([], {}, {}))

    def canonical(key: str) -> str:
        return bibliography.get(key, {}).get("same", key)

    def known(key: str) -> bool:
        return key in bibliography or key in module_texts or key in roadmap_texts

    def work(key: str) -> dict:
        if key in bibliography:
            return bibliography[key]
        text = module_texts[key].most_common(1)[0][0] if key in module_texts else roadmap_texts[key]
        fallback = {"uri": f"urn:lmlexplore:reference:{key}"}
        arxiv = re.search(r"arXiv[: ]\s*(\d{4}\.\d{4,5})(v\d+)?", text)
        if arxiv:  # the text names an arXiv preprint, and its revision if it names one
            fallback = {"uri": f"https://arxiv.org/abs/{arxiv.group(1)}", "identifiers": {"arxiv": arxiv.group(1)}}
            if arxiv.group(2):
                fallback["version"] = arxiv.group(2)
        return {**fallback, "citation": {"id": key, "type": "document", "title": text}}

    kinds: dict[tuple[str, str], str] = {}
    # (key, label) → declaration → the parts it cites, if any
    links: dict[tuple[str, str], dict[str, set]] = defaultdict(lambda: defaultdict(set))
    # (key, label) → the roadmap items that cite it
    cited: dict[tuple[str, str], set] = defaultdict(set)
    unknown: Counter = Counter()
    unparsed: Counter = Counter()

    def results(key: str, locator: str):
        key = canonical(key)
        if not known(key):
            unknown[key] += 1
            return []
        parsed = items(locator)
        if not parsed:
            unparsed[f"[{key}, {' '.join(locator.split())}]"] += 1
        for kind, number, part in parsed:
            kinds.setdefault((key, label(kind, number)), kind)
        return [((key, label(kind, number)), part) for kind, number, part in parsed]

    def cite(decl: str, text: str) -> None:
        for key, locator in CITATION.findall(text):
            for result, part in results(key, locator):
                parts = links[result][decl]
                if part:
                    parts.add(part)

    for name, text in docstrings.items():
        cite(name, text)
    for m in modules:
        for names, text in main_entries(m["doc"]):
            for n in names:
                decl = resolve(n, by_module.get(m["name"], []))
                if decl is not None:
                    cite(decl, text)
    for key, locator, ref in roadmap_citations:
        for result, _ in results(key, locator):
            cited[result].add(ref)

    def subject(key: str, lab: str, part: str | None) -> dict:
        w = work(key)
        location = {"profile": PROFILE, "label": lab}
        if part and part != "proof":
            location["part"] = part
        end = {"type": end_type(w["uri"]), "uri": w["uri"]}
        if "version" in w:
            end["version"] = w["version"]
        end.update({"location": location,
                    "title": f"Proof of {lab}" if part == "proof" else lab + (f" {part}" if part else ""),
                    "citation": w["citation"]})
        if "identifiers" in w:
            end["identifiers"] = w["identifiers"]
        return end

    def roadmap_extension(result: tuple[str, str]) -> dict:
        if result not in cited:
            return {}
        return {"extensions": {ROADMAPS: {"repository": f"https://github.com/{ROADMAPS_REPO}", "version": roadmap_commit,
                                          "items": sorted(cited[result], key=item_sort)}}}

    annotations: list[dict] = []
    records: list[tuple[dict, str | None]] = []  # each annotation, with its declaration's name in the dataset
    every = sorted(set(links) | {r for r in cited if kinds[r] not in PLACES}, key=lambda r: (r[0], sort_key(r[1])))
    for result in every:
        key, lab = result
        for decl in sorted(links.get(result, {})):
            parts = sorted(links[result][decl])
            part = ", ".join(parts) if parts else None
            a = {"subject": [subject(key, lab, part)],
                 "object": [{"type": "lean", "uri": f"https://github.com/{repo}", "version": commit,
                             "location": {"declaration": readable(decl), "module": decls[decl]["module"]}}],
                 "kind": "proof" if part == "proof" else KINDS[kinds[result]],
                 "id": f"{key}:{lab}", **roadmap_extension(result)}
            annotations.append(a)
            records.append((a, decl))
        if result not in links:  # cited by the roadmaps only: not linked yet
            a = {"subject": [subject(key, lab, None)], "object": [], "kind": KINDS[kinds[result]],
                 "id": f"{key}:{lab}", **roadmap_extension(result)}
            annotations.append(a)
            records.append((a, None))

    out.mkdir(parents=True, exist_ok=True)
    (out / "annotations.jsonl").write_text(
        "".join(json.dumps(a, ensure_ascii=False, separators=(",", ":")) + "\n" for a in annotations),
        encoding="utf-8")
    keys = sorted({a["id"].split(":")[0] for a in annotations})
    page = render(records, sources, repo, commit, {k: work(k) for k in keys}, item_links, roadmap_commit,
                  {r for r in cited if kinds[r] not in PLACES})
    (out / "index.html").write_text(page, encoding="utf-8")
    goals = {r for r in cited if kinds[r] not in PLACES}
    return {"annotations": len(annotations), "linked": sum(a["object"] != [] for a in annotations),
            "declarations": len({d for _, d in records if d}), "results": len(links), "works": len(keys),
            "goals": len(goals), "covered": len(goals & set(links)), "unknown": unknown, "unparsed": unparsed}


# --- the page ------------------------------------------------------------------------------------

def authors(citation: dict) -> str:
    names = [" ".join(filter(None, [a.get("given"), a.get("family")])) for a in citation.get("author", [])]
    return names[0] if len(names) == 1 else ", ".join(names[:-1]) + " and " + names[-1] if names else ""


def reference(w: dict) -> str:
    """A work, as a line of HTML: authors, title, where it appeared, year, and its links."""
    c = w["citation"]
    links = []
    if w["uri"].startswith("http"):
        links.append(f'<a href="{html.escape(w["uri"])}">link</a>')
    arxiv = w.get("identifiers", {}).get("arxiv")
    if arxiv:
        links.append(f"arXiv:{html.escape(arxiv)}{html.escape(w.get('version', ''))}")
    if c.get("type") == "document" and "author" not in c:  # a fallback: the text of a References section
        return html.escape(c["title"]).replace("*", "") + (" · " + " · ".join(links) if links else "")
    year = c.get("issued", {}).get("date-parts", [[None]])[0][0]
    where = c.get("container-title") or c.get("publisher") or ""
    parts = [html.escape(authors(c)), f"<em>{html.escape(c['title'])}</em>", html.escape(where), str(year or "")]
    if c.get("DOI"):
        links.append(f"doi:{html.escape(c['DOI'])}")
    return ", ".join(p for p in parts if p) + (" · " + " · ".join(links) if links else "")


def meter(covered: int, total: int) -> str:
    pct = round(100 * covered / total) if total else 0
    return (f'<span class="meter" role="img" aria-label="{covered} of {total}"><span style="width:{pct}%"></span></span>'
            f' {covered} of {total}')


def render(records: list[tuple[dict, str | None]], sources: dict, repo: str, commit: str, works: dict,
           item_links: dict, roadmap_commit: str, goals: set) -> str:
    """The page: the works by number of results, each result with the declarations and the roadmap
    items citing it, and the coverage of the results that the roadmaps cite."""
    by_work: dict[str, dict[str, list[tuple[dict, str | None]]]] = defaultdict(lambda: defaultdict(list))
    for a, decl in records:
        key, lab = a["id"].split(":", 1)
        by_work[key][lab].append((a, decl))
    linked = {(k, lab) for k, results in by_work.items() for lab, rs in results.items() if any(d for _, d in rs)}

    def chips(refs: list[str]) -> str:
        return "".join(f' <a class="chip" href="{html.escape(item_links.get(r, ""))}">{html.escape(r)}</a>' for r in refs)

    rows = []
    for key in sorted(by_work, key=lambda k: (-len(by_work[k]), k)):
        results = by_work[key]
        items_html = []
        for lab in sorted(results, key=sort_key):
            rs = results[lab]
            refs = rs[0][0].get("extensions", {}).get(ROADMAPS, {}).get("items", [])
            decls = []
            for a, decl in sorted((r for r in rs if r[1]), key=lambda r: r[0]["object"][0]["location"]["declaration"]):
                name = a["object"][0]["location"]["declaration"]
                private = " <span class=tag>private</span>" if name != decl else ""
                title = a["subject"][0]["title"]
                extra = title[len(lab):].strip() if title.startswith(lab) else "proof"
                s = sources.get(decl)
                src = (f' <a class="src" href="https://github.com/{repo}/blob/{commit}/{s["path"]}#L{s["start"][0]}">source</a>'
                       if s else "")
                decls.append(f'<li><a href="../#/d/{urllib.parse.quote(decl, safe="")}"><code>{html.escape(name)}</code></a>'
                             f'{private}{" <span class=tag>" + html.escape(extra) + "</span>" if extra else ""}{src}</li>')
            if not decls:
                decls.append('<li class="none">not linked yet</li>')
            names = " ".join(a["object"][0]["location"]["declaration"] for a, d in rs if d)
            cls = "result" + ("" if (key, lab) in linked else " unlinked")
            roadmap = f'<div class="items">cited by{chips(refs)}</div>' if refs else ""
            items_html.append(f'<li class="{cls}" data-text="{html.escape((key + " " + lab + " " + names + " " + " ".join(refs)).lower())}">'
                              f'<span class="label">{html.escape(lab)}</span><div><ul>{"".join(decls)}</ul>{roadmap}</div></li>')
        work_goals = {lab for (k, lab) in goals if k == key}
        n_linked = sum((key, lab) in linked for lab in results)
        coverage = (f' · the roadmaps cite {len(work_goals)}: {meter(len(work_goals & {lab for (k, lab) in linked if k == key}), len(work_goals))} have a declaration'
                    if work_goals else "")
        rows.append(f'<section class="work" id="{html.escape(key)}"><h2><span class="key">[{html.escape(key)}]</span> '
                    f'{reference(works[key])}</h2><p class="count">{n_linked} result{"s" * (n_linked != 1)} with a declaration'
                    f'{coverage}</p><ul class="results">{"".join(items_html)}</ul></section>')

    # coverage by roadmap: the results each roadmap cites, and those that have a declaration
    by_area: dict[str, set] = defaultdict(set)
    for a, _ in records:
        result = tuple(a["id"].split(":", 1))
        if result in goals:
            for ref in a.get("extensions", {}).get(ROADMAPS, {}).get("items", []):
                by_area[ref.split(" ")[0]].add(result)
    table = "".join(f'<tr><td>{html.escape(area)}</td><td>{meter(len(rs & linked), len(rs))}</td></tr>'
                    for area, rs in sorted(by_area.items()))
    n_decls = len({decl for _, decl in records if decl})
    covered = len(goals & linked)
    template = (Path(__file__).with_name("page.html")).read_text(encoding="utf-8")
    summary = (f"{len(linked)} results of {len({k for k, _ in linked})} works are cited by {n_decls} declarations. "
               + (f"The roadmaps cite {len(goals)} results, of which {covered} ({round(100 * covered / len(goals))}%) "
                  f"have a declaration" if goals else "No roadmap was read"))
    return (template.replace("{{works}}", "\n".join(rows)).replace("{{summary}}", summary)
            .replace("{{roadmaps}}", table)
            .replace("{{roadmaps-commit}}", html.escape(roadmap_commit))
            .replace("{{roadmaps-commit12}}", html.escape(roadmap_commit[:12]))
            .replace("{{annotations}}", str(len(records)))
            .replace("{{commit}}", html.escape(commit)).replace("{{commit12}}", html.escape(commit[:12]))
            .replace("{{repo}}", html.escape(repo)).replace("{{profile}}", html.escape(PROFILE))
            .replace("{{extension}}", ROADMAPS))


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--dataset", type=Path, required=True, help="the S2 dataset extracted by trust-extract")
    p.add_argument("--bibliography", type=Path, required=True, help="the works, by citation key")
    p.add_argument("--out", type=Path, required=True, help="the folder to write to")
    p.add_argument("--roadmaps", type=Path, help="a checkout of LMLRoadmaps")
    p.add_argument("--roadmaps-commit", default="main", help="the commit of that checkout, for links")
    args = p.parse_args()
    bibliography = json.loads(args.bibliography.read_text(encoding="utf-8"))
    stats = build(args.dataset, bibliography, args.out, args.roadmaps, args.roadmaps_commit)
    print(f"{stats['annotations']} annotations: {stats['linked']} links from {stats['declarations']} declarations "
          f"to {stats['results']} results of {stats['works']} works; the roadmaps cite {stats['goals']} results, "
          f"of which {stats['covered']} have a declaration")
    if stats["unknown"]:
        print("citation keys in neither bibliography.json nor a References section, left out: "
              + ", ".join(f"{k} ({n})" for k, n in stats["unknown"].most_common()), file=sys.stderr)
    if stats["unparsed"]:
        print(f"{sum(stats['unparsed'].values())} citations name no numbered result, e.g. "
              + "; ".join(k for k, _ in stats["unparsed"].most_common(5)), file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
