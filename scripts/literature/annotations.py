#!/usr/bin/env python3
"""Literature Links annotations for LMLExplore, and the page that lists them.

Reads the dataset (S2) that the referee site workflow extracts, and a checkout of LMLRoadmaps. It
finds the citations of numbered results of the literature, such as `[GK16, Theorem 14]`,
`[LS, Lemmas 12.2–12.4]`, `[P, proof of Theorem 6.2.2]` or `[GK16, Theorem 1; LS, Theorem 33.5]`:

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

With `--papers FILE`, the `papers.json` that `scripts/papers/papers.py` writes, the page can also show
the literature links of the papers built on LMLExplore, behind a toggle: the `literature/annotations.jsonl`
that each paper publishes on its website, in the same format. A paper's work is the page's work with
the same arXiv ID or URI, and its results are matched by label. `annotations.jsonl` keeps LMLExplore's
links only.

With `--summary FILE`, it appends to FILE (the run summary, in the workflow) what `bibliography.json`
lacks: the works the page shows from their reference text, and the possible duplicates, a work cited
under two keys. `lookup.py` proposes the entries and aliases to add.

usage: annotations.py --dataset DIR --bibliography FILE --out DIR [--roadmaps DIR]
       [--roadmaps-commit SHA] [--papers FILE] [--summary FILE]
"""
from __future__ import annotations

import argparse
import html
import json
import re
import sys
import unicodedata
import urllib.parse
import urllib.request
from collections import Counter, defaultdict
from dataclasses import dataclass
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

#: A bracket citing works, not right after a letter or a digit: `[GK16]`, `[GK16, Theorem 14]`,
#: `[GK16, Theorem 1; LS, Theorem 33.5]`.
CITATION = re.compile(r"(?<!\w)\[([A-Z][A-Za-z]*\d*[a-z]?(?:\s*[,;][^\[\]]*)?)\]")
#: A part of a bracket, between semicolons, that names a work: its key, then a locator if any.
CITED = re.compile(r"\s*([A-Z][A-Za-z]*\d*[a-z]?)\s*(?:,\s*(.*))?", re.S)
#: An inline code span: the brackets in it are Lean notation (`Var[X; μ]`), not citations.
CODE = re.compile(r"`[^`]*`")
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


def citations_of(text: str) -> list[tuple[int, str, str]]:
    """The citations in a text, as (position of the bracket, key, locator): one for each work that a
    bracket cites with a locator. `[GK16, Theorem 1; LS, Theorem 33.5]` cites two works, and
    `[KCG16; LS, Theorem 33.5]` cites a result of `LS` (and the whole of `KCG16`, which gives no
    link). A part without a key continues the work before it: `[Ora, Lemma 6.32; Lemma 7.15]`.
    The brackets in code spans, and right after a letter or a digit (`\\mathbb E[X]`), are notation."""
    masked = CODE.sub(lambda m: " " * len(m.group()), text)
    out = []
    for m in CITATION.finditer(masked):
        key = None
        for part in m.group(1).split(";"):
            c = CITED.fullmatch(part)
            if c and kind_of(c.group(1)) is None:  # `Lemma 7.15` continues the work before it
                key, locator = c.group(1), c.group(2) or ""
            else:
                locator = part
            if key is not None and locator.strip():
                out.append((m.start(), key, " ".join(locator.split())))
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


def normalize(text: str) -> str:
    """Text for comparing titles: without markup, accents, case and punctuation."""
    text = unicodedata.normalize("NFKD", re.sub(r"<[^>]+>|[*_]", "", text))
    return re.sub(r"[^a-z0-9]+", "", "".join(c for c in text if not unicodedata.combining(c)).lower())


def same_work(text: str, entry: dict) -> bool:
    """Whether a reference text names the work of a bibliography entry: it names the entry's first
    author, and its title in italics is the entry's, or the whole text contains the entry's title
    (when that title is long enough not to occur by chance)."""
    c = entry["citation"]
    title = normalize(c["title"])
    family = normalize(c["author"][0]["family"]) if c.get("author") else ""
    if not title or not family or family not in normalize(text):
        return False
    italic = re.search(r"\*([^*]+)\*", text)
    if italic and normalize(italic.group(1)) == title:
        return True
    return len(title) >= 25 and title in normalize(text)


def bibliography_gaps(bibliography: dict, fallback: dict[str, str]) -> list[tuple[str, str, str]]:
    """The possible duplicates, as (key, key of the same work, why): a work the page shows from its
    reference text whose text names a work of the bibliography, and two entries with one title and
    one first author."""
    entries = {k: e for k, e in bibliography.items() if "same" not in e}
    out = [(key, other, "its reference text names this work")
           for key, text in sorted(fallback.items()) for other, e in sorted(entries.items()) if same_work(text, e)]
    seen: dict[tuple[str, str], str] = {}
    for key, e in sorted(entries.items()):
        c = e["citation"]
        sig = (normalize(c["title"]), normalize(c["author"][0]["family"]) if c.get("author") else "")
        if sig in seen:
            out.append((key, seen[sig], "same title and first author"))
        seen.setdefault(sig, key)
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
        for start, key, locator in citations_of(body):
            heading, item = None, None
            for pos, what, value in marks:
                if pos > start:
                    break
                if what == "h":
                    heading, item = value, None
                else:
                    item = value
            layer = re.match(r"Layer (\d+)\b", heading or "")
            ref = f"{area} {layer.group(1)}.{item}" if layer and item else area
            links.setdefault(ref, f"https://github.com/{ROADMAPS_REPO}/blob/{commit}/{rel}"
                             + (f"#{slug(heading)}" if layer else ""))
            citations.append((key, locator, ref))
    return citations, texts, links


# --- the papers ----------------------------------------------------------------------------------
#
# The papers' annotations are written in other people's repositories: everything read from them is
# checked and escaped, and the links of the page are built here, from the repository and website
# that `papers.json` names (as GitHub returned them) and from identifiers checked against a pattern,
# never taken from the files.

#: The relations of the Literature Links format, read "result *relation* declaration": as the page
#: shows them, and what they mean.
RELATIONS = {"exactMatch": ("exact", "the declaration states the result"),
             "closeMatch": ("close", "the declaration states the result, with a difference a reader should know"),
             "broadMatch": ("more general", "the declaration is more general than the result"),
             "narrowMatch": ("less general", "the result is more general than the declaration"),
             "hasPart": ("one part", "the declaration is one claim of the result")}
REPOSITORY = re.compile(r"^[A-Za-z0-9-]+/[A-Za-z0-9_.-]+$")
WEBSITE = re.compile(r"^https://[A-Za-z0-9-]+\.github\.io/[A-Za-z0-9_.-]+/$")
COMMIT = re.compile(r"^[0-9a-f]{40}$")
KEY = re.compile(r"^[A-Z][A-Za-z]*\d*[a-z]?$")
ARXIV = re.compile(r"\b(\d{4}\.\d{4,5})(?:v\d+)?\b")
DOI = re.compile(r"^https://doi\.org/10\.\d{4,9}/[-._;()/:A-Za-z0-9]+$")
#: What `build` writes as the part of a result: `(a)`, or several, possibly with `proof`.
PART = re.compile(r"^(?:\([a-z0-9]{1,4}\)|proof)(?:, (?:\([a-z0-9]{1,4}\)|proof))*$")
#: The largest annotations file read from a paper.
MAX_BYTES = 10 * 2**20


@dataclass(frozen=True)
class PaperLink:
    """A declaration of a paper's repository that cites a result."""
    repo: str
    site: str
    decl: str
    module: str
    commit: str
    #: `proof`, or the part of the result that it cites, such as `(a)`
    tag: str | None
    relation: str | None


@dataclass
class Papers:
    """The literature links of the papers, matched with the works of the page."""
    #: (key, label) → the declarations of the papers that cite the result
    links: dict[tuple[str, str], list[PaperLink]]
    #: the works that only the papers cite, by key
    works: dict[str, dict]
    #: the papers read
    count: int
    notes: list[str]


def fetch_papers(path: Path, notes: list[str]) -> list[tuple[str, str, list]]:
    """The papers of `papers.json` that publish literature links, as (repository, website,
    annotations): the `literature/annotations.jsonl` on each paper's website."""
    out = []
    for p in json.loads(path.read_text(encoding="utf-8")):
        repo, site = p.get("repo"), p.get("site")
        if not (isinstance(repo, str) and REPOSITORY.match(repo)):
            continue
        if not (isinstance(site, str) and WEBSITE.match(site)):
            notes.append(f"{repo}: no website, so no literature links")
            continue
        url = site + "literature/annotations.jsonl"
        try:
            request = urllib.request.Request(url, headers={"User-Agent": "lmlexplore-literature-page/1"})
            with urllib.request.urlopen(request, timeout=30) as r:
                data = r.read(MAX_BYTES + 1)
            if len(data) > MAX_BYTES:
                raise ValueError(f"larger than {MAX_BYTES} bytes")
            records = [json.loads(line) for line in data.decode("utf-8").splitlines() if line.strip()]
        except (OSError, ValueError) as e:  # network errors, and files that are not JSON Lines
            notes.append(f"{repo}: no literature links read from {url} ({e})")
            continue
        out.append((repo, site, records))
    return out


def identities(w: dict) -> list[str]:
    """What identifies a work across bibliographies: its arXiv ID, then its URI."""
    out = []
    uri = w.get("uri") if isinstance(w.get("uri"), str) else ""
    arxiv = (w.get("identifiers") or {}).get("arxiv") if isinstance(w.get("identifiers"), dict) else None
    for text in (arxiv if isinstance(arxiv, str) else "", uri if "arxiv.org/" in uri else ""):
        m = ARXIV.search(text)
        if m:
            out.append("arxiv:" + m.group(1))
    if uri.startswith(("https://", "http://")):
        out.append("uri:" + uri.split("://", 1)[1].rstrip("/").lower())
    return out


def paper_work(end: dict, key: str) -> dict:
    """A work that only the papers cite, from the subject of their annotations: the text of its
    citation, and a link built from its arXiv ID or DOI."""
    c = end.get("citation") if isinstance(end.get("citation"), dict) else {}

    def text(v) -> str:
        return " ".join(v.split()) if isinstance(v, str) else ""

    citation = {"id": key, "type": text(c.get("type")) or "document", "title": text(c.get("title")) or key}
    names = [{"given": text(a.get("given")), "family": text(a.get("family"))}
             for a in c.get("author") or [] if isinstance(a, dict) and text(a.get("family"))]
    if names:
        citation["author"] = names
    else:  # shown as its title alone
        citation["type"] = "document"
    for field in ("container-title", "publisher", "DOI"):
        if text(c.get(field)):
            citation[field] = text(c.get(field))
    dates = c.get("issued", {}).get("date-parts") if isinstance(c.get("issued"), dict) else None
    year = dates[0][0] if isinstance(dates, list) and dates and isinstance(dates[0], list) and dates[0] else None
    if isinstance(year, int):
        citation["issued"] = {"date-parts": [[year]]}
    w: dict = {"uri": f"urn:lmlexplore:paper:{key}", "citation": citation}
    arxiv = next((i.removeprefix("arxiv:") for i in identities(end) if i.startswith("arxiv:")), None)
    if arxiv:
        w["uri"], w["identifiers"] = f"https://arxiv.org/abs/{arxiv}", {"arxiv": arxiv}
        if isinstance(end.get("version"), str) and re.fullmatch(r"v\d+", end["version"]):
            w["version"] = end["version"]
    elif isinstance(end.get("uri"), str) and DOI.match(end["uri"]):
        w["uri"] = end["uri"]
    return w


def paper_link(a, repo: str, site: str) -> tuple[dict, str, PaperLink] | None:
    """An annotation of a paper as (its subject, the result's label, the declaration), or None when
    it is not an annotation as this script writes them, linking a declaration of the paper."""
    if not isinstance(a, dict) or not isinstance(a.get("subject"), list) or not isinstance(a.get("object"), list):
        return None
    if len(a["subject"]) != 1 or len(a["object"]) != 1 or not all(isinstance(e, dict) for e in a["subject"] + a["object"]):
        return None
    end, obj = a["subject"][0], a["object"][0]
    loc = end.get("location") if isinstance(end.get("location"), dict) else {}
    where = obj.get("location") if isinstance(obj.get("location"), dict) else {}
    if loc.get("profile") != PROFILE or obj.get("type") != "lean" or not isinstance(loc.get("label"), str):
        return None
    if not isinstance(obj.get("uri"), str) or obj["uri"].lower() != f"https://github.com/{repo}".lower():
        return None  # a paper links its own declarations only
    parsed = items(loc["label"])
    if len(parsed) != 1 or label(parsed[0][0], parsed[0][1]) != loc["label"]:
        return None
    decl, module, commit = where.get("declaration"), where.get("module"), obj.get("version")
    if not (isinstance(decl, str) and decl and isinstance(module, str) and module
            and isinstance(commit, str) and COMMIT.match(commit)):
        return None
    part = loc.get("part")
    tag = "proof" if a.get("kind") == "proof" else part if isinstance(part, str) and PART.match(part) else None
    relation = a.get("relation") if a.get("relation") in RELATIONS else None
    return end, loc["label"], PaperLink(repo, site, decl, module, commit, tag, relation)


def match_papers(fetched: list[tuple[str, str, list]], page: dict[str, dict], bibliography: dict,
                 ported: set[str], notes: list[str]) -> Papers:
    """The papers' links, matched with the works of the page (`page`, by key), then with those of
    `bibliography.json`: a work is the one with the same arXiv ID or URI. Another work keeps the
    paper's key, unless the page has that key already. A declaration named as one of LMLExplore's
    (`ported`) is a paper's copy of it, from before it was ported: left out."""
    index: dict[str, str] = {}
    known = {**page, **{k: e for k, e in bibliography.items() if "same" not in e and k not in page}}
    for key, w in known.items():
        for i in identities(w):
            index.setdefault(i, key)
    links: dict[tuple[str, str], set[PaperLink]] = defaultdict(set)
    works: dict[str, dict] = {}
    versions: set[tuple[str, str, str]] = set()
    for repo, site, records in fetched:
        skipped, copies = 0, 0
        for a in records:
            parsed = paper_link(a, repo, site)
            if parsed is None:
                if not (isinstance(a, dict) and a.get("object") == []):  # a result no declaration cites
                    skipped += 1
                continue
            end, lab, link = parsed
            if link.decl in ported:
                copies += 1
                continue
            cited = end.get("citation", {}).get("id") if isinstance(end.get("citation"), dict) else None
            cited = cited if isinstance(cited, str) and KEY.match(cited) else "?"
            ids = identities(end) or [f"paper:{repo}:{cited}"]
            key = next((index[i] for i in ids if i in index), None)
            if key is None:  # a work the page does not have
                key = cited if cited not in known and cited not in works else f"{cited}-{repo.split('/')[1]}"
                works[key] = paper_work(end, key)
                for i in ids:
                    index.setdefault(i, key)
            elif key in known:
                if key not in page:
                    works[key] = known[key]
                ours = known[key].get("version")
                theirs = end.get("version") if isinstance(end.get("version"), str) else None
                if ours != theirs:
                    versions.add((key, repo, f"{ours or 'the published numbering'} here, "
                                             f"{theirs or 'the published numbering'} in the paper"))
            links[(key, lab)].add(link)
        if skipped:
            notes.append(f"{repo}: {skipped} annotations that are not links of its own declarations, left out")
        if copies:
            notes.append(f"{repo}: {copies} links of its copies of declarations that LMLExplore has now, left out")
    notes += [f"[{key}] in {repo}: {why}; the results are matched by label" for key, repo, why in sorted(versions)]
    return Papers({r: sorted(ls, key=lambda pl: (pl.repo, pl.decl)) for r, ls in links.items()},
                  works, len(fetched), notes)


# --- the annotations -----------------------------------------------------------------------------

def end_type(uri: str) -> str:
    if uri.lower().endswith(".pdf"):
        return "pdf"
    return "html" if uri.startswith(("https://", "http://")) else "generic"


def item_sort(ref: str) -> tuple:
    area, _, number = ref.partition(" ")
    return (area, [int(n) for n in number.split(".")] if number else [])


def build(dataset: Path, bibliography: dict, out: Path, roadmap_root: Path | None, roadmap_commit: str,
          papers_file: Path | None = None) -> dict:
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
        for _, key, locator in citations_of(text):
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
    goals = {r for r in cited if kinds[r] not in PLACES}
    notes: list[str] = []
    papers = (match_papers(fetch_papers(papers_file, notes), {k: work(k) for k in keys}, bibliography,
                           {readable(d) for d in decls}, notes) if papers_file else None)
    page = render(records, sources, repo, commit, {k: work(k) for k in keys}, item_links, roadmap_commit, goals,
                  papers)
    (out / "index.html").write_text(page, encoding="utf-8")
    fallback = {k: work(k)["citation"]["title"] for k in keys if k not in bibliography}
    counts = Counter(a["id"].split(":")[0] for a in annotations)
    return {"annotations": len(annotations), "linked": sum(a["object"] != [] for a in annotations),
            "fallback": {k: (text, counts[k]) for k, text in fallback.items()},
            "duplicates": bibliography_gaps(bibliography, fallback),
            "declarations": len({d for _, d in records if d}), "results": len(links), "works": len(keys),
            "goals": len(goals), "covered": len(goals & set(links)), "unknown": unknown, "unparsed": unparsed,
            "papers": papers and {
                "read": papers.count, "notes": papers.notes,
                "papers": len({pl.repo for pls in papers.links.values() for pl in pls}),
                "links": sum(len(pls) for pls in papers.links.values()),
                "declarations": len({(pl.repo, pl.decl) for pls in papers.links.values() for pl in pls}),
                "works": len(papers.works), "covered": len(goals & (set(links) | set(papers.links)))}}


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


def bar(covered: int, total: int) -> str:
    """A bar showing the share `covered / total`."""
    pct = round(100 * covered / total) if total else 0
    return f'<span class="meter" role="img" aria-label="{covered} of {total}"><span style="width:{pct}%"></span></span>'


def meter(covered: int, total: int) -> str:
    return f"{bar(covered, total)} {covered} of {total}"


def dual(here: str, every: str) -> str:
    """What the page shows without the papers' links, then with them (the toggle shows one)."""
    return here if here == every else f'<span class="v-lml">{here}</span><span class="v-all">{every}</span>'


def paper_item(pl: PaperLink) -> str:
    """A declaration of a paper citing a result: its page on the paper's referee site, the relation
    that the paper gives, the paper, and the source."""
    tags = f" <span class=tag>{html.escape(pl.tag)}</span>" if pl.tag else ""
    if pl.relation:
        shown, meaning = RELATIONS[pl.relation]
        tags += f' <span class="tag" title="{pl.relation}: {html.escape(meaning)}">{html.escape(shown)}</span>'
    path = "/".join(urllib.parse.quote(s, safe="") for s in pl.module.split(".")) + ".lean"
    return (f'<li class="paper"><a href="{pl.site}referee/#/d/{urllib.parse.quote(pl.decl, safe="")}">'
            f'<code>{html.escape(pl.decl)}</code></a>{tags}'
            f' <a class="chip" href="../papers/#{urllib.parse.quote(pl.repo)}">{html.escape(pl.repo.split("/")[1])}</a>'
            f' <a class="src" href="https://github.com/{pl.repo}/blob/{pl.commit}/{path}">source</a></li>')


def render(records: list[tuple[dict, str | None]], sources: dict, repo: str, commit: str, works: dict,
           item_links: dict, roadmap_commit: str, goals: set, papers: Papers | None = None) -> str:
    """The page: the works by number of results, each result with the declarations and the roadmap
    items citing it, and the coverage of the results that the roadmaps cite. With `papers`, also the
    declarations of the papers citing them, and the counts with them, which the toggle shows."""
    by_work: dict[str, dict[str, list[tuple[dict, str | None]]]] = defaultdict(lambda: defaultdict(list))
    for a, decl in records:
        key, lab = a["id"].split(":", 1)
        by_work[key][lab].append((a, decl))
    ours = set(by_work)
    plinks = papers.links if papers else {}
    works = {**works, **(papers.works if papers else {})}
    for key, lab in plinks:
        by_work[key].setdefault(lab, [])  # the results that only the papers cite
    linked = {(k, lab) for k, results in by_work.items() for lab, rs in results.items() if any(d for _, d in rs)}
    every = linked | set(plinks)

    def chips(refs: list[str]) -> str:
        return "".join(f' <a class="chip" href="{html.escape(item_links.get(r, ""))}">{html.escape(r)}</a>' for r in refs)

    def results_here(key: str) -> int:
        return sum(bool(rs) for rs in by_work[key].values())

    rows = []
    # LMLExplore's works in the order of the page without the papers, then the papers' own
    for key in sorted(by_work, key=lambda k: (k not in ours, -(results_here(k) if k in ours else len(by_work[k])), k)):
        results = by_work[key]
        items_html = []
        for lab in sorted(results, key=sort_key):
            rs = results[lab]
            pls = plinks.get((key, lab), [])
            refs = rs[0][0].get("extensions", {}).get(ROADMAPS, {}).get("items", []) if rs else []
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
                decls.append(f'<li class="none{" p" if pls else ""}">not linked yet</li>')
            decls += [paper_item(pl) for pl in pls]
            names = " ".join(a["object"][0]["location"]["declaration"] for a, d in rs if d)
            cls = ("result" + ("" if (key, lab) in linked else " unlinked") + (" p-linked" if pls else "")
                   + ("" if rs else " paper"))
            found = " ".join(f"{pl.decl} {pl.repo.split('/')[1]}" for pl in pls)
            data = f' data-papers="{html.escape(found.lower())}"' if pls else ""
            roadmap = f'<div class="items">cited by{chips(refs)}</div>' if refs else ""
            items_html.append(f'<li class="{cls}" data-text="{html.escape((key + " " + lab + " " + names + " " + " ".join(refs)).lower())}"{data}>'
                              f'<span class="label">{html.escape(lab)}</span><div><ul>{"".join(decls)}</ul>{roadmap}</div></li>')
        work_goals = {lab for (k, lab) in goals if k == key}

        def covered(s: set) -> int:
            return len(work_goals & {lab for (k, lab) in s if k == key})

        n_linked = sum((key, lab) in linked for lab in results)
        n_every = sum((key, lab) in every for lab in results)
        count = dual(f'{n_linked} result{"s" * (n_linked != 1)}', f'{n_every} result{"s" * (n_every != 1)}')
        coverage = (f' · the roadmaps cite {len(work_goals)}: '
                    f'{dual(meter(covered(linked), len(work_goals)), meter(covered(every), len(work_goals)))} have a declaration'
                    if work_goals else "")
        rows.append(f'<section class="work{"" if key in ours else " paper"}" id="{html.escape(key)}"><h3 class="work-title">'
                    f'<span class="key">[{html.escape(key)}]</span> '
                    f'{reference(works[key])}</h3><div class="count">{count} with a declaration'
                    f'{coverage}</div><ul class="results">{"".join(items_html)}</ul></section>')

    # coverage by roadmap: the results each roadmap cites, and those that have a declaration
    by_area: dict[str, set] = defaultdict(set)
    for a, _ in records:
        result = tuple(a["id"].split(":", 1))
        if result in goals:
            for ref in a.get("extensions", {}).get(ROADMAPS, {}).get("items", []):
                by_area[ref.split(" ")[0]].add(result)

    def row(name: str, rs: set) -> str:
        return (f'<tr><th scope="row">{html.escape(name)}</th><td class="num">{len(rs):,}</td>'
                f'<td class="num">{dual(f"{len(rs & linked):,}", f"{len(rs & every):,}")}</td>'
                f'<td>{dual(bar(len(rs & linked), len(rs)), bar(len(rs & every), len(rs)))}</td></tr>')

    def share(s: set) -> str:
        return f"{round(100 * len(goals & s) / len(goals))}%" if goals else "–"

    n_decls = len({decl for _, decl in records if decl})
    n_paper_decls = len({(pl.repo, pl.decl) for pls in plinks.values() for pl in pls})
    toggle, note, data = "", "", ""
    if plinks:
        n_papers = len({pl.repo for pls in plinks.values() for pl in pls})
        toggle = '<label><input type="checkbox" id="papers"> include the papers</label>'
        note = ('<p>The <a href="../papers/">papers formalized on top of LMLExplore</a> link their declarations to '
                "the literature in the same way. With <em>include the papers</em>, the page shows their links too, "
                "each with its paper, and for a main result of a paper, how the declaration relates to the result "
                "according to the paper: <em>exact</em>, <em>close</em> (with a difference a reader should know), "
                "<em>more general</em>, <em>less general</em>, or <em>one part</em> of it. The counts and the "
                f"coverage of the roadmaps then include them. They are read from the websites of the {n_papers} "
                f"papers that publish links, when the page is built.</p>")
        data = ("<p>It has LMLExplore's links only: each paper publishes its own on its website, in the same "
                "format, as <code>literature/annotations.jsonl</code>.</p>")
    template = (Path(__file__).with_name("page.html")).read_text(encoding="utf-8")
    return (template.replace("{{works}}", "\n".join(rows))
            .replace("{{stat-results}}", dual(f"{len(linked):,}", f"{len(every):,}"))
            .replace("{{stat-works}}", dual(f"{len({k for k, _ in linked}):,}", f"{len({k for k, _ in every}):,}"))
            .replace("{{stat-declarations}}", dual(f"{n_decls:,}", f"{n_decls + n_paper_decls:,}"))
            .replace("{{stat-coverage}}", dual(share(linked), share(every)))
            .replace("{{goals}}", f"{len(goals):,}")
            .replace("{{roadmaps}}", "".join(row(area, rs) for area, rs in sorted(by_area.items())))
            .replace("{{roadmaps-total}}", row("All roadmaps", goals))
            .replace("{{papers-toggle}}", toggle).replace("{{papers-note}}", note).replace("{{papers-data}}", data)
            .replace("{{roadmaps-commit}}", html.escape(roadmap_commit))
            .replace("{{roadmaps-commit12}}", html.escape(roadmap_commit[:12]))
            .replace("{{annotations}}", str(len(records)))
            .replace("{{commit}}", html.escape(commit)).replace("{{commit12}}", html.escape(commit[:12]))
            .replace("{{repo}}", html.escape(repo)).replace("{{profile}}", html.escape(PROFILE))
            .replace("{{extension}}", ROADMAPS))


def summary(stats: dict) -> str:
    """The run summary: the counts, and what `bibliography.json` lacks."""
    lines = ["### Literature page", "",
             f"{stats['annotations']} annotations: {stats['linked']} links from {stats['declarations']} declarations "
             f"to {stats['results']} results of {stats['works']} works. The roadmaps cite {stats['goals']} results, "
             f"of which {stats['covered']} have a declaration.", ""]
    if stats["fallback"]:
        lines += [f"**{len(stats['fallback'])} works shown from their reference text.** Give them an entry in "
                  "`scripts/literature/bibliography.json`: `python3 scripts/literature/lookup.py propose` "
                  "proposes them.", ""]
        lines += [f"- `{k}` ({n} result{'s' * (n != 1)}): {text}"
                  for k, (text, n) in sorted(stats["fallback"].items(), key=lambda kv: (-kv[1][1], kv[0]))]
        lines.append("")
    if stats["duplicates"]:
        lines += ["**Possible duplicates**: one work under two keys. If they are the same work, make the first "
                  'key an alias of the second, `"KEY": {"same": "OTHER"}`.', ""]
        lines += [f"- `{a}` and `{b}`: {why}" for a, b, why in stats["duplicates"]]
        lines.append("")
    if not stats["fallback"] and not stats["duplicates"]:
        lines += ["Every work on the page has a bibliography entry, under one key.", ""]
    if stats["papers"] is not None:
        p = stats["papers"]
        lines += [f"With the papers: {p['links']} links from {p['declarations']} declarations of {p['papers']} papers "
                  f"(of the {p['read']} read), to {p['works']} more works; with them, {p['covered']} of the roadmaps' "
                  "results have a declaration.", ""]
        lines += [f"- {n}" for n in p["notes"]] + ([""] if p["notes"] else [])
    return "\n".join(lines) + "\n"


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--dataset", type=Path, required=True, help="the S2 dataset extracted by trust-extract")
    p.add_argument("--bibliography", type=Path, required=True, help="the works, by citation key")
    p.add_argument("--out", type=Path, required=True, help="the folder to write to")
    p.add_argument("--roadmaps", type=Path, help="a checkout of LMLRoadmaps")
    p.add_argument("--roadmaps-commit", default="main", help="the commit of that checkout, for links")
    p.add_argument("--papers", type=Path, help="the papers.json of scripts/papers/papers.py, for the papers' links")
    p.add_argument("--summary", type=Path, help="a Markdown file to append the report to (the run summary)")
    args = p.parse_args()
    bibliography = json.loads(args.bibliography.read_text(encoding="utf-8"))
    stats = build(args.dataset, bibliography, args.out, args.roadmaps, args.roadmaps_commit, args.papers)
    print(f"{stats['annotations']} annotations: {stats['linked']} links from {stats['declarations']} declarations "
          f"to {stats['results']} results of {stats['works']} works; the roadmaps cite {stats['goals']} results, "
          f"of which {stats['covered']} have a declaration")
    if stats["unknown"]:
        print("citation keys in neither bibliography.json nor a References section, left out: "
              + ", ".join(f"{k} ({n})" for k, n in stats["unknown"].most_common()), file=sys.stderr)
    if stats["unparsed"]:
        print(f"{sum(stats['unparsed'].values())} citations name no numbered result, e.g. "
              + "; ".join(k for k, _ in stats["unparsed"].most_common(5)), file=sys.stderr)
    if stats["papers"] is not None:
        p = stats["papers"]
        print(f"with the papers: {p['links']} links from {p['declarations']} declarations of {p['papers']} papers"
              + "".join(f"\n  {n}" for n in p["notes"]))
    if args.summary:
        with args.summary.open("a", encoding="utf-8") as f:
            f.write(summary(stats))
        if stats["fallback"] or stats["duplicates"]:
            print(f"::notice::bibliography.json lacks {len(stats['fallback'])} works and has "
                  f"{len(stats['duplicates'])} possible duplicates: see the run summary")
    return 0


if __name__ == "__main__":
    sys.exit(main())
