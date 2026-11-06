#!/usr/bin/env python3
"""Propose the bibliography entries that the literature page lacks, and add them once reviewed.

    lookup.py [--bibliography FILE] propose [--annotations FILE_OR_URL] [--out proposals.json]
    lookup.py [--bibliography FILE] merge proposals.json

`propose` reads the annotations the page publishes (by default those of the live site), finds the works
it shows from their reference text, and proposes for each:

* an alias `{"same": KEY}` when its text names a work of `bibliography.json`
  (`annotations.same_work`), so that one work keeps one key;
* otherwise an entry found in Crossref and arXiv. A candidate counts only when its title, without
  markup, accents, case and punctuation, occurs in the reference text, and the text names its first
  author. A DOI is proposed only for the version that the text cites: a journal or a book within a
  year of the text's year, or, for a conference citation (NeurIPS, ICML, COLT, ...), proceedings of
  that conference's year; otherwise the arXiv version, whose numbering the citations may follow.

It writes the proposals as JSON and prints a table to review. Check each one: the work, the version
(the edition of a book, the conference or the journal version of a paper), and the authors. Edit or
delete the proposals that are wrong, add by hand those it could not find, then `merge` adds them to
`bibliography.json` (without replacing an entry) and checks the result.

The lookups send the reference texts to the Crossref and arXiv APIs, with pauses between requests.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from annotations import normalize, same_work  # noqa: E402

HERE = Path(__file__).resolve().parent
BIBLIOGRAPHY = HERE / "bibliography.json"
PUBLISHED = "https://leanmachinelearning.org/LMLExplore/literature/annotations.jsonl"
HEADERS = {"User-Agent": "lmlexplore-literature-lookup/1"}
CONFERENCES = {"NeurIPS": "Advances in Neural Information Processing Systems (NeurIPS)",
               "ICML": "Proceedings of the International Conference on Machine Learning (ICML)",
               "COLT": "Proceedings of the Conference on Learning Theory (COLT)",
               "ALT": "Proceedings of the International Conference on Algorithmic Learning Theory (ALT)",
               "AISTATS": "Proceedings of the International Conference on Artificial Intelligence and Statistics (AISTATS)",
               "ECML PKDD": "Machine Learning and Knowledge Discovery in Databases (ECML PKDD)",
               "ICLR": "International Conference on Learning Representations (ICLR)"}
TYPES = {"journal-article": "article-journal", "book": "book", "monograph": "book", "edited-book": "book",
         "reference-book": "book", "book-chapter": "chapter", "proceedings-article": "paper-conference"}
ARXIV_ID = re.compile(r"arXiv[: ]\s*(\d{4}\.\d{4,5})")
INITIALS = re.compile(r"^((?:[A-Z][a-z]?\.(?:-[A-Z][a-z]?\.)?\s*)+)(\S.*)$")


def fetch(url: str, pause: float) -> str:
    time.sleep(pause)
    with urllib.request.urlopen(urllib.request.Request(url, headers=HEADERS), timeout=60) as r:
        return r.read().decode()


# --- the reference text --------------------------------------------------------------------------

def authors_of(text: str) -> list[dict]:
    """The authors a reference text begins with, `J.-Y. Audibert, S. Bubeck and R. Munos`, as CSL
    names with the initials as given names."""
    out = []
    for segment in re.sub(r"[*_]", "", text).split(", "):
        names = segment.split(" and ")
        parsed = [INITIALS.match(n.strip()) for n in names]
        if not all(parsed):
            break
        out += [{"family": m.group(2).strip(), "given": m.group(1).strip()} for m in parsed]
        if len(names) > 1:
            break
    return out


def year_of(text: str) -> int | None:
    years = re.findall(r"\b(1[89]\d\d|20\d\d)\b", ARXIV_ID.sub("", text))
    return int(years[-1]) if years else None


def conference_of(text: str) -> tuple[str, int] | None:
    m = re.search(r"\b(" + "|".join(CONFERENCES) + r")\s+(\d{4})\b", text)
    return (m.group(1), int(m.group(2))) if m else None


def matches(title: str, family: str, text: str) -> bool:
    t, f = normalize(title), normalize(family)
    return bool(t) and bool(f) and t in normalize(text) and f in normalize(text)


# --- the sources ---------------------------------------------------------------------------------

def arxiv(query: str) -> list[dict]:
    ns = {"a": "http://www.w3.org/2005/Atom"}
    out = []
    for e in ET.fromstring(fetch("http://export.arxiv.org/api/query?" + query, 3)).findall("a:entry", ns):
        out.append({"id": re.sub(r"v\d+$", "", e.find("a:id", ns).text.rsplit("/abs/", 1)[-1]),
                    "title": " ".join(e.find("a:title", ns).text.split()),
                    "authors": [a.find("a:name", ns).text for a in e.findall("a:author", ns)]})
    return out


def find_arxiv(text: str) -> dict | None:
    """The arXiv preprint the text names by its ID, or else one whose title the text contains."""
    plain = re.sub(r"[*_]", "", text)
    m = ARXIV_ID.search(text)
    if m:
        found = arxiv(f"id_list={m.group(1)}")
        return found[0] if found else None
    words = [w for w in re.findall(r"[A-Za-z]{5,}", plain)][:7]
    query = "+AND+".join(f"all:{urllib.parse.quote(w)}" for w in words)
    for e in arxiv(f"search_query={query}&max_results=5"):
        if matches(e["title"], e["authors"][0].split()[-1], plain):
            return e
    return None


def find_crossref(text: str) -> dict | None:
    plain = re.sub(r"[*_]", "", text)
    data = json.loads(fetch("https://api.crossref.org/works?rows=5&query.bibliographic="
                            + urllib.parse.quote(plain[:300]), 1))
    for item in data["message"]["items"]:
        family = (item.get("author") or [{}])[0].get("family", "")
        if matches((item.get("title") or [""])[0], family, plain):
            return item
    return None


def clean(title: str) -> str:
    return " ".join(re.sub(r"<[^>]+>", "", title).replace("$\\varepsilon$", "ε").split())


def propose_entry(key: str, text: str) -> tuple[dict | None, str]:
    """An entry for a work from its reference text, and how it was found."""
    conference, year, authors = conference_of(text), year_of(text), authors_of(text)
    item, preprint = find_crossref(text), find_arxiv(text)
    citation: dict = {"id": key}
    use_doi = False
    if item:
        typ = TYPES.get(item.get("type"), "document")
        doi_year = (item.get("issued") or {}).get("date-parts", [[None]])[0][0]
        if conference:  # a conference citation: only proceedings of that year
            use_doi = typ in ("paper-conference", "chapter") and doi_year == conference[1]
        else:  # a journal or a book: the version within a year of the text's
            use_doi = year is None or doi_year is None or abs(doi_year - year) <= 1
    if use_doi:
        entry = {"uri": f"https://doi.org/{item['DOI']}"}
        citation.update({"type": TYPES.get(item.get("type"), "document"), "title": clean(item["title"][0])})
        if item.get("container-title") and citation["type"] != "book":
            citation["container-title"] = clean(item["container-title"][-1])
        if item.get("volume"):
            citation["volume"] = item["volume"]
        if citation["type"] in ("book", "chapter") and item.get("publisher"):
            citation["publisher"] = item["publisher"]
        citation["DOI"] = item["DOI"]
        named = [{"family": a["family"], "given": a.get("given", "")} for a in item.get("author", []) if "family" in a]
        authors = named or authors
        how = f"Crossref, DOI {item['DOI']}"
        if preprint:
            entry["identifiers"] = {"arxiv": preprint["id"]}
    elif preprint:
        entry = {"uri": f"https://arxiv.org/abs/{preprint['id']}", "identifiers": {"arxiv": preprint["id"]}}
        citation.update({"type": "article", "title": clean(preprint["title"])})
        how = f"arXiv {preprint['id']}" + (f" (Crossref has DOI {item['DOI']}, another version)" if item else "")
    else:
        return None, "not found: add it by hand"
    jmlr = re.search(r"JMLR\*? (\d+)", text)
    if jmlr:
        citation.update({"type": "article-journal", "container-title": "Journal of Machine Learning Research",
                         "volume": jmlr.group(1)})
    if conference and "container-title" not in citation:
        citation.update({"type": "paper-conference", "container-title": CONFERENCES[conference[0]]})
    citation["author"] = authors
    citation["issued"] = {"date-parts": [[conference[1] if conference else year or 0]]}
    order = ["id", "type", "title", "author", "container-title", "volume", "edition", "publisher", "DOI", "issued"]
    entry["citation"] = {k: citation[k] for k in order if k in citation}
    return entry, how


# --- the commands --------------------------------------------------------------------------------

def read_annotations(source: str) -> list[dict]:
    if source.startswith(("https://", "http://")):
        text = fetch(source, 0)
    else:
        text = Path(source).read_text(encoding="utf-8")
    return [json.loads(line) for line in text.splitlines() if line.strip()]


def fallback_works(annotations: list[dict]) -> dict[str, str]:
    """The works the page shows from their reference text, by key: their citation has no author."""
    out = {}
    for a in annotations:
        c = a["subject"][0]["citation"]
        if c.get("type") == "document" and "author" not in c:
            out[c["id"]] = c["title"]
    return out


def propose(args: argparse.Namespace) -> int:
    bibliography = json.loads(args.bibliography.read_text(encoding="utf-8"))
    works = fallback_works(read_annotations(args.annotations))
    if not works:
        print("every work on the page has a bibliography entry", file=sys.stderr)
        return 0
    proposals = {}
    for key, text in sorted(works.items()):
        same = [k for k, e in sorted(bibliography.items()) if "same" not in e and same_work(text, e)]
        if same:
            proposals[key] = {"same": same[0]}
            how = f"alias of {same[0]}"
        else:
            entry, how = propose_entry(key, text)
            if entry:
                proposals[key] = entry
        print(f"{key}: {how}\n    text:     {text}", file=sys.stderr)
        if key in proposals and "citation" in proposals[key]:
            c = proposals[key]["citation"]
            print(f"    proposed: {', '.join(a['family'] for a in c['author'])}, {c['title']}, "
                  f"{c.get('container-title') or c.get('publisher') or ''} {c['issued']['date-parts'][0][0]}, "
                  f"{proposals[key]['uri']}", file=sys.stderr)
    out = json.dumps(proposals, ensure_ascii=False, indent=1) + "\n"
    if args.out:
        args.out.write_text(out, encoding="utf-8")
    else:
        sys.stdout.write(out)
    print(f"{len(proposals)} proposals for {len(works)} works: review them, then `lookup.py merge`", file=sys.stderr)
    return 0


def check(bibliography: dict) -> list[str]:
    problems = []
    for key, e in bibliography.items():
        if "same" in e:
            target = bibliography.get(e["same"])
            if target is None or "same" in target:
                problems.append(f"{key}: an alias of {e['same']}, which is not an entry")
            continue
        c = e.get("citation", {})
        if not e.get("uri") or c.get("id") != key or not c.get("type") or not c.get("title"):
            problems.append(f"{key}: needs uri, and citation.id = {key}, citation.type and citation.title")
        if not c.get("author") or not all(a.get("family") for a in c["author"]):
            problems.append(f"{key}: needs authors, each with a family name")
    return problems


def merge(args: argparse.Namespace) -> int:
    bibliography = json.loads(args.bibliography.read_text(encoding="utf-8"))
    proposals = json.loads(args.proposals.read_text(encoding="utf-8"))
    existing = sorted(set(proposals) & set(bibliography))
    if existing:
        print(f"already in bibliography.json, left as they are: {', '.join(existing)}", file=sys.stderr)
    merged = {**bibliography, **{k: v for k, v in proposals.items() if k not in bibliography}}
    problems = check(merged)
    if problems:
        print("not merged:\n" + "\n".join(problems), file=sys.stderr)
        return 1
    args.bibliography.write_text(json.dumps(dict(sorted(merged.items())), ensure_ascii=False, indent=1) + "\n",
                                 encoding="utf-8")
    print(f"added {len(merged) - len(bibliography)} entries to {args.bibliography}", file=sys.stderr)
    return 0


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--bibliography", type=Path, default=BIBLIOGRAPHY, help="default: the one beside this script")
    sub = p.add_subparsers(dest="command", required=True)
    q = sub.add_parser("propose", help="propose entries for the works shown from their reference text")
    q.add_argument("--annotations", default=PUBLISHED, help="annotations.jsonl, a file or a URL (default: the live site's)")
    q.add_argument("--out", type=Path, help="where to write the proposals (default: standard output)")
    m = sub.add_parser("merge", help="add reviewed proposals to bibliography.json")
    m.add_argument("proposals", type=Path)
    args = p.parse_args()
    return propose(args) if args.command == "propose" else merge(args)


if __name__ == "__main__":
    sys.exit(main())
