#!/usr/bin/env python3
"""The papers built on LMLExplore, and what they bring to it: two pages of LMLExplore's site.

A paper project formalizes one research paper on top of LMLExplore, in a repository made from
https://github.com/LeanMachineLearning/lml-paper-template; a public one carries the GitHub topic
`lmlexplore-paper`. For each such repository, this script reads through the GitHub API:

* `PAPER_ROADMAP.md`: the paper's prerequisites, each tagged `exists` (LMLExplore has it),
  `target` (it advances a target of LMLRoadmaps), `refactor` (it changes code LMLExplore has),
  `staged` (no target covers it yet; the file proposes one) or `paper`, with its status, in the
  format that the paper-roadmap skill of https://github.com/LeanMachineLearning/lml-claude fixes;
* `formalization.yaml`: the paper, and the status of its main results;
* `lakefile.toml`: the name of its Lean library, the folder that the roadmap's files are in;

and the pull requests of LMLExplore whose description names the paper and one of its items, in
the lines `Paper: <owner>/<repo>` and `Item: <Id>`. It writes to the output folder:

* `index.html`: the papers, with the status of their main results and their pull requests;
* `material/index.html`: their prerequisites by tag: the targets by roadmap item, the refactors,
  the staged items with their proposed targets, and what they use from LMLExplore;
* `papers.json`: the data of both pages.

Everything read from a paper repository is shown as text: escaped, with only its `code` spans
rendered. Links are built here from names that GitHub returns, never taken from the files.

    papers.py --out DIR [--repo LeanMachineLearning/LMLExplore] [--summary FILE]

The GitHub token comes from GH_TOKEN or GITHUB_TOKEN. It only reads public data; without one, the
API's lower rate limit applies.
"""

import argparse
import html
import json
import os
import re
import sys
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter
from dataclasses import asdict, dataclass, field
from pathlib import Path

import yaml

API = "https://api.github.com"
TOPIC = "lmlexplore-paper"
ROADMAPS = "LeanMachineLearning/LMLRoadmaps"
FORMALIZE = "https://leanmachinelearning.org/formalize/"
TEMPLATE = "https://github.com/LeanMachineLearning/lml-paper-template"
#: A repository's `owner/name`, as GitHub allows them.
FULL_NAME = re.compile(r"^[A-Za-z0-9-]+/[A-Za-z0-9_.-]+$")
#: A target of LMLRoadmaps: the roadmap's directory, then the layer and item numbers.
TARGET = re.compile(r"^([A-Z][A-Za-z]+) (\d+(?:\.\d+)*)$")


# --- GitHub -------------------------------------------------------------------------------------

class GitHub:
    def __init__(self, token: str | None):
        self.token = token

    def get(self, path: str, params: dict | None = None, raw: bool = False):
        """The JSON (or with `raw`, the text) at an API path; None when it does not exist."""
        url = API + path + ("?" + urllib.parse.urlencode(params) if params else "")
        headers = {"Accept": "application/vnd.github.raw+json" if raw else "application/vnd.github+json",
                   "User-Agent": "LMLExplore-papers-page", "X-GitHub-Api-Version": "2022-11-28"}
        if self.token:
            headers["Authorization"] = f"Bearer {self.token}"
        try:
            with urllib.request.urlopen(urllib.request.Request(url, headers=headers), timeout=30) as r:
                data = r.read()
        except urllib.error.HTTPError as e:
            if e.code == 404:
                return None
            raise
        return data.decode("utf-8", "replace") if raw else json.loads(data)

    def search(self, kind: str, query: str) -> list[dict]:
        """All the results of a search (`repositories` or `issues`), up to GitHub's 1000."""
        out: list[dict] = []
        for page in range(1, 11):
            result = self.get(f"/search/{kind}", {"q": query, "per_page": 100, "page": page}) or {}
            items = result.get("items") or []
            out += items
            if len(items) < 100:
                break
        return out

    def file(self, repo: str, path: str) -> str | None:
        return self.get(f"/repos/{repo}/contents/{urllib.parse.quote(path)}", raw=True)


# --- Reading a paper repository -----------------------------------------------------------------

@dataclass
class Item:
    id: str
    text: str
    tag: str
    link: str
    status: str
    files: list[str]
    #: The pull requests of LMLExplore that name this item: number, title, state.
    prs: list[dict] = field(default_factory=list)


@dataclass
class Paper:
    repo: str
    url: str
    site: str | None
    pushed: str
    library: str
    title: str = ""
    authors: list[str] = field(default_factory=list)
    source: str = ""
    arxiv: str | None = None
    statements: dict[str, int] = field(default_factory=dict)
    sorry: int | None = None
    refreshed: str = ""
    pin: str = ""
    items: list[Item] = field(default_factory=list)
    #: The proposed targets of the staged items, by their `S<n>`: title and text.
    proposals: dict[str, dict] = field(default_factory=dict)
    prs: list[dict] = field(default_factory=list)


def sections(text: str, level: str) -> dict[str, list[str]]:
    """The lines under each heading of a level (`## ` or `### `), by heading."""
    out: dict[str, list[str]] = {}
    current = None
    for line in text.splitlines():
        if line.startswith(level):
            current = line[len(level):].strip()
            out[current] = []
        elif current is not None:
            if level == "### " and line.startswith("## "):
                current = None
            else:
                out[current].append(line)
    return out


def read_roadmap(paper: Paper, text: str) -> None:
    """The items, header line and proposed targets of PAPER_ROADMAP.md."""
    for line in text.splitlines():
        if line.startswith("# Paper roadmap:") and not paper.title:
            paper.title = line.split(":", 1)[1].strip()
        if line.startswith("Paper:"):
            for part in line.split("·"):
                key, _, value = part.strip().partition(" ")
                if key == "LMLExplore":
                    paper.pin = value.strip()
                elif key == "Refreshed":
                    paper.refreshed = value.strip()
            break
    parts = sections(text, "## ")
    for row in parts.get("Items", []):
        row = row.strip()
        if not row.startswith("|"):
            continue
        cells = [c.strip() for c in row.strip("|").split("|")]
        if len(cells) < 6 or cells[0] == "Id" or set("".join(cells)) <= set("-: "):
            continue
        if len(cells) > 6:  # a `|` inside the item's description
            cells = [cells[0], "|".join(cells[1:-4])] + cells[-4:]
        paper.items.append(Item(id=cells[0], text=cells[1], tag=cells[2].lower(), link=cells[3],
                                status=cells[4], files=re.findall(r"`([^`]+)`", cells[5])))
    proposed = "\n".join(parts.get("Proposed targets", []))
    for heading, lines in sections(proposed, "### ").items():
        key, _, title = heading.partition(".")
        paper.proposals[key.strip()] = {"title": title.strip(), "text": "\n".join(lines).strip()}


def read_formalization(paper: Paper, text: str) -> None:
    """The paper (its title, authors and identifier) and the status of its main results."""
    try:
        data = yaml.safe_load(text)
    except yaml.YAMLError:
        return
    if not isinstance(data, dict):
        return
    sources = [s for s in data.get("sources") or [] if isinstance(s, dict)]
    source = next((s for s in sources if s.get("relationship") == "formalizes"), sources[0] if sources else {})
    paper.title = str(source.get("title") or paper.title)
    paper.authors = [str(a) for a in source.get("authors") or []]
    paper.source = str(source.get("id") or "")
    m = re.search(r"arXiv:(\d{4}\.\d{4,5})(v\d+)?", paper.source)
    paper.arxiv = f"https://arxiv.org/abs/{m.group(1)}{m.group(2) or ''}" if m else None
    statements = (data.get("alignment") or {}).get("statements") or []
    paper.statements = dict(Counter(str(s.get("status", "")) for s in statements if isinstance(s, dict)))
    sorry = (data.get("status") or {}).get("sorry_count")
    paper.sorry = sorry if isinstance(sorry, int) else None


def read_papers(gh: GitHub, notes: list[str]) -> list[Paper]:
    papers = []
    for repo in gh.search("repositories", f"topic:{TOPIC}"):
        name = repo.get("full_name", "")
        if not FULL_NAME.match(name) or repo.get("private"):
            continue
        roadmap = gh.file(name, "PAPER_ROADMAP.md")
        if roadmap is None:
            notes.append(f"{name} has the topic {TOPIC} but no PAPER_ROADMAP.md: left out")
            continue
        lakefile = gh.file(name, "lakefile.toml") or ""
        m = re.search(r'^name\s*=\s*"([A-Za-z0-9_.]+)"', lakefile, re.M)
        owner, short = name.split("/")
        paper = Paper(repo=name, url=f"https://github.com/{name}",
                      site=f"https://{owner.lower()}.github.io/{short}/" if repo.get("has_pages") else None,
                      pushed=repo.get("pushed_at") or "", library=m.group(1) if m else short)
        read_roadmap(paper, roadmap)
        formalization = gh.file(name, "formalization.yaml")
        if formalization is not None:
            read_formalization(paper, formalization)
        papers.append(paper)
    papers.sort(key=lambda p: p.pushed, reverse=True)
    return papers


def attach_pull_requests(gh: GitHub, repo: str, papers: list[Paper]) -> None:
    """The pull requests of LMLExplore whose description names one of the papers."""
    by_repo = {p.repo.lower(): p for p in papers}
    for result in gh.search("issues", f'repo:{repo} is:pr "Paper:" in:body'):
        body = result.get("body") or ""
        m = re.search(r"^\s*Paper:\s*(\S+)\s*$", body, re.M)
        paper = by_repo.get(m.group(1).lower()) if m else None
        if paper is None:
            continue
        item = re.search(r"^\s*Item:\s*([A-Za-z]?\d+)\b", body, re.M)
        merged = (result.get("pull_request") or {}).get("merged_at")
        pr = {"number": int(result["number"]), "title": str(result.get("title") or ""),
              "state": "merged" if merged else str(result.get("state") or ""),
              "item": item.group(1) if item else None}
        paper.prs.append(pr)
        for it in paper.items:
            if it.id == pr["item"]:
                it.prs.append(pr)
    for paper in papers:
        paper.prs.sort(key=lambda pr: pr["number"])


# --- Rendering ----------------------------------------------------------------------------------

def esc(text: str) -> str:
    return html.escape(text, quote=True)


def inline(text: str) -> str:
    """Text from a paper repository, escaped, with its `code` spans."""
    return re.sub(r"`([^`]+)`", r"<code>\1</code>", esc(text))


def paragraphs(text: str) -> str:
    return "".join(f"<p>{inline(' '.join(p.split()))}</p>" for p in re.split(r"\n\s*\n", text) if p.strip())


def pr_link(repo: str, pr: dict) -> str:
    return f'<a href="https://github.com/{repo}/pull/{pr["number"]}">#{pr["number"]}</a>'


def status(repo: str, item: Item) -> str:
    """The item's status: from its pull requests when they say more than the roadmap."""
    merged = [pr for pr in item.prs if pr["state"] == "merged"]
    open_ = [pr for pr in item.prs if pr["state"] == "open"]
    if merged:
        return '<span class="status done">merged ' + ", ".join(pr_link(repo, pr) for pr in merged) + "</span>"
    if open_:
        return '<span class="status">pull request ' + ", ".join(pr_link(repo, pr) for pr in open_) + "</span>"
    text = item.status if item.status not in ("", "–", "-") else "in LMLExplore"
    return f'<span class="status">{esc(text)}</span>'


def file_links(paper: Paper, item: Item) -> str:
    if not item.files:
        return ""
    links = [f'<a href="{paper.url}/blob/HEAD/{urllib.parse.quote(paper.library + "/" + f)}"><code>{esc(f)}</code></a>'
             for f in item.files]
    return '<div class="files">' + ", ".join(links) + "</div>"


def decl(item: Item) -> str | None:
    m = re.search(r"`([^`]+)`", item.link)
    return m.group(1) if m else None


def decl_link(name: str, up: str) -> str:
    """A declaration of LMLExplore, on the referee site at the root of LMLExplore's site."""
    return f'<a href="{up}#/d/{urllib.parse.quote(name, safe="")}"><code>{esc(name)}</code></a>'


def paper_link(paper: Paper) -> str:
    return f'<a href="{paper.url}">{esc(paper.repo.split("/")[1])}</a>'


def tiles(stats: list[tuple[str, str]]) -> str:
    return '<div class="stat-tiles">' + "".join(
        f'<div class="stat-tile"><span class="stat-value">{esc(v)}</span><span class="stat-label">{esc(k)}</span></div>'
        for k, v in stats) + "</div>"


def section(title: str, intro: str, body: str, anchor: str = "") -> str:
    ident = f' id="{anchor}"' if anchor else ""
    return f'<div class="library-section"{ident}><p><strong>{esc(title)}</strong></p>{intro}{body}</div>'


def plural(n: int, one: str, many: str | None = None) -> str:
    return f"{n} {one if n == 1 else (many or one + 's')}"


def papers_page(papers: list[Paper], repo: str) -> str:
    proved = sum(p.statements.get("proved", 0) for p in papers)
    total = sum(sum(p.statements.values()) for p in papers)
    merged = sum(1 for p in papers for pr in p.prs if pr["state"] == "merged")
    waiting = sum(1 for p in papers for it in p.items if it.tag in ("target", "refactor", "staged")
                  and not any(pr["state"] == "merged" for pr in it.prs) and not it.status.startswith("merged"))
    out = ['<div class="library-header"><p><strong>Papers</strong></p>'
           '<p>Research papers formalized on top of <a href="../">LMLExplore</a></p></div>',
           tiles([("papers", str(len(papers))), ("main results proved", f"{proved}/{total}"),
                  ("pull requests merged", str(merged)), ("items still to contribute", str(waiting))])]
    out.append(section("How papers get here", (
        f'<p>Each paper is formalized in its own repository, made from <a href="{TEMPLATE}">lml-paper-template</a> '
        f'and following <a href="{FORMALIZE}">the formalization workflow</a>: an AI agent writes the Lean code, '
        "the paper's author checks the statements of its main results, and comparator checks that they are "
        "proved. The general results that the paper needs go to LMLExplore as pull requests; "
        '<a href="material/">What the papers bring</a> lists them.</p>'
        f"<p>A public paper repository carries the GitHub topic <code>{TOPIC}</code>, which is how this page "
        "finds it. The page is rebuilt with the site, twice a day.</p>"), ""))
    cards = []
    for p in papers:
        title = esc(p.title or p.repo)
        title = f'<a href="{p.arxiv}">{title}</a>' if p.arxiv else title
        sub = " · ".join(x for x in (esc(" and ".join(p.authors)) if p.authors else "", esc(p.source)) if x)
        counts = Counter(it.tag for it in p.items)
        st = p.statements
        results = f"{st.get('proved', 0)} of {sum(st.values())} proved" if st else "not stated yet"
        others = [f"{n} {s}" for s, n in sorted(st.items()) if s != "proved" and n]
        if others:
            results += " (" + ", ".join(esc(o) for o in others) + ")"
        if p.sorry is not None:
            results += "; no <code>sorry</code> left" if p.sorry == 0 else f"; {p.sorry} <code>sorry</code> left"
        prs = ", ".join(f'{pr_link(repo, pr)} {esc(pr["state"])}' for pr in p.prs) or '<span class="muted">none yet</span>'
        tags = ", ".join(f"{counts[t]} {name}" for t, name in (
            ("exists", "in LMLExplore"), ("target", "for a roadmap target"), ("refactor", "refactor"),
            ("staged", "staged"), ("paper", "specific to the paper")) if counts[t])
        links = [f'<a href="{p.url}">repository</a>'] + ([f'<a href="{p.site}">website</a>'] if p.site else [])
        rows = [("Links", " · ".join(links)),
                ("Main results", results),
                ("Pull requests", prs),
                ("Prerequisites", f'{tags or "none listed"} (<a href="material/#{esc(p.repo)}">details</a>)'),
                ("Roadmap", f"checked {esc(p.refreshed or 'never')}, on LMLExplore <code>{esc(p.pin or '?')}</code>")]
        cards.append(f'<div class="card" id="{esc(p.repo)}"><div class="card-title">{title}</div>'
                     f'<div class="card-sub">{sub}</div><ul class="rows">'
                     + "".join(f'<li><span class="label">{k}</span><span>{v}</span></li>' for k, v in rows)
                     + "</ul></div>")
    out.append(section("The papers", "<p>Most recently updated first.</p>",
                       "".join(cards) or '<p class="muted">No paper yet.</p>'))
    return "\n".join(out)


def material_page(papers: list[Paper], repo: str) -> str:
    up = "../../"  # the referee site, at the root of LMLExplore's site
    items = [(p, it) for p in papers for it in p.items]
    by_tag = {t: [(p, it) for p, it in items if it.tag == t] for t in ("target", "refactor", "staged", "exists", "paper")}
    used = {decl(it) for _, it in by_tag["exists"] if decl(it)}
    out = ['<div class="library-header"><p><strong>What the papers bring</strong></p>'
           '<p>The general results of the <a href="../">papers</a> built on <a href="../../">LMLExplore</a>, '
           "and where each one goes</p></div>",
           tiles([("for roadmap targets", str(len(by_tag["target"]))), ("refactors", str(len(by_tag["refactor"]))),
                  ("staged, with a proposed target", str(len(by_tag["staged"]))),
                  ("LMLExplore declarations used", str(len(used)))])]
    out.append(section("How to read this page", (
        "<p>Each paper lists its prerequisites in its <code>PAPER_ROADMAP.md</code>, one per future pull "
        "request, and says where each one goes. A result that a roadmap of "
        f'<a href="https://github.com/{ROADMAPS}">LMLRoadmaps</a> asks for is proved in the paper\'s repository, '
        "then ported to LMLExplore by the paper's agents. An improvement of a result that LMLExplore has, such as "
        "a more general version, goes there too. A general result that no roadmap asks for yet waits in the "
        "paper's repository, with a proposed target for the roadmap, until a maintainer adds it. The rest is "
        "either in LMLExplore already or specific to the paper.</p>"
        "<p>Statuses come from the papers' roadmaps, and from the pull requests of LMLExplore that name the "
        "item: <em>todo</em>, <em>proved</em> (in the paper's repository), <em>pull request</em> (open), "
        "<em>merged</em>.</p>"), ""))

    # Targets, by roadmap item.
    groups: dict[str, list] = {}
    for p, it in by_tag["target"]:
        groups.setdefault(it.link, []).append((p, it))

    def target_key(link: str):
        m = TARGET.match(link)
        return (m.group(1), [int(n) for n in m.group(2).split(".")]) if m else ("~", [link])

    cards = []
    for link in sorted(groups, key=target_key):
        m = TARGET.match(link)
        head = f'<span class="key">{esc(link)}</span>'
        if m:
            head += (f'<span class="muted">in the <a href="https://github.com/{ROADMAPS}/blob/main/LMLRoadmaps/'
                     f'{m.group(1)}/README.md">{esc(m.group(1))} roadmap</a></span>')
        rows = "".join(f'<li><span class="label">{paper_link(p)} {esc(it.id)}</span><span>{inline(it.text)} '
                       f"{status(repo, it)}{file_links(p, it)}</span></li>" for p, it in groups[link])
        cards.append(f'<div class="card"><div class="card-title">{head}</div><ul class="rows">{rows}</ul></div>')
    out.append(section("For roadmap targets",
                       "<p>The items that advance a target of LMLRoadmaps, by target.</p>",
                       "".join(cards) or '<p class="muted">None yet.</p>', "targets"))

    # Refactors.
    rows = "".join(f'<tr><td>{decl_link(decl(it), up) if decl(it) else inline(it.link)}</td>'
                   f"<td>{inline(it.text)}{file_links(p, it)}</td><td>{paper_link(p)} {esc(it.id)}</td>"
                   f"<td>{status(repo, it)}</td></tr>" for p, it in by_tag["refactor"])
    table = ('<div class="table-scroll"><table class="stats-table"><thead><tr><th scope="col">LMLExplore declaration</th>'
             '<th scope="col">Change</th><th scope="col">Paper</th><th scope="col">Status</th></tr></thead>'
             f"<tbody>{rows}</tbody></table></div>") if rows else '<p class="muted">None yet.</p>'
    out.append(section("Refactors", "<p>Improvements of declarations that LMLExplore has.</p>", table, "refactors"))

    # Staged items, with their proposed targets.
    cards = []
    for p, it in by_tag["staged"]:
        proposal = p.proposals.get(it.link.strip("`"), {})
        head = f'<span class="key">{esc(it.link)}</span>{inline(proposal.get("title") or it.text)}'
        sub = f'{paper_link(p)} {esc(it.id)}: {inline(it.text)} {status(repo, it)}'
        cards.append(f'<div class="card"><div class="card-title">{head}</div><div class="card-sub">{sub}'
                     f'{file_links(p, it)}</div><div class="text">{paragraphs(proposal.get("text", ""))}</div></div>')
    out.append(section("Staged, with a proposed target", (
        "<p>General results that no roadmap asks for yet. Each comes with a target that the paper proposes, "
        "written like an item of LMLRoadmaps; once a maintainer adds such a target to a roadmap, the paper's "
        "next round sends the item to LMLExplore.</p>"), "".join(cards) or '<p class="muted">None yet.</p>', "staged"))

    # What the papers use from LMLExplore.
    users: dict[str, list] = {}
    for p, it in by_tag["exists"]:
        users.setdefault(decl(it) or it.link, []).append((p, it))
    rows = "".join(f"<tr><td>{decl_link(name, up) if decl(users[name][0][1]) else inline(name)}</td>"
                   "<td>" + "<br>".join(f"{paper_link(p)} {esc(it.id)}: {inline(it.text)}" for p, it in users[name])
                   + "</td></tr>" for name in sorted(users))
    table = ('<div class="table-scroll"><table class="stats-table"><thead><tr><th scope="col">Declaration</th>'
             f'<th scope="col">Used for</th></tr></thead><tbody>{rows}</tbody></table></div>') if rows else '<p class="muted">None yet.</p>'
    out.append(section("Used from LMLExplore",
                       "<p>The prerequisites that LMLExplore had already, with the declaration that each paper uses.</p>",
                       table, "exists"))

    # By paper, for the links of the papers page.
    rows = "".join(f'<tr id="{esc(p.repo)}"><td>{paper_link(p)}</td>' + "".join(
        f'<td class="num">{sum(1 for it in p.items if it.tag == t)}</td>' for t in ("target", "refactor", "staged", "exists", "paper"))
        + "</tr>" for p in papers)
    table = ('<div class="table-scroll"><table class="stats-table"><thead><tr><th scope="col">Paper</th>'
             '<th scope="col" class="num">Targets</th><th scope="col" class="num">Refactors</th>'
             '<th scope="col" class="num">Staged</th><th scope="col" class="num">In LMLExplore</th>'
             f'<th scope="col" class="num">Paper only</th></tr></thead><tbody>{rows}</tbody></table></div>')
    out.append(section("By paper", "<p>How many prerequisites of each kind each paper has. The paper-specific "
                       "ones stay in the paper's repository.</p>", table, "papers"))
    out.append(section("The data", '<p>Both pages are made from <a href="../papers.json"><code>papers.json</code></a>, '
                       "by <code>scripts/papers/papers.py</code> in LMLExplore.</p>", ""))
    return "\n".join(out)


def write(path: Path, template: str, title: str, content: str, repo: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(template.replace("{{title}}", esc(title)).replace("{{repo}}", esc(repo))
                    .replace("{{content}}", content), encoding="utf-8")


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--out", type=Path, required=True, help="the folder to write to")
    p.add_argument("--repo", default=os.environ.get("GITHUB_REPOSITORY") or "LeanMachineLearning/LMLExplore",
                   help="LMLExplore's repository, for its pull requests")
    p.add_argument("--summary", type=Path, help="a Markdown file to append the report to (the run summary)")
    args = p.parse_args()
    gh = GitHub(os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN"))
    notes: list[str] = []
    papers = read_papers(gh, notes)
    attach_pull_requests(gh, args.repo, papers)
    template = (Path(__file__).with_name("page.html")).read_text(encoding="utf-8")
    write(args.out / "index.html", template, "Papers", papers_page(papers, args.repo), args.repo)
    write(args.out / "material" / "index.html", template, "What the papers bring",
          material_page(papers, args.repo), args.repo)
    (args.out / "papers.json").write_text(json.dumps([asdict(p) for p in papers], ensure_ascii=False, indent=1),
                                          encoding="utf-8")
    report = f"{len(papers)} papers, {sum(len(p.items) for p in papers)} items" + "".join(f"\n- {n}" for n in notes)
    print(report)
    if args.summary:
        with args.summary.open("a", encoding="utf-8") as f:
            f.write(f"\n### Papers pages\n\n{report}\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
