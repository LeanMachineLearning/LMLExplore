# Papers built on LMLExplore

Two pages of LMLExplore's site list the research papers formalized on top of LMLExplore, and what
they bring to it:

* https://leanmachinelearning.org/LMLExplore/papers/: each paper, with the status of its main
  results and its pull requests to LMLExplore;
* https://leanmachinelearning.org/LMLExplore/papers/material/: the papers' prerequisites by tag:
  those that advance a target of [LMLRoadmaps](https://github.com/LeanMachineLearning/LMLRoadmaps),
  by target; the refactors of LMLExplore code; the `staged` items, with the target that each paper
  proposes for a roadmap; and the declarations of LMLExplore that the papers use.

Their data is published beside them as `papers.json`.

## Where the data comes from

A paper project is a repository made from
[lml-paper-template](https://github.com/LeanMachineLearning/lml-paper-template), formalized with the
`lml` plugin of [lml-claude](https://github.com/LeanMachineLearning/lml-claude) (see
https://leanmachinelearning.org/formalize/). A public one carries the GitHub topic
`lmlexplore-paper`, which `START.md` of lml-claude adds; private and local paper projects are not
listed. From each, `papers.py` reads through the GitHub API:

* `PAPER_ROADMAP.md`: one row per prerequisite, tagged `exists`, `target`, `refactor`, `staged` or
  `paper`, with its status, and the proposed targets of the `staged` items, in the format that the
  `paper-roadmap` skill of the plugin fixes;
* `formalization.yaml`: the paper, and the status of each main result;
* `lakefile.toml`: the name of the Lean library, the folder that the roadmap's files are in.

It also reads the pull requests of LMLExplore whose description has the lines
`Paper: <owner>/<repo>` and `Item: <Id>`, which the paper's Tau Ceti workers write. An item's status
on the pages is the newest of its pull requests' (merged, then open), else the one its roadmap
gives.

The referee site workflow (`.github/workflows/referee-site.yml`) writes the pages at each build,
twice a day:

```bash
GH_TOKEN=... python3 scripts/papers/papers.py --out OUT --summary SUMMARY
```

It needs PyYAML. The token only reads public data. A failure leaves the pages out of the site
without stopping it.

## Safety

The pages show text written in other people's repositories, on leanmachinelearning.org. Everything
read from a paper repository is escaped; only its `code` spans are rendered. Links are built by the
script from the names that GitHub returns (repositories, pull request numbers, declarations, file
paths), never taken from the files.

## The look

The pages share the visual identity of https://leanmachinelearning.org, as the literature page
does: `page.html` loads the site's stylesheet (`/static/style.css`), uses its classes
(`library-page`, `stat-tiles`, `stats-table`) and colours, and copies its navigation bar and footer.
When the site's navigation or footer change, update them here and in `scripts/literature/page.html`.
