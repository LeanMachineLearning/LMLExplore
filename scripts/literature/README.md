# Literature links

The page https://leanmachinelearning.org/LMLExplore/literature/ lists the results of the literature
that LMLExplore's declarations and its [roadmaps](https://github.com/LeanMachineLearning/LMLRoadmaps)
cite, the declarations and the roadmap items that cite them, and how many of the results that the
roadmaps cite have a declaration, for each work and each roadmap. Its data is published beside it as
`annotations.jsonl`, in the [Literature Links](https://github.com/mathlib-initiative/literature-links)
format. The subject of each annotation is a result, as a part of its work, and its object is:

* a declaration that cites the result, at the commit of the build: one annotation per declaration
  and result it cites;
* nothing, for a result that the roadmaps cite and no declaration does: the result is not linked
  yet. It may be formalized without the citation, or not at all.

The annotations have no `relation`: they say that the two sides correspond, not how. The extension
`org.leanmachinelearning.lmlroadmaps` of an annotation names the roadmap items that cite its result,
as `Identification 5.2`, with the commit of LMLRoadmaps they were read at. Sections, chapters,
appendices, figures and tables that the roadmaps cite are places, not results, and count in no
coverage.

The referee site workflow (`.github/workflows/referee-site.yml`) writes both from the dataset of
the build and a checkout of LMLRoadmaps, with `annotations.py`:

```bash
python3 scripts/literature/annotations.py --dataset DATASET \
  --bibliography scripts/literature/bibliography.json --out OUT \
  --roadmaps LMLROADMAPS --roadmaps-commit SHA
```

and checks the annotations with the format's checker, `literature-links validate`.

The page shares the visual identity of https://leanmachinelearning.org: it loads the site's
stylesheet (`/static/style.css`, on the same domain), uses its classes (`library-page`, `stat-tiles`,
`stats-table`) and colours, and copies its navigation bar and footer into `page.html`. When the
site's navigation or footer change, update them here.

## Where the links come from

A citation of a numbered result, `[KEY, Theorem 14]`, in a declaration's docstring, or in an entry of
a `## Main ...` list of a module docstring, which links it to the declarations that the entry names
in backquotes before its colon. In a roadmap, the same citation names a result that LMLExplore aims
at, cited by the target of the layer it is in (`Area N.k`), or by the roadmap as a whole outside the
layers. The locator may name several results (`[LS, Lemmas 8.2, 8.3]`, `[LS, Lemmas 12.2–12.4]`,
`[DK19, Lemma 6 and Theorem 7]`), a part (`[P, Theorem 6.2.2 (a)]`), a proof
(`[GK16, proof of Theorem 14]`) or an equation (`[LS, (20.9)]`). A citation of a whole work, `[GK16]`,
gives no link.

## The works

`bibliography.json` describes each work by its citation key: `uri`, a link to the work (its arXiv
page, its DOI, or its page at the publisher); `citation`, a [CSL-JSON](https://citeproc-js.readthedocs.io/en/latest/csl-json/markup.html)
item; `identifiers`, such as `{"arxiv": "1602.04589"}`; and `version`, the revision whose numbering
the docstrings use, when it is not the published one (`v4` of an arXiv preprint). A key that it does
not describe falls back to the text that the modules' `## References` sections, then the roadmaps'
References, give for it, with the arXiv ID that the text names if any. Add a work here when
LMLExplore or a roadmap starts citing it, to give it a full citation and a link. A work cited under
two keys has one entry, and the other key maps to it: `"CT06": {"same": "CT"}`.

## Keeping the bibliography up to date

The page is rewritten at every build, so new citations in the docstrings and the roadmaps appear by
themselves. The bibliography does not: a work cited for the first time is shown from its reference
text, and a work cited under a new key gets a second section. The summary of each run of the referee
site workflow lists both, under "Literature page". To fix them:

```bash
python3 scripts/literature/lookup.py propose --out proposals.json
python3 scripts/literature/lookup.py merge proposals.json
```

`propose` reads the annotations of the live site (or `--annotations FILE`), and proposes an alias for
each work whose reference text names a work of the bibliography, and otherwise an entry found in
Crossref and arXiv, under the rules its docstring gives: an exact title and the first author, and
the version the text cites. Review `proposals.json` before merging: the work, its version (the
edition, the conference or journal version) and its authors. Delete or correct what is wrong, and
add by hand what it could not find. `merge` adds the proposals to `bibliography.json` without
replacing any entry, and checks the result; then open a pull request.
