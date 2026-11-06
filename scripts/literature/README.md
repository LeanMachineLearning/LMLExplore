# Literature links

The page https://leanmachinelearning.org/LMLExplore/literature/ lists the results of the literature
that LMLExplore's declarations cite, and the declarations that cite them. Its data is published
beside it as `annotations.jsonl`, in the
[Literature Links](https://github.com/mathlib-initiative/literature-links) format: one annotation
per declaration and cited result, whose subject is the result, as a part of its work, and whose
object is the declaration at the commit of the build. The annotations have no `relation`: they say
that the two sides correspond, not how.

The referee site workflow (`.github/workflows/referee-site.yml`) writes both from the dataset of
the build, with `annotations.py`:

```bash
python3 scripts/literature/annotations.py --dataset DATASET \
  --bibliography scripts/literature/bibliography.json --out OUT
```

and checks the annotations with the format's checker, `literature-links validate`.

## Where the links come from

A citation of a numbered result, `[KEY, Theorem 14]`, in a declaration's docstring, or in an entry of
a `## Main ...` list of a module docstring, which links it to the declarations that the entry names
in backquotes before its colon. The locator may name several results (`[LS, Lemmas 8.2, 8.3]`,
`[DK19, Lemma 6 and Theorem 7]`), a part (`[P, Theorem 6.2.2 (a)]`), a proof
(`[GK16, proof of Theorem 14]`) or an equation (`[LS, (20.9)]`). A citation of a whole work, `[GK16]`,
gives no link.

## The works

`bibliography.json` describes each work by its citation key: `uri`, a link to the work (its arXiv
page, its DOI, or its page at the publisher); `citation`, a [CSL-JSON](https://citeproc-js.readthedocs.io/en/latest/csl-json/markup.html)
item; `identifiers`, such as `{"arxiv": "1602.04589"}`; and `version`, the revision whose numbering
the docstrings use, when it is not the published one (`v4` of an arXiv preprint). A key that it does
not describe falls back to the text that the modules' `## References` sections give for it, so add
a work here when LMLExplore starts citing it.
