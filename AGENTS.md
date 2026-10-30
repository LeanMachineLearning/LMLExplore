# Working in LMLExplore

This is the AI-owned code repository of LMLExplore, a Lean 4 library of machine learning theory
built on top of Mathlib, [Tau Ceti](https://github.com/TauCetiProject/TauCeti) and
[LML](https://github.com/LeanMachineLearning/LML). It follows the Tau Ceti workflow: humans write
the roadmaps, AIs write the code, and AI reviewers judge every pull request against fixed rubrics.
Read `README.md` for how the repositories fit together; this file is the contract for agents.

## Before you write code

**Read the roadmap first.** The roadmaps live in
[LMLRoadmaps](https://github.com/LeanMachineLearning/LMLRoadmaps). The roadmap gates *new*
mathematics: only add a new mathematical declaration (definition, theorem, instance, notation) or
file when it advances a specific LMLRoadmaps target, or supplies a prerequisite that a specific
target needs. If what you want to build is not on the roadmap, select a target the roadmaps do
support instead. Never open a pull request or an issue in LMLRoadmaps yourself.

Improving code that already exists is **always in scope** and needs no roadmap entry:
refactoring, simplifying proofs, fixing or modestly generalising an existing lemma, relocating a
misplaced declaration, adopting a cleaner idiom, documenting existing code, and deleting material
that a dependency now provides.

Every pull request description contains one standalone attribution line, `Roadmap: AreaName`
(the LMLRoadmaps directory name), or `Roadmap: none` for cross-cutting, infrastructure or
dependency work.

## The dependencies

LMLExplore depends on Mathlib, Tau Ceti and LML, at the exact versions recorded in
`lake-manifest.json` (their sources are under `.lake/packages/`).

- **Reuse what exists.** Before adding a declaration, search all three dependencies as well as
  `LMLExplore/` for it, up to renaming, generalisation and definitional unfolding. Material that
  already exists at the pinned version must be used, never restated.
- **Other projects' plans do not block you.** Tau Ceti's own roadmaps, open pull requests to
  Mathlib, Tau Ceti or LML, and anything else that is planned but not present at the pinned
  versions, are not reasons to wait or to skip a target. Build what the LMLRoadmaps target needs
  here, now. Where such a plan, pull request or Mathlib convention already fixes a name or a
  statement shape, follow it, so that adopting the upstream version later is a deletion plus an
  import rather than a rewrite.
- **Duplicates are deleted later, here.** When a dependency bump brings in material that
  LMLExplore already has, LMLExplore deletes its copy and migrates every use to the upstream
  declaration, keeping any additional mathematics.
- **Never contribute upstream.** Do not open pull requests or issues in Mathlib, Tau Ceti or LML.
  Their maintainers decide, by hand, whether to adopt anything from here.

## The rules of the repo

- `main` is always green. CI builds against the pinned dependencies and enforces: no `sorry`, no
  axioms beyond `propext`, `Classical.choice` and `Quot.sound` (so no `native_decide`), no
  `meta import`, and the Mathlib linter set with warnings as errors (style, header, file length,
  no `maxHeartbeats` overrides). Do not try to disable these.
- Every file starts with the copyright header and then `module`, as in LML and Tau Ceti.
- `set_option` is forbidden anywhere in library code, including `set_option hygiene false`. Prefer
  named definitions, abbreviations and lemmas to custom term syntax. Local tactic macros must
  remove substantial repeated proof machinery. No meta or unsafe declarations, elaborators,
  initializers, `run_cmd`/`run_tac`/`#eval`, or nonlocal macros: Lean meta code is human-owned and
  lives in `scripts/`.
- One topic per pull request. Ship a prerequisite refactor as its own pull request.
- Stacked pull requests are prohibited, including drafts. Wait for each prerequisite to land on
  `main`, then rebase onto `main` and include only the new work.
- No backwards compatibility. When a declaration or module is moved, renamed, replaced or deleted
  (including because a dependency now provides it), update every use and remove the old name in
  the same pull request. No aliases, wrappers, forwarding modules or `deprecated` shims.
- `LMLExplore/` is the only place code goes. Do not edit the root `LMLExplore.lean`: the
  lakefile's glob builds every module under `LMLExplore/` without it.
- Human-owned: `scripts/`, `.github/`, `lakefile.toml`, `tauceti.toml`, `README.md`, this file,
  and the pins `lake-manifest.json` and `lean-toolchain`. The pins move only when a maintainer
  syncs the dependencies to a new Lean release; never bump them yourself.
- Never delete a pull request's human-owned changes to get it past the build gate, and never
  admin-merge an AI-authored pull request.

## How review works

Open a pull request against `main` from your fork. After CI passes, AI reviewers judge it against
the [Tau Ceti rubrics](https://github.com/TauCetiProject/TauCetiReview/tree/main/rubrics)
(correctness, reuse, scope, attribution, API design, generality, placement, naming,
documentation, proof quality) and post `approve` / `request_changes` / `block` verdicts. Address
the findings and push. If two findings contradict each other, contest one of the threads, link
the other and quote its wording, rather than silently satisfying one.

When every rubric approves the current commit, the pull request changes only `LMLExplore/` and
CI is green, it merges through the merge queue. A pull request touching any human-owned path
needs a human.
