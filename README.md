# LMLExplore

LMLExplore is a Lean 4 library of machine learning theory, written by AI contributors following
human-written roadmaps and checked by adversarial AI review. It builds on
[Mathlib](https://github.com/leanprover-community/mathlib4),
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) and
[LML](https://github.com/LeanMachineLearning/LML), and uses the
[Tau Ceti workflow and tools](https://github.com/TauCetiProject/TauCetiTools).

## The repositories

- **LMLExplore** (this repository): the AI-authored Lean code, under `LMLExplore/`.
- **[LMLRoadmaps](https://github.com/LeanMachineLearning/LMLRoadmaps)**: the human-written
  roadmaps that decide what gets built.
- **[TauCetiReview](https://github.com/TauCetiProject/TauCetiReview)**: the review rubrics and
  the engine that runs them.

## Relationship to LML and Tau Ceti

LMLExplore never proposes material to its dependencies. LML's maintainers pick, by hand, what
they want to curate into LML. Material planned elsewhere (for example in Tau Ceti's roadmaps) does
not block work here: when a dependency later provides something LMLExplore already has, the copy
here is deleted and its uses move to the upstream declaration.

## Dependency versions

The dependencies move together, only at Lean releases that both Tau Ceti and LML have tagged:

- Tau Ceti at its release tag (for example `v4.36.0-rc1`);
- Mathlib at the commit that Tau Ceti's tag pins, required directly so that it wins over the
  inherited pins;
- LML at its last commit on the same Lean toolchain;
- `lean-toolchain` set to that release.

A maintainer prepares each sync as a pull request changing `lake-manifest.json` and
`lean-toolchain`, together with any repairs it needs.

## Building

```bash
scripts/build.sh
```

The script fetches Mathlib's prebuilt files (`lake exe cache get`) and Tau Ceti's, from Tau Ceti's
public Lake artifact cache, then runs `lake build`; arguments are passed on to `lake build`.
A plain `lake exe cache get && lake build` also works, but compiles the Tau Ceti modules that
LMLExplore imports.

## Contributing

Code is contributed by agents running the
[Tau Ceti worker](https://github.com/TauCetiProject/TauCetiWorker) against this project's
configuration, on the operator's own subscription:

```bash
uv tool install git+https://github.com/TauCetiProject/TauCetiWorker
tauceti --conf https://raw.githubusercontent.com/LeanMachineLearning/LMLExplore/main/tauceti.toml doctor
tauceti --conf https://raw.githubusercontent.com/LeanMachineLearning/LMLExplore/main/tauceti.toml work
```

To review a pull request with the same engine and rubrics as CI:

```bash
uvx --from git+https://github.com/TauCetiProject/TauCetiReview tauceti-review PR_NUMBER \
  --conf https://raw.githubusercontent.com/LeanMachineLearning/LMLExplore/main/tauceti.toml
```

Humans contribute by writing and reviewing roadmaps in
[LMLRoadmaps](https://github.com/LeanMachineLearning/LMLRoadmaps), and by raising issues here.
Agents read `AGENTS.md` before working in this repository.
