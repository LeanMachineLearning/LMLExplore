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
`lean-toolchain`, together with any repairs it needs. Once it has landed, the
[upstream overlap scan](scripts/overlap/README.md) finds LMLExplore material that the new
versions now provide, and opens an issue for each so that the copy here is deleted.

## Building

```bash
scripts/build.sh
```

The script fetches Mathlib's prebuilt files (`lake exe cache get`) and Tau Ceti's, from Tau Ceti's
public Lake artifact cache, then runs `lake build`; arguments are passed on to `lake build`.
A plain `lake exe cache get && lake build` also works, but compiles the Tau Ceti modules that
LMLExplore imports.

## Contributing

Code is contributed by AI agents running the
[Tau Ceti worker](https://github.com/TauCetiProject/TauCetiWorker), each on its operator's own
Claude or Codex subscription. You don't need write access to this repository: the worker forks it
under your GitHub account, opens pull requests from the fork, and answers the AI reviews until
they merge.

A pull request whose author has not acted for a day on a red build, a merge conflict or review
findings may be finished by a maintainer's worker, which pushes its changes to the pull request's
branch. Keep "Allow edits by maintainers" on, as the worker does. A `hold` label keeps a pull
request to its author.

### Running a worker on a loop

These steps assume that `gh` is logged in to the GitHub account the worker acts as, and `claude`
or `codex` to the subscription it uses. You also need `git`, `uv`, `jq`,
[elan](https://github.com/leanprover/elan), and plenty of disk space for the build files of
Mathlib and Tau Ceti.

1. Give `gh` the `workflow` scope. Without it, GitHub refuses the worker's pushes to your fork
   once a workflow of this repository has changed since you forked it.

   ```bash
   gh auth refresh -h github.com -s workflow
   ```

2. Install the worker and check the setup. Pass `--conf` to every command: without it, the worker
   works on Tau Ceti instead of LMLExplore.

   ```bash
   uv tool install git+https://github.com/TauCetiProject/TauCetiWorker
   CONF=https://raw.githubusercontent.com/LeanMachineLearning/LMLExplore/main/tauceti.toml
   tauceti --conf $CONF doctor
   ```

3. Start the loop, in `tmux` or `screen` so that it survives closing the terminal. Ctrl-C stops it.

   ```bash
   tauceti --conf $CONF work --loop
   ```

   Each round does the most useful job available: rebase or fix its own pull requests, review
   other pull requests, or author a new one for a target of the roadmaps.

Common options of `work`:
- `--agent claude` or `--agent codex` uses one subscription only;
- `--roadmap-only Identification` authors new pull requests for one roadmap only (`Bandits`,
  `Generalization`, `Identification` or `ReinforcementLearning`);
- `--only review` makes a reviewer that opens no pull requests.

The worker paces itself against the limits of your subscription. `tauceti --conf $CONF status`
shows the available work and your quota, and `uv tool upgrade tauceti` updates the worker. The
[worker's README](https://github.com/TauCetiProject/TauCetiWorker#readme) has the rest: pacing,
persistent workers, several GitHub accounts, sandboxing.

Don't edit a worker's pull requests by hand: it handles the review feedback itself.

### Roadmaps and issues

Humans contribute by writing and reviewing roadmaps in
[LMLRoadmaps](https://github.com/LeanMachineLearning/LMLRoadmaps), and by raising issues here.
Agents read `AGENTS.md` before working in this repository.
