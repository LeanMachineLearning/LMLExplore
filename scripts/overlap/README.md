# Upstream overlap scan

LMLExplore never waits for its dependencies: it may build material that Mathlib, Tau Ceti or LML
later provide. This scan finds such material after each dependency sync, so that LMLExplore can
delete its copy and use the upstream version. It also catches duplicates of material that already
existed upstream, which review cannot see for Tau Ceti and LML: the review engine only gives
reviewers Mathlib's source.

The design follows Tau Ceti's Mathlib overlap scanner (scan, then one issue per finding, then one
refactor pull request per issue). Because LMLExplore moves its pins only at syncs, each scan simply
covers the range between the previous pins and the current ones, for every upstream marked
`overlap = true` in `tauceti.toml`.

## Procedure

Run these from an up-to-date checkout of `main`, right after a sync has landed.

1. Check out the dependencies at their new pins:

   ```bash
   scripts/build.sh
   ```

2. Collect the material to compare (mechanical, a few seconds):

   ```bash
   python3 scripts/overlap/collect.py
   ```

   It prints the bundle directory it created under `.lake/overlap-scan/`. By default it compares
   with the previous sync, the previous commit that changed `lake-manifest.json`; use `--since` to
   choose another LMLExplore commit, or `--old PACKAGE=REV` to override one upstream's previous pin.

3. Have an agent run the scan, which only writes `result.json` in the bundle:

   ```bash
   claude "Follow scripts/overlap/scan.md with the bundle <bundle directory>"
   ```

4. Read `result.json`, then publish one issue per finding (labelled `upstream-overlap`). Findings
   that already have an issue are skipped:

   ```bash
   python3 scripts/overlap/publish.py <bundle directory>          # dry run
   python3 scripts/overlap/publish.py <bundle directory> --apply  # create the issues
   ```

5. Resolve each issue with a refactor pull request, which goes through normal review:

   ```bash
   claude "Follow scripts/overlap/fix.md for issue #<number>"
   ```

## Files

- `collect.py`: lists the declarations each upstream added or changed between its two pins
  (ignoring moves and private declarations), and LMLExplore's new and current declarations.
- `scan.md`: instructions for the read-only scan.
- `publish.py`: turns the scan result into issues.
- `fix.md`: instructions for resolving one issue.
