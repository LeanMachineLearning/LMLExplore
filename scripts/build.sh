#!/usr/bin/env bash
# Build LMLExplore, reusing Mathlib's and Tau Ceti's prebuilt files instead of compiling them.
#
# Usage: scripts/build.sh [lake build arguments]
#
# Mathlib's files come from `lake exe cache get`. Tau Ceti publishes its own build outputs in a
# public, anonymous Lake artifact cache; this script fetches the index for the pinned Tau Ceti
# revision, and Lake then downloads the Tau Ceti modules the build actually needs. The cache
# settings must stay active during `lake build`, which is why the build runs here too.
#
# The Tau Ceti files only match when Mathlib and the Lean toolchain are exactly the ones Tau Ceti
# was built with, which the dependency policy in README.md guarantees. On any cache problem the
# script falls back to compiling the needed Tau Ceti modules from source.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

lake exe cache get

config="$root/.lake/tauceti-cache.toml"
mkdir -p "$root/.lake"
cat > "$config" <<'TOML'
cache.defaultService = "tauceti-public"
[[cache.service]]
name = "tauceti-public"
kind = "s3"
artifactEndpoint = "https://cache.taucetiproject.org/artifacts"
revisionEndpoint = "https://cache.taucetiproject.org/revisions"
TOML

export LAKE_CONFIG="$config"
export LAKE_CACHE_DIR="$root/.lake/cache"
export LAKE_ARTIFACT_CACHE=true
export LAKE_RESTORE_ARTIFACTS=true

if ! lake cache get --service tauceti-public --repo TauCetiProject/TauCeti \
    --package TauCeti --max-revs=1 --mappings-only; then
  echo "warning: no Tau Ceti cache for the pinned revision; compiling the Tau Ceti modules needed" >&2
  unset LAKE_CONFIG LAKE_CACHE_DIR
  export LAKE_ARTIFACT_CACHE=false LAKE_RESTORE_ARTIFACTS=false
fi

lake build "$@"
