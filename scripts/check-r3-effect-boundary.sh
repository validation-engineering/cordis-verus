#!/usr/bin/env bash
# Prove the shared runtime fixture's return law, then reproduce its real failure.
# This is a contract-boundary check, not whole-kernel or R3 acceptance.
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/toolchain-env.sh"
cd "$CORDIS_ROOT"
CORDIS_BOUNDARY_TMP="$(mktemp -d "${TMPDIR:-/tmp}/cordis-effect-boundary.XXXXXX")"
trap 'rm -rf -- "$CORDIS_BOUNDARY_TMP"' EXIT
cp -R crates/cordis-kernel/src "$CORDIS_BOUNDARY_TMP/src"
cp crates/cordis-kernel/tests/support/replay_effect_boundary.rs "$CORDIS_BOUNDARY_TMP/src/replay_effect_boundary.rs"
cat >> "$CORDIS_BOUNDARY_TMP/src/lib.rs" <<'RS'
#[path = "replay_effect_boundary.rs"]
mod replay_effect_boundary;
RS
"$VERUS" "$CORDIS_BOUNDARY_TMP/src/lib.rs" --crate-name cordis_kernel \
    --crate-type=lib --edition=2021 --no-cheating \
    --verify-only-module replay_effect_boundary --triggers-mode silent
CARGO_INCREMENTAL=0 cargo test -p cordis-kernel --test replay_effect_boundary --locked --offline
