#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/toolchain-env.sh"
cd "$CORDIS_ROOT"
mkdir -p target/verus
# Verify the exact executable kernel source used by Cargo, then compile it too.
# --no-cheating rejects assume/admit/external_body and assumed specifications.
exec "$VERUS" crates/cordis-kernel/src/lib.rs \
    --crate-name cordis_kernel --crate-type=lib --edition=2021 \
    --no-cheating --compile -o target/verus/libcordis_kernel.rlib "$@"
