#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/toolchain-env.sh"
cd "$CORDIS_ROOT"
python3 scripts/check-positive.py
echo 'BEGIN WORKSPACE TESTS'
cargo test --workspace --locked
echo 'END WORKSPACE TESTS'
for source in crates/cordis/examples/*.rs; do
    example="$(basename "$source" .rs)"
    cargo run --locked -p cordis-verus --example "$example"
done
