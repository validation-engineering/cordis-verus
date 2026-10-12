#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/toolchain-env.sh"
cd "$CORDIS_ROOT"
python3 scripts/check-positive.py
echo 'BEGIN WORKSPACE TESTS'
cargo test --workspace --all-features --locked
echo 'END WORKSPACE TESTS'
cargo run --locked -p cordis-kernel --example semantic_context
for source in crates/cordis/examples/*.rs; do
    example="$(basename "$source" .rs)"
    cargo run --locked --all-features -p cordis-verus --example "$example"
done
