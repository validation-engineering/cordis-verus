#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/toolchain-env.sh"
cd "$CORDIS_ROOT"
./scripts/verify.sh --triggers-mode silent
cargo test --workspace --locked
for source in crates/cordis/examples/*.rs; do
    example="$(basename "$source" .rs)"
    cargo run --locked -p cordis --example "$example"
done
python3 scripts/check-negative.py
