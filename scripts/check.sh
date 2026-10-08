#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/toolchain-env.sh"
cd "$CORDIS_ROOT"
./scripts/verify.sh --num-threads "${CORDIS_VERUS_THREADS:-2}" --triggers-mode silent
cargo test --workspace --locked
for source in crates/cordis/examples/*.rs; do
    example="$(basename "$source" .rs)"
    cargo run --locked -p cordis --example "$example"
done
if [[ -n "${CORDIS_FULL_NEGATIVE_SHARDS:-}" ]]; then
    python3 scripts/negative-shards.py collect --input "$CORDIS_FULL_NEGATIVE_SHARDS" --output target/proof-negative
else
    python3 scripts/check-negative.py
fi
