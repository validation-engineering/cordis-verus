#!/usr/bin/env bash
# Daily development checks. Full mutation testing remains in quality.sh.
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/toolchain-env.sh"
cd "$CORDIS_ROOT"
if [[ $# -eq 1 && "$1" == "--offline" ]]; then
    export CARGO_NET_OFFLINE=true
elif [[ $# -ne 0 ]]; then
    echo "Usage: $0 [--offline]" >&2
    exit 2
fi
node scripts/sync-profile-types.mjs --check
python3 scripts/check-paper-coverage.py
python3 scripts/check-paper-review.py
python3 -m unittest discover -s scripts/tests
cargo fmt --all --check
cargo clippy --workspace --all-targets --locked -- -D warnings
RUSTDOCFLAGS="${RUSTDOCFLAGS:-} -D warnings" cargo doc --workspace --no-deps --locked
./scripts/verify.sh --num-threads "${CORDIS_VERUS_THREADS:-2}" --triggers-mode silent
echo 'BEGIN WORKSPACE TESTS'
cargo test --workspace --locked
echo 'END WORKSPACE TESTS'
for source in crates/cordis/examples/*.rs; do
    cargo run --locked -p cordis --example "$(basename "$source" .rs)"
done
node scripts/build-node.mjs "$@"
echo 'BEGIN NODE COMPATIBILITY TESTS'
node --test --test-concurrency=4 --test-timeout=30000 --test-reporter=tap tests/node-compat/*.test.mjs tests/node-loader/*.test.mjs tests/benchmarks/*.test.mjs
echo 'END NODE COMPATIBILITY TESTS'
python3 scripts/package-check.py "$@"
node scripts/check-npm-package.mjs
echo 'DEVELOPMENT CHECKS PASSED; full negative controls and release acceptance are separate.'
