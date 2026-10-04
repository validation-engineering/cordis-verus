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
python3 scripts/check-paper-coverage.py
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
python3 scripts/package-check.py "$@"
echo 'DEVELOPMENT CHECKS PASSED; full negative controls and release acceptance are separate.'
