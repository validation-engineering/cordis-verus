#!/usr/bin/env bash
# The local equivalent of the required CI job. Never publishes anything.
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/toolchain-env.sh"
cd "$CORDIS_ROOT"
python3 scripts/check-paper-coverage.py
python3 -m unittest discover -s scripts/tests
cargo fmt --all --check
cargo clippy --workspace --all-targets --locked -- -D warnings
RUSTDOCFLAGS="${RUSTDOCFLAGS:-} -D warnings" cargo doc --workspace --no-deps --locked
./scripts/check.sh
python3 scripts/package-check.py "$@"
