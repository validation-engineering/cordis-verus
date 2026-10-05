#!/usr/bin/env bash
# The local equivalent of the required CI job. Never publishes anything.
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/toolchain-env.sh"
cd "$CORDIS_ROOT"
node scripts/sync-profile-types.mjs --check
python3 scripts/check-paper-coverage.py
python3 -m unittest discover -s scripts/tests
cargo fmt --all --check
cargo clippy --workspace --all-targets --locked -- -D warnings
RUSTDOCFLAGS="${RUSTDOCFLAGS:-} -D warnings" cargo doc --workspace --no-deps --locked
./scripts/check.sh
node scripts/build-node.mjs "$@"
node --test --test-timeout=30000 --test-reporter=tap tests/node-compat/*.test.mjs tests/node-loader/*.test.mjs tests/benchmarks/*.test.mjs
python3 scripts/package-check.py "$@"
node scripts/check-npm-package.mjs
