#!/usr/bin/env bash
# Release quality reuses the development checks without repeating the proof.
# Runtime asset collection/installation is an additional release workflow step.
set -euo pipefail
cd "$(dirname -- "${BASH_SOURCE[0]}")/.."
./scripts/check-development.sh "$@"
echo 'RELEASE QUALITY CHECKS PASSED; full negative regressions are separate.'
