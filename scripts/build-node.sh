#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/toolchain-env.sh"
cd "$CORDIS_ROOT"
if [[ $# -eq 1 && "$1" == "--offline" ]]; then
  export CARGO_NET_OFFLINE=true
elif [[ $# -ne 0 ]]; then
  echo 'Usage: build-node.sh [--offline]' >&2
  exit 2
fi
cargo build --locked -p cordis-node --lib --examples --message-format=json-render-diagnostics
