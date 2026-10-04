#!/usr/bin/env bash
# Source this file from another script. All paths remain valid after moving the project.
CORDIS_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export PATH="${CARGO_HOME:-$HOME/.cargo}/bin:$PATH"
CORDIS_VERUS_DIR="$(PYTHONDONTWRITEBYTECODE=1 python3 - "$CORDIS_ROOT" <<'PY'
import importlib.util
from pathlib import Path
import sys
root = Path(sys.argv[1])
spec = importlib.util.spec_from_file_location('cordis_install', root / 'scripts/install-verus.py')
installer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(installer)
print(root / '.tools' / installer.LOCK['verus']['assets'][installer.platform_key()]['directory'])
PY
)"
export RUSTUP_TOOLCHAIN="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["rust"]["channel"])' "$CORDIS_ROOT/toolchain.lock.json")"
if [[ ! -x "$CORDIS_VERUS_DIR/verus" ]]; then
    echo 'Verus is missing. Run ./scripts/install-verus.sh first.' >&2
    return 1
fi
export VERUS="$CORDIS_VERUS_DIR/verus"
export PATH="$CORDIS_VERUS_DIR:$PATH"
