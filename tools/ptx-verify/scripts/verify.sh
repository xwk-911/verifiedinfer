#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if [[ -n ${LEAN_TOOLCHAIN_DIR:-} ]]; then
    export PATH="$LEAN_TOOLCHAIN_DIR/bin:$PATH"
fi
exec python3 "$ROOT/scripts/verify.py" "$@"
