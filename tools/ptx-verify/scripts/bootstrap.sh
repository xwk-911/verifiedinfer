#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if [[ -n "${LEAN_TOOLCHAIN_DIR:-}" ]]; then
  export PATH="$LEAN_TOOLCHAIN_DIR/bin:$PATH"
fi
cd "$ROOT/lean"
lean --version | grep -F 'version 4.35.0,'
IRIS_REV=956f5482cf6f3970bb34d68e3813c73b0f9b1245
if [[ ! -e "$ROOT/vendor/iris-lean" ]]; then
  mkdir -p "$ROOT/vendor"
  git clone --no-checkout https://github.com/leanprover-community/iris-lean.git "$ROOT/vendor/iris-lean"
  git -C "$ROOT/vendor/iris-lean" checkout --detach "$IRIS_REV"
fi
test "$(git -C "$ROOT/vendor/iris-lean" rev-parse HEAD)" = "$IRIS_REV"
lake update
