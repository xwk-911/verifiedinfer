#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if [[ -n "${LEAN_TOOLCHAIN_DIR:-}" ]]; then
  export PATH="$LEAN_TOOLCHAIN_DIR/bin:$PATH"
fi
cd "$ROOT"
test "$(git -C vendor/iris-lean rev-parse HEAD)" = 956f5482cf6f3970bb34d68e3813c73b0f9b1245
cargo fmt --check
cargo test --locked
cargo clippy --locked --all-targets -- -D warnings
python3 scripts/check.py
