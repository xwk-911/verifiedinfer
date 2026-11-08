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
python3 -m unittest discover -s scripts -p test_rejection_harness.py
python3 -m unittest discover -s scripts -p test_verify.py
python3 scripts/check.py
if [[ "${PTX_VERIFY_GPU:-0}" == 1 ]]; then
  bash scripts/check_gpu.sh
fi
