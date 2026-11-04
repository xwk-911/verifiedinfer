#!/bin/bash
set -euo pipefail
root="$WORKSPACE/tools/ptx-verify"
cd "$root"
if [[ ! -d vendor/iris-lean || ! -d lean/.lake/packages/mathlib ]]; then
    bash scripts/bootstrap.sh
fi
test "$(git -C vendor/iris-lean rev-parse HEAD)" = 956f5482cf6f3970bb34d68e3813c73b0f9b1245
export CARGO_TARGET_DIR="$WORKSPACE/build/container/ptx-target"
export PTXAS=/usr/local/cuda/bin/ptxas
if [[ ! -d lean/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib ]]; then
    (cd lean && lake exe cache get)
fi
exec bash scripts/check.sh "$@"
