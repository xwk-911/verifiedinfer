#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROJECT="$(cd "$ROOT/../.." && pwd)"
# Use the project's existing matching libraries without changing system drivers.
if [[ -z "${CUDA_DRIVER_LIBRARY:-}" && -r /sys/module/nvidia/version ]]; then
  driver_version=$(cat /sys/module/nvidia/version)
  compat="$PROJECT/build/nvidia-compat/$driver_version"
  if [[ -r "$compat/libcuda.so.1" ]]; then
    export CUDA_DRIVER_LIBRARY="$compat/libcuda.so.1"
    export LD_LIBRARY_PATH="$compat${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
  fi
fi
exec python3 "$ROOT/scripts/check_gpu.py" "$@"
