#!/bin/bash
set -euo pipefail
cd "${WORKSPACE:?Compose must bind the project workspace}"
export XDG_CACHE_HOME="$WORKSPACE/build/container-cache"
export HF_HOME="$XDG_CACHE_HOME/huggingface"
export CARGO_HOME="$XDG_CACHE_HOME/cargo"
mkdir -p "$XDG_CACHE_HOME" "$CARGO_HOME"
export GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=safe.directory GIT_CONFIG_VALUE_0="$WORKSPACE"

if [[ ${VI_DRIVER_COMPAT:-0} == 1 ]]; then
    version=$(cat /sys/module/nvidia/version)
    compat="$WORKSPACE/build/nvidia-compat/$version"
    test -r "$compat/libcuda.so.1"
    export LD_LIBRARY_PATH="$compat${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
    export PATH="$compat:$PATH"
fi

case "${VI_SERVICE:-}:${1:-}" in
    engine:generate) shift; exec python3 /opt/verifiedinfer/infer.py "$@" ;;
    qcp:check)
        shift
        # The upstream foundation is compiled into the image. Project-local
        # proof/Rocq may intentionally use different rules and remains separate.
        exec make -C "${QCP_IMAGE_ROOT:?}/Rocq" -j"${MAKE_JOBS:-4}" core "$@"
        ;;
esac
exec "$@"
