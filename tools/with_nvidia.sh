#!/bin/sh
# Scope compatibility libraries to this command; do not edit the system loader.
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
version=$(cat /sys/module/nvidia/version)
compat="$root/build/nvidia-compat/$version"
if [ -d "$compat" ]; then
    LD_LIBRARY_PATH="$compat${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
    export LD_LIBRARY_PATH
fi
if [ "$#" -eq 0 ]; then set -- nvidia-smi; fi
if [ "$1" = nvidia-smi ] && [ -x "$compat/nvidia-smi" ]; then
    shift
    set -- "$compat/nvidia-smi" "$@"
fi
exec "$@"
