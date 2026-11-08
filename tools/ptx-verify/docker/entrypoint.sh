#!/usr/bin/env bash
set -euo pipefail
tool=/opt/ptx-verify
source_root=${PTX_VERIFY_SOURCE:-$tool}
if [[ $source_root != "$tool" ]]; then
    # Keep image dependencies visible when the user's repository is bind-mounted.
    # Dependency changes require an image rebuild; startup never fetches packages.
    for lock in lean/lean-toolchain lean/lakefile.toml lean/lake-manifest.json; do
        if ! cmp -s "$source_root/$lock" "$tool/$lock"; then
            echo "PTX dependency configuration changed ($lock); rebuild the ptx image." >&2
            exit 2
        fi
    done
    rsync -rl --checksum --delete --no-perms \
        --exclude=/.git --exclude=/vendor --exclude=/target \
        --exclude=/lean/.lake --exclude=__pycache__ --exclude='*.pyc' \
        --exclude='*.olean' --exclude='*.ilean' --exclude='*.trace' \
        --exclude='/docs/*.log' "$source_root/" "$tool/"
fi
export CARGO_HOME=/tmp/ptx-cargo
export XDG_CACHE_HOME=/tmp/ptx-cache
export GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=safe.directory GIT_CONFIG_VALUE_0='*'
case "${1:-help}" in
    translate) shift; exec bash "$tool/scripts/translate.sh" "$@" ;;
    verify) shift; exec bash "$tool/scripts/verify.sh" "$@" ;;
    check) shift; cd "$tool"; exec bash scripts/check.sh "$@" ;;
    help|--help|-h)
        echo 'translate INPUT.ptx OUTPUT.lean   Translate PTX to Lean program data'
        echo 'verify MODULE THEOREM...          Check supplied Lean proofs and assumptions'
        echo 'Other commands run in the image tool directory (e.g. bash).'
        ;;
    *) cd "$tool"; exec "$@" ;;
esac
