#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if [[ ${1:-} == --help || ${1:-} == -h ]]; then
    echo "Usage: bash scripts/translate.sh INPUT.ptx OUTPUT.lean"
    exit 0
fi
if [[ $# != 2 ]]; then
    echo "Usage: bash scripts/translate.sh INPUT.ptx OUTPUT.lean" >&2
    exit 2
fi
exec cargo run --quiet --locked --manifest-path "$ROOT/Cargo.toml" -- "$@"
