#!/usr/bin/env bash
# Host-side integration test: the image must work without host dependencies/network.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
image=${PTX_VERIFY_IMAGE:-verifiedinfer-ptx:local}
temporary=$(mktemp -d)
build_volume=
cleanup() {
    rm -rf "$temporary"
    if [[ -n $build_volume ]]; then docker volume rm "$build_volume" >/dev/null; fi
}
trap cleanup EXIT
build_volume=$(docker volume create "ptx-verify-smoke-$$")
rsync -a --exclude=/.git --exclude=/vendor --exclude=/target \
    --exclude=/lean/.lake --exclude=__pycache__ --exclude='*.pyc' \
    "$root/" "$temporary/"
test ! -e "$temporary/vendor"
test ! -e "$temporary/lean/.lake"
run() {
    docker run --rm --network=none --user "$(id -u):$(id -g)" \
        --mount "type=bind,source=$temporary,target=/workspace" \
        --mount "type=volume,source=$build_volume,target=/opt/ptx-verify/lean/.lake/build" \
        --workdir /workspace --env PTX_VERIFY_SOURCE=/workspace "$image" "$@"
}
run translate examples/copy.ptx lean/Ptx/Generated/Copy.lean
run verify Ptx.Kernels.CopyEventWitness Ptx.CopyEvent.correct Ptx.CopyEvent.nonvacuous
# Exercise Mathlib modules beyond those prebuilt for Copy (including lazy hashes).
run verify Ptx.Kernels.ScalarMatmulWitness \
    Ptx.ScalarMatmulEvent.correct Ptx.ScalarMatmulEvent.nonvacuous
cat > "$temporary/lean/Ptx/Tests/ContainerSmoke.lean" <<'LEAN'
namespace ContainerSmoke
theorem checked : True := True.intro
end ContainerSmoke
LEAN
run verify Ptx.Tests.ContainerSmoke ContainerSmoke.checked
# Changing host proof source must invalidate any previous proof result.
cat > "$temporary/lean/Ptx/Tests/ContainerSmoke.lean" <<'LEAN'
namespace ContainerSmoke
theorem checked : False := by sorry
end ContainerSmoke
LEAN
if run verify Ptx.Tests.ContainerSmoke ContainerSmoke.checked > "$temporary/rejected.log" 2>&1; then
    echo 'ERROR: a sorry proof was accepted' >&2
    exit 1
fi
grep -F 'unproved assumptions: sorryAx' "$temporary/rejected.log"
printf '\n# changed dependencies\n' >> "$temporary/lean/lakefile.toml"
if run verify Ptx.Tests.ContainerSmoke ContainerSmoke.checked > "$temporary/rejected.log" 2>&1; then
    echo 'ERROR: changed dependencies were accepted without an image rebuild' >&2
    exit 1
fi
grep -F 'rebuild the ptx image' "$temporary/rejected.log"
echo 'Offline image smoke test passed (clean source, live edits, proof rejection, dependency guard).'
