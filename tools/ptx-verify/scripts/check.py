"""Run frontend, Lean, and rejection checks for the verifier examples."""

import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"
CASES = {
    "copy": "Copy",
    "shared_swap": "SharedSwap",
    "loop": "Loop",
    "missing_sync": "MissingSync",
    "out_of_bounds": "OutOfBounds",
}
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
NEGATIVE_CASES = {
    "out_of_bounds": (
        "run Generated.out_of_bounds.program (List.replicate 11 (.thread 0)) copyInitial"
    ),
    "missing_barrier": (
        "run Generated.missing_sync.program missingSyncSchedule sharedInitial"
    ),
    "early_reclaim": "earlyReclaim",
    "partial_barrier": "SharedInstances.partialArrival.bind release",
    "stale_event_reclaim": (
        "Async.run (Async.initial 1 [42]) "
        "[.use 0 0,.record 0 9,.device 0,.acquire 9,.use 0 0,.acquire 9,.reclaim 0]"
    ),
    "remaining_reader_reclaim": (
        "Async.run (Async.initial 2 [42]) "
        "[.use 0 0,.use 1 0,.record 0 7,.device 0,.acquire 7,.reclaim 0]"
    ),
    "host_write_inflight": "Async.run (Async.initial 1 [42]) [.use 0 0,.write 0 99]",
}


def run(args, cwd=ROOT):
    return subprocess.run(args, cwd=cwd, text=True, check=True)


def check_generated(directory):
    for name, module in CASES.items():
        output = directory / f"{module}.lean"
        run([
            "cargo", "run", "--quiet", "--locked", "--",
            f"examples/{name}.ptx", str(output),
        ])
        expected = LEAN / "Ptx" / "Generated" / f"{module}.lean"
        if output.read_bytes() != expected.read_bytes():
            raise SystemExit(f"Stale generated AST: {expected}; regenerate and review it")


def check_proofs():
    # Scan project sources; public theorem dependencies are audited separately.
    for source in (LEAN / "Ptx").rglob("*.lean"):
        code = re.sub(r"/-.*?-/|--[^\n]*", "", source.read_text(), flags=re.S)
        if re.search(r"\bsorry\b|^\s*(axiom|constant|unsafe|partial)\b", code, flags=re.M):
            raise SystemExit(f"Untrusted proof construct in {source}")

    run(["lake", "build", "Ptx", "Ptx.Tests"], LEAN)
    audit = subprocess.run(
        ["lake", "env", "lean", "Ptx/Tests/Audit.lean"],
        cwd=LEAN, text=True, capture_output=True,
    )
    if audit.returncode:
        raise SystemExit(f"Lean audit failed:\n{audit.stdout}\n{audit.stderr}")
    for names in re.findall(r"depends on axioms: \[([^\]]*)\]", audit.stdout):
        used = {name.strip() for name in names.split(",") if name.strip()}
        if used - ALLOWED_AXIOMS:
            raise SystemExit(f"Unapproved axiom: {used - ALLOWED_AXIOMS}")
    declarations = sum(line.startswith("'") for line in audit.stdout.splitlines())
    print(f"Lean audit: {declarations} declarations checked")


def check_rejections(directory):
    imports = "\n".join([
        "import Ptx.Tests.Kernels",
        "import Ptx.Tests.SharedSwap",
        "import Ptx.Async.Contracts",
        "open Ptx Ptx.Examples",
    ])
    for name, expression in NEGATIVE_CASES.items():
        path = directory / f"Reject_{name}.lean"
        path.write_text(
            f"{imports}\n"
            f"example : ({expression}).toOption.isSome = true := by decide\n"
        )
        result = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=LEAN, text=True, capture_output=True,
        )
        # A negative must be refuted, rather than fail to parse or import.
        if not result.returncode or "Tactic `decide` proved that the proposition" not in result.stdout:
            raise SystemExit(
                f"Wrong rejection result for {name}:\n{result.stdout}\n{result.stderr}"
            )
        print(f"Rejected by Lean: {name}")


def check_ptx(directory):
    ptxas = os.environ.get("PTXAS") or shutil.which("ptxas")
    if not ptxas:
        print("Skipping PTX assembly; set PTXAS to enable it")
        return
    for name in CASES:
        run([
            ptxas, "-arch=sm_70", str(ROOT / f"examples/{name}.ptx"),
            "-o", str(directory / f"{name}.cubin"),
        ])
    print(f"PTX assembly: {len(CASES)} examples accepted")


def main():
    with tempfile.TemporaryDirectory(prefix="ptx-verify-") as temporary:
        directory = Path(temporary)
        check_generated(directory)
        check_proofs()
        check_rejections(directory)
        check_ptx(directory)
    print("All verifier checks passed")


if __name__ == "__main__":
    main()
