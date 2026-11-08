#!/usr/bin/env python3
"""Check named Lean proof theorems without translating or running other cases."""

import argparse
import subprocess
import sys

from prototype_audit import AuditError, BASE_AXIOMS, LEAN, lean_metadata, valid_name


def check_theorems(declarations, names):
    for name in names:
        declaration = declarations[name]
        if declaration["kind"] != "theorem" or not declaration["is_prop"]:
            raise AuditError(f"{name} is not a proof theorem; generated program data is not a correctness proof")
        extra = set(declaration["axioms"]) - BASE_AXIOMS
        if extra:
            raise AuditError(f"{name} depends on unproved assumptions: {', '.join(sorted(extra))}")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module", type=valid_name, help="Lean contract module, e.g. Ptx.Kernels.Copy")
    parser.add_argument("theorems", nargs="+", type=valid_name, help="proof theorem names to check")
    args = parser.parse_args(argv)
    try:
        print(f"Checking {args.module}", flush=True)
        build = subprocess.run(["lake", "build", args.module, "PtxPrototype.Audit"], cwd=LEAN,
                               text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if build.returncode:
            sys.stderr.write(build.stdout)
            raise AuditError("Lean module build failed")
        declarations, _ = lean_metadata([args.module], names=args.theorems)
        check_theorems(declarations, args.theorems)
        for name in args.theorems:
            print(f"Verified theorem (strict): {name}\n{declarations[name]['statement']}")
        return 0
    except (AuditError, FileNotFoundError) as error:
        print(f"Verification failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
