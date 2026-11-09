#!/usr/bin/env python3
"""One-command reproducible prototype acceptance, separate from strict proof."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tomllib

from proof_audit import (AuditError, LEAN, ROOT, classify_cases, lean_metadata, validate_manifest)
from instruction_inventory import check_inventory


def source_fingerprint():
    files = [ROOT / "coverage.toml", ROOT / "prototype.toml", ROOT / "instructions.toml", ROOT / "Cargo.toml",
             LEAN / "Ptx.lean",
             LEAN / "lakefile.toml", LEAN / "lake-manifest.json", LEAN / "lean-toolchain", ROOT / "Cargo.lock"]
    for directory in ("src", "examples", "scripts", "lean/Ptx"):
        files.extend(path for path in (ROOT / directory).rglob("*")
                     if path.is_file() and "__pycache__" not in path.parts and path.suffix in {".rs", ".ptx", ".py", ".sh", ".lean"})
    digest = hashlib.sha256()
    for path in sorted(set(files)):
        digest.update(str(path.relative_to(ROOT)).encode() + b"\0" + hashlib.sha256(path.read_bytes()).digest())
    return {"sha256": digest.hexdigest(), "file_count": len(set(files))}


def run_logged(args, log):
    with log.open("w") as stream:
        result = subprocess.run(args, cwd=ROOT, text=True, stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        raise AuditError(f"Command failed ({result.returncode}); see {log}")


def audit(manifest):
    validate_manifest(manifest)
    claims = sorted({name for case in manifest["cases"] for role in ("correctness", "nonvacuity", "instances")
                     for name in case.get(role, [])} | {name for names in manifest["capability_claims"].values() for name in names})
    declarations, _ = lean_metadata(["Ptx", "Ptx.Tests"], names=claims)
    capability_groups = [{"id": key, "scope": "Listed capability claims; implementation gaps remain separately recorded",
                           "correctness": names, "nonvacuity": [], "instances": []}
                          for key, names in manifest["capability_claims"].items()]
    results = classify_cases(manifest["cases"] + capability_groups, declarations)
    return results[:len(manifest["cases"])], results[len(manifest["cases"]):]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, default=ROOT / "docs/prototype-evidence.json")
    parser.add_argument("--gpu", choices=("run", "off"), default="run",
                        help="Run fresh exact GPU checks, or explicitly record them as not run on CPU hosts")
    args = parser.parse_args(argv)
    if toolchain := os.environ.get("LEAN_TOOLCHAIN_DIR"):
        os.environ["PATH"] = str(Path(toolchain) / "bin") + os.pathsep + os.environ["PATH"]
    report_path = args.report.resolve()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report = {"schema_version": 1, "timestamp_utc": datetime.now(timezone.utc).isoformat(), "status": "failed",
              "verdict_scope": "Prototype acceptance of registered model-relative VCs; not complete formal verification or hardware IEEE equivalence",
              "cases": [], "gpu": {"status": "not_run"}}
    try:
        before = source_fingerprint()
        manifest = tomllib.loads((ROOT / "prototype.toml").read_text())
        validate_manifest(manifest)
        run_logged([sys.executable, "-m", "unittest", "discover", "-s", "scripts", "-p", "test_proof_audit.py"],
                   report_path.with_suffix(".audit-tests.log"))
        run_logged([sys.executable, "-m", "unittest", "discover", "-s", "scripts", "-p", "test_instruction_inventory.py"],
                   report_path.with_suffix(".inventory-tests.log"))
        strict_log = report_path.with_suffix(".strict.log")
        print(f"Running unchanged strict gate; log: {strict_log}", flush=True)
        run_logged(["bash", "scripts/check.sh"], strict_log)
        report["strict_gate"] = {"status": "passed", "log": str(strict_log),
                                 "sha256": hashlib.sha256(strict_log.read_bytes()).hexdigest()}
        strict_text = strict_log.read_text()
        assembly = ROOT / "docs/assembly-evidence.json"
        if "PTX assembly:" in strict_text:
            evidence = json.loads(assembly.read_text())
            if evidence.get("status") != "passed" or any(
                hashlib.sha256((ROOT / "examples" / f"{name}.ptx").read_bytes()).hexdigest() != value
                for name, value in evidence.get("fixtures", {}).items()
            ) or not evidence.get("fixtures"):
                raise AuditError("Assembly evidence is missing or stale")
            report["assembly"] = {"status": "passed", "timestamp_utc": evidence["timestamp_utc"],
                                   "fixtures": len(evidence["fixtures"])}
        else:
            report["assembly"] = {"status": "not_run", "reason": "No assembler in the strict gate; set PTXAS"}
        report["cases"], capability_results = audit(manifest)
        coverage = tomllib.loads((ROOT / "coverage.toml").read_text())
        by_id = {entry["id"]: entry for entry in capability_results}
        report["capabilities"] = [{**entry, "registered_claims": by_id[entry["id"]]} for entry in coverage["capabilities"]]
        case_coverage = {entry["id"]: entry["status"] for entry in coverage["cases"]}
        for case in report["cases"]:
            case["coverage_status"] = case_coverage[case["id"]]
        report["instruction_inventory"] = {**check_inventory(), "exact_parity": coverage["exact_instruction_inventory"],
                                            "source": "instructions.toml", "note": "No unsupported paper form is counted as implemented"}
        if args.gpu == "run":
            gpu_path = report_path.with_suffix(".gpu.json")
            run_logged(["bash", "scripts/check_gpu.sh", "--report", str(gpu_path)], report_path.with_suffix(".gpu.log"))
            gpu = json.loads(gpu_path.read_text())
            if gpu.get("status") != "passed":
                raise AuditError("GPU command did not produce passing evidence")
            if not gpu.get("source_sha256") or any(
                hashlib.sha256((ROOT / "examples" / f"{name}.ptx").read_bytes()).hexdigest() != value
                for name, value in gpu["source_sha256"].items()
            ):
                raise AuditError("GPU report source hashes are missing or stale")
            report["gpu"] = {"status": "passed", "report": str(gpu_path), "timestamp_utc": gpu["timestamp_utc"],
                             "cases": len(gpu["cases"]), "scope": gpu["scope"]}
        else:
            report["gpu"] = {"status": "not_run", "reason": "Explicit --gpu off; no new hardware evidence"}
        after = source_fingerprint()
        if before != after:
            raise AuditError("Sources changed during acceptance; rerun against a stable worktree")
        report["source_fingerprint"] = after
        gaps = any(case["status"] == "unsupported" for case in report["cases"]) or any(
            entry["status"] != "baseline" for entry in report["capabilities"])
        report["status"] = "prototype-passed-with-gaps" if gaps else "prototype-passed"
        report["limits"] = ["Strict proof labels apply only to the listed theorem statements and declared scopes",
                            "Temporary sorry and extra unproved assumptions cannot pass strict acceptance",
                            "Prototype acceptance does not close compiler/runtime/allocation, full PTX ISA or universal IEEE/logits/token correspondence"]
    except (AuditError, OSError, ValueError, subprocess.SubprocessError) as error:
        report["error"] = str(error)
        print(f"Prototype acceptance failed: {error}", file=sys.stderr)
    finally:
        report_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(f"{report['status']}: {report_path}")
    return 0 if report["status"].startswith("prototype-passed") else 1


if __name__ == "__main__":
    raise SystemExit(main())
