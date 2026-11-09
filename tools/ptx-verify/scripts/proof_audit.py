"""Read actual Lean declaration metadata and reject unfinished proof dependencies."""

import hashlib
import json
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"
BASE_AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z")
CASE_IDS = frozenset({"copy-shared-swap", "scalar-matmul", "atomic-dispatch", "online-flash-attention",
                      "three-kernel-moe", "ampere-tiled-matmul", "hopper-double-buffer-gemm"})
CAPABILITY_IDS = frozenset({"legacy-operational-subset", "typed-ast-and-launch", "oracle-event-execution",
                            "ptx-memory-model", "synchronized-global-observation", "legacy-event-refinement",
                            "atomics-and-shuffle", "real-float-semantics", "ampere-copy-and-mma",
                            "hopper-tma-mbarrier-wgmma", "sequential-kernel-composition", "iris-runtime-event-connection"})


class AuditError(ValueError):
    pass


def valid_name(name):
    if not isinstance(name, str) or not NAME.fullmatch(name):
        raise AuditError(f"Invalid Lean name: {name!r}")
    return name


def digest_type(declaration):
    return hashlib.sha256(declaration["type_repr"].encode()).hexdigest()


def lean_metadata(imports, names=(), cwd=LEAN, source_before_audit=""):
    """Elaborate the audit tooling with Lean and collect transitive axioms."""
    imports = [valid_name(name) for name in imports]
    names = list(dict.fromkeys(valid_name(name) for name in names))
    source = "\n".join(f"import {name}" for name in imports) + "\n"
    source += (ROOT / "scripts/proof_audit.lean").read_text() + "\n"
    source += source_before_audit + "\n"
    source += "\n".join(f"proof_decl {name}" for name in names) + "\nproof_inventory\n"
    with tempfile.TemporaryDirectory(prefix="ptx-proof-") as temporary:
        path = Path(temporary) / "Audit.lean"
        path.write_text(source)
        result = subprocess.run(["lake", "env", "lean", "--json", str(path)], cwd=cwd,
                                text=True, capture_output=True, timeout=300)
    if result.returncode or result.stderr.strip():
        raise AuditError(f"Lean metadata audit failed:\n{result.stdout}\n{result.stderr}")
    declarations, inventory = {}, None
    for line in result.stdout.splitlines():
        try:
            diagnostic = json.loads(line)
        except json.JSONDecodeError as error:
            raise AuditError(f"Unexpected Lean output: {line}") from error
        if diagnostic.get("severity") == "error":
            raise AuditError(f"Lean audit diagnostic: {diagnostic}")
        data = diagnostic.get("data", "")
        if data.startswith("PTX_PROOF_DECL "):
            entry = json.loads(data.removeprefix("PTX_PROOF_DECL "))
            if entry["name"] in declarations or entry["name"] not in names:
                raise AuditError(f"Duplicate/unrequested declaration: {entry['name']}")
            declarations[entry["name"]] = entry
        elif data.startswith("PTX_PROOF_AXIOMS "):
            if inventory is not None:
                raise AuditError("Duplicate axiom inventory")
            inventory = set(json.loads(data.removeprefix("PTX_PROOF_AXIOMS ")))
    if inventory is None or declarations.keys() != set(names):
        raise AuditError(f"Incomplete Lean audit: missing {set(names)-declarations.keys()}")
    return declarations, inventory


def validate_manifest(manifest):
    if manifest.get("schema_version") != 1:
        raise AuditError("Unsupported acceptance manifest version")
    if {"assumptions", "overrides", "imports"} & manifest.keys():
        raise AuditError("Assumption registries and alternate proofs are no longer supported")
    cases = manifest.get("cases", [])
    ids = [case.get("id") for case in cases]
    if len(ids) != len(set(ids)) or set(ids) != CASE_IDS:
        raise AuditError("Acceptance must retain all seven original case groups")
    for case in cases:
        if not isinstance(case.get("scope"), str) or not case["scope"].strip():
            raise AuditError(f"Missing case scope: {case['id']}")
        if not isinstance(case.get("unsupported", False), bool):
            raise AuditError(f"Unsupported status must be an explicit Boolean: {case['id']}")
        if case.get("unsupported", False):
            if not case.get("reason"):
                raise AuditError(f"Unsupported case needs a reason: {case['id']}")
            continue
        for role in ("correctness", "nonvacuity", "instances"):
            if not isinstance(case.get(role), list) or not case[role]:
                raise AuditError(f"Missing {role} VCs: {case['id']}")
            for name in case[role]:
                valid_name(name)
    capability_claims = manifest.get("capability_claims", {})
    if set(capability_claims) != CAPABILITY_IDS:
        raise AuditError("Acceptance must retain all twelve capability groups")
    for names in capability_claims.values():
        if not isinstance(names, list) or not names:
            raise AuditError("Capability groups require explicit checked claims")
        for name in names:
            valid_name(name)

def classify_cases(cases, declarations):
    results = []
    for case in cases:
        if case.get("unsupported", False):
            results.append({"id": case["id"], "status": "unsupported", "reason": case["reason"], "scope": case["scope"]})
            continue
        vcs = []
        for role in ("correctness", "nonvacuity", "instances"):
            for name in case[role]:
                declaration = declarations[name]
                if declaration["kind"] != "theorem" or not declaration["is_prop"]:
                    raise AuditError(f"VC must be proved as a theorem: {name}")
                if used := set(declaration["axioms"]) - BASE_AXIOMS:
                    raise AuditError(f"VC has unproved assumptions: {name}: {sorted(used)}")
                vcs.append({"name": name, "reference": name, "role": role, "statement": declaration["statement"],
                            "type_sha256": digest_type(declaration), "assumptions": []})
        results.append({"id": case["id"], "status": "strict-proof", "scope": case["scope"],
                        "assumptions": [], "vcs": vcs})
    return results
