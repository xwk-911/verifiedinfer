"""Fail-closed Lean metadata and named-assumption audit for prototype acceptance.

The strict checker is independent. This module never treats a failed Lean
process, an unregistered axiom, or a changed VC type as successful acceptance.
Structural guards catch direct/definition/structure VC wrappers; arbitrary
semantic equivalence and axiom consistency still require statement review.
"""

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
VC_HEADS = frozenset({"Triple", "CheckedTriple", "Safe", "Nonvacuous", "CheckedNonvacuous",
                      "WellFormed", "Complete", "MemoryConditions", "GenericMemoryConditions",
                      "ObserverConditions", "Post", "RegisterPost"})
ROLES = frozenset({"arithmetic", "indexing", "collections", "encoding", "local_semantic_interface"})


class AuditError(ValueError):
    pass


def valid_name(name):
    if not isinstance(name, str) or not NAME.fullmatch(name):
        raise AuditError(f"Invalid Lean name: {name!r}")
    return name


def digest_type(declaration):
    return hashlib.sha256(declaration["type_repr"].encode()).hexdigest()


def lean_metadata(imports, names=(), comparisons=(), cwd=LEAN, source_before_audit="", auxiliary_type_checks=()):
    """Read kernel-checked declarations and their transitive axiom dependencies."""
    imports = [valid_name(name) for name in imports]
    names = list(dict.fromkeys(valid_name(name) for name in names))
    comparisons = [(valid_name(a), valid_name(b)) for a, b in comparisons]
    auxiliary_type_checks = [(valid_name(a), valid_name(b)) for a, b in auxiliary_type_checks]
    if len(auxiliary_type_checks) != len(set(auxiliary_type_checks)):
        raise AuditError("Duplicate protected-type check")
    requested = names + [a for a, _ in comparisons]
    if len(requested) != len(set(requested)):
        raise AuditError("Duplicate declaration audit request")
    source = "\n".join(f"import {name}" for name in imports) + "\nimport PtxPrototype.Audit\n"
    source += source_before_audit + "\n"
    source += "\n".join(f"prototype_decl {name}" for name in names) + "\n"
    source += "\n".join(f"prototype_vc {a} against {b}" for a, b in comparisons) + "\n"
    source += "\n".join(f"prototype_aux_guard {a} against {b}" for a, b in auxiliary_type_checks) + "\nprototype_inventory\n"
    with tempfile.TemporaryDirectory(prefix="ptx-prototype-") as temporary:
        path = Path(temporary) / "Audit.lean"
        path.write_text(source)
        result = subprocess.run(["lake", "env", "lean", "--json", str(path)], cwd=cwd,
                                text=True, capture_output=True, timeout=300)
    if result.returncode or result.stderr.strip():
        raise AuditError(f"Lean metadata audit failed:\n{result.stdout}\n{result.stderr}")
    declarations, inventory, type_checks = {}, None, {}
    for line in result.stdout.splitlines():
        try:
            diagnostic = json.loads(line)
        except json.JSONDecodeError as error:
            raise AuditError(f"Unexpected Lean output: {line}") from error
        if diagnostic.get("severity") == "error":
            raise AuditError(f"Lean audit diagnostic: {diagnostic}")
        data = diagnostic.get("data", "")
        if data.startswith("PTX_PROTOTYPE_DECL "):
            entry = json.loads(data.removeprefix("PTX_PROTOTYPE_DECL "))
            if entry["name"] in declarations or entry["name"] not in requested:
                raise AuditError(f"Duplicate/unrequested declaration: {entry['name']}")
            declarations[entry["name"]] = entry
        elif data.startswith("PTX_PROTOTYPE_AXIOMS "):
            if inventory is not None:
                raise AuditError("Duplicate axiom inventory")
            inventory = set(json.loads(data.removeprefix("PTX_PROTOTYPE_AXIOMS ")))
        elif data.startswith("PTX_PROTOTYPE_AUX_TYPE "):
            entry = json.loads(data.removeprefix("PTX_PROTOTYPE_AUX_TYPE "))
            pair = (entry["assumption"], entry["reference"])
            if pair in type_checks or pair not in auxiliary_type_checks:
                raise AuditError(f"Duplicate/unrequested protected-type check: {pair}")
            type_checks[pair] = entry["same_type"]
    if inventory is None or declarations.keys() != set(requested):
        raise AuditError(f"Incomplete Lean audit: missing {set(requested)-declarations.keys()}")
    if type_checks.keys() != set(auxiliary_type_checks):
        raise AuditError("Missing protected-type comparison")
    for name, declaration in declarations.items():
        declaration["checked_protected_types"] = sorted(b for a, b in type_checks if a == name)
        declaration["matches_protected_types"] = sorted(b for (a, b), same in type_checks.items() if a == name and same)
    return declarations, inventory


def validate_manifest(manifest):
    if manifest.get("schema_version") != 1:
        raise AuditError("Unsupported prototype manifest version")
    cases = manifest.get("cases", [])
    ids = [case.get("id") for case in cases]
    if len(ids) != len(set(ids)) or set(ids) != CASE_IDS:
        raise AuditError("Prototype acceptance must retain all seven original case groups")
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
    for name in manifest.get("imports", []):
        valid_name(name)
    capability_claims = manifest.get("capability_claims", {})
    if set(capability_claims) != CAPABILITY_IDS:
        raise AuditError("Prototype acceptance must retain all twelve capability groups")
    for names in capability_claims.values():
        if not isinstance(names, list) or not names:
            raise AuditError("Capability groups require explicit checked claims")
        for name in names:
            valid_name(name)
    assumptions = manifest.get("assumptions", [])
    names = [entry.get("name") for entry in assumptions]
    if len(names) != len(set(names)):
        raise AuditError("Duplicate registered assumption")
    claims = {name for case in cases for role in ("correctness", "nonvacuity", "instances")
              for name in case.get(role, [])}
    claims.update(name for names in capability_claims.values() for name in names)
    overrides = manifest.get("overrides", {})
    if not isinstance(overrides, dict) or not overrides.keys() <= claims:
        raise AuditError("Prototype overrides must name registered reference VCs")
    for reference, target in overrides.items():
        valid_name(reference)
        valid_name(target)
        if not target.startswith("PtxPrototype."):
            raise AuditError(f"Alternate proofs must stay outside the strict library: {target}")
    targets = [overrides.get(name, name) for name in claims]
    if len(targets) != len(set(targets)):
        raise AuditError("Each reference VC requires a distinct audited proof declaration")
    for entry in assumptions:
        name = valid_name(entry.get("name"))
        if not name.startswith("PtxPrototype.Assumptions."):
            raise AuditError(f"Assumption outside designated namespace: {name}")
        if name in claims:
            raise AuditError(f"A top-level VC cannot be an assumption: {name}")
        if entry.get("role") not in ROLES:
            raise AuditError(f"Unsupported auxiliary role: {name}")
        for field in ("statement", "purpose", "review", "discharge_task"):
            if not isinstance(entry.get(field), str) or not entry[field].strip():
                raise AuditError(f"Missing {field}: {name}")
        if not re.fullmatch(r"[a-f0-9]{64}", entry.get("type_sha256", "")):
            raise AuditError(f"Missing exact checked type fingerprint: {name}")
        affected = entry.get("affected_vcs")
        if not isinstance(affected, list) or len(affected) != len(set(affected)) or not set(affected) <= claims:
            raise AuditError(f"Invalid affected VC inventory: {name}")


def forbidden_assumption_dependencies(declaration, protected):
    forbidden = set()
    for name in declaration["type_dependencies"]:
        leaf = name.rsplit(".", 1)[-1]
        if (name in protected or name == "False"
                or name.startswith("Ptx.") and leaf in VC_HEADS
                or name.startswith("Ptx.Generated.") and leaf in {"program", "checked"}):
            forbidden.add(name)
    return sorted(forbidden)


def audit_registered_assumptions(registry, declarations, extra_axioms, protected):
    registered = {entry["name"]: entry for entry in registry}
    if set(registered) != set(extra_axioms):
        raise AuditError(f"Additional axioms differ from registry: unregistered={set(extra_axioms)-registered.keys()}, "
                         f"unloaded={registered.keys()-set(extra_axioms)}")
    for name, entry in registered.items():
        declaration = declarations[name]
        if declaration["kind"] != "axiom" or not declaration["is_prop"]:
            raise AuditError(f"Registered auxiliary must be a named proposition axiom: {name}")
        if declaration["statement"] != entry["statement"] or digest_type(declaration) != entry["type_sha256"]:
            raise AuditError(f"Registered statement/type changed: {name}")
        if set(declaration["checked_protected_types"]) != set(protected):
            raise AuditError(f"Incomplete protected VC type comparisons: {name}")
        if declaration["matches_protected_types"]:
            raise AuditError(f"Auxiliary assumption has a top-level VC type: {name}: {declaration['matches_protected_types']}")
        if forbidden := forbidden_assumption_dependencies(declaration, protected):
            raise AuditError(f"Auxiliary assumption wraps a VC/protected obligation: {name}: {forbidden}")
        if used := set(declaration["axioms"]) - BASE_AXIOMS - registered.keys():
            raise AuditError(f"Assumption depends on unregistered axioms: {name}: {used}")


def classify_cases(cases, declarations, registry):
    registered = {entry["name"] for entry in registry}
    impacted = {name: set() for name in registered}
    results = []
    for case in cases:
        if case.get("unsupported", False):
            results.append({"id": case["id"], "status": "unsupported", "reason": case["reason"], "scope": case["scope"]})
            continue
        vcs, assumptions = [], set()
        for role in ("correctness", "nonvacuity", "instances"):
            for name in case[role]:
                declaration = declarations[name]
                if declaration["kind"] != "theorem" or not declaration["is_prop"]:
                    raise AuditError(f"VC must be proved as a theorem: {name}")
                if not declaration["matches_reference"]:
                    raise AuditError(f"VC statement changed: {name}")
                used = set(declaration["axioms"]) - BASE_AXIOMS
                if unknown := used - registered:
                    raise AuditError(f"VC has unregistered/anonymous axiom dependencies: {name}: {unknown}")
                for assumption in used:
                    impacted[assumption].add(name)
                assumptions.update(used)
                vcs.append({"name": declaration["name"], "reference": name, "role": role, "statement": declaration["statement"],
                            "type_sha256": digest_type(declaration), "assumptions": sorted(used)})
        results.append({"id": case["id"], "status": "conditional-proof" if assumptions else "strict-proof",
                        "scope": case["scope"], "assumptions": sorted(assumptions), "vcs": vcs})
    for entry in registry:
        if impacted[entry["name"]] != set(entry["affected_vcs"]):
            raise AuditError(f"Affected VC list differs from actual transitive dependencies: {entry['name']}")
    return results
