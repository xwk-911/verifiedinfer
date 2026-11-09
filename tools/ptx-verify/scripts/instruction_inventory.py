"""Check fixed opcode spellings with actual translation and Lean typing.

This is an inventory of this frontend, not an inferred reconstruction of the
paper's unpublished per-form inventory or a proof of instruction semantics.
"""

import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
import tomllib

from proof_audit import AuditError, LEAN, ROOT


def parser_spellings(source):
    marker = "let instr = match op.as_str() {"
    if source.count(marker) != 1:
        raise AuditError("Instruction dispatch changed; review inventory extraction")
    tokens = re.findall(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|=>|[^\s]',
                        source.split(marker)[1], re.S)
    depth, names = 1, []
    for index, token in enumerate(tokens):
        if token.startswith(("//", "/*")):
            continue
        if token == "{":
            depth += 1
        elif token == "}":
            depth -= 1
            if depth == 0:
                break
        elif depth == 1 and token.startswith('"'):
            following = index + 1
            while following + 1 < len(tokens) and tokens[following] == "|" and tokens[following+1].startswith('"'):
                following += 2
            if following < len(tokens) and tokens[following] == "=>":
                names.append(json.loads(token))
    else:
        raise AuditError("Unterminated instruction dispatch")
    if not names or len(names) != len(set(names)):
        raise AuditError("Empty/duplicate opcode dispatch inventory")
    return set(names)


def validate_inventory(data, source, root=ROOT):
    if data.get("schema_version") != 1:
        raise AuditError("Unsupported instruction inventory schema")
    paper = data.get("paper", {})
    if (paper.get("mapping_status") != "unconfirmed" or paper.get("forms") != 81
            or paper.get("groups") != {"scalar_control_memory": 66, "ampere": 5, "hopper": 10}
            or not paper.get("gap")):
        raise AuditError("Paper parity requires explicit new source/evidence review")
    profiles = data.get("profiles", {})
    forms = data.get("forms", [])
    names = [entry.get("opcode") for entry in forms]
    if len(names) != len(set(names)) or set(names) != parser_spellings(source):
        raise AuditError("Instruction registry differs from actual parser dispatch spellings")
    for entry in forms:
        if entry.get("profile") not in profiles or entry.get("canonical") not in names:
            raise AuditError(f"Unknown profile/canonical form: {entry['opcode']}")
        if entry.get("paper_mapping") != "unconfirmed":
            raise AuditError(f"Unreviewed paper form correspondence: {entry['opcode']}")
        for key in ("instruction", "limits", "semantics", "regression"):
            if not isinstance(entry.get(key), str) or not entry[key].strip():
                raise AuditError(f"Missing {key}: {entry['opcode']}")
        if not re.match(re.escape(entry["opcode"]) + r"(?=\s|;)", entry["instruction"]):
            raise AuditError(f"Probe does not exercise declared opcode: {entry['opcode']}")
        path = (root / entry["semantics"]).resolve()
        if not path.is_relative_to(root.resolve()) or not path.is_file():
            raise AuditError(f"Missing semantics evidence: {entry['opcode']}")
        if f"fn {entry['regression']}(" not in source:
            raise AuditError(f"Missing Rust regression: {entry['opcode']}")
    by_name = {entry["opcode"]: entry for entry in forms}
    for entry in forms:
        canonical = by_name[entry["canonical"]]
        if canonical["canonical"] != canonical["opcode"]:
            raise AuditError("Canonical aliases must resolve directly to a canonical form")


def probe_source(entry, profile, index, negative=False):
    instruction = entry["instruction"]
    if negative:
        instruction = instruction.replace(entry["opcode"], entry["opcode"] + ".ptx_verify_unmodeled", 1)
    return (f".version {profile['version']}\n.target {profile['target']}\n.address_size 64\n"
            f".visible .entry inventory_{index}(.param .u32 X,.param .u64 P) {{\n"
            + profile["declarations"] + "\n" + instruction + "\nEND: ret;\n}\n")


def check_inventory():
    manifest_path = ROOT / "instructions.toml"
    data = tomllib.loads(manifest_path.read_text())
    source = (ROOT / "src/parser.rs").read_text()
    validate_inventory(data, source)
    # Locate the real cargo artifact, including configured target directories.
    build = subprocess.run(["cargo", "build", "--locked", "--message-format=json"], cwd=ROOT,
                           text=True, capture_output=True, timeout=300)
    if build.returncode:
        raise AuditError(f"Instruction probe translator build failed: {build.stderr}")
    executables = [item["executable"] for line in build.stdout.splitlines()
                   if (item := json.loads(line)).get("reason") == "compiler-artifact"
                   and item.get("target", {}).get("name") == "ptx-verify" and item.get("executable")]
    if len(executables) != 1:
        raise AuditError("Missing/ambiguous translator executable")
    entries, generated, imports = [], [], set()
    with tempfile.TemporaryDirectory(prefix="ptx-inventory-") as temporary:
        directory = Path(temporary)
        for index, entry in enumerate(data["forms"]):
            profile = data["profiles"][entry["profile"]]
            ptx, lean = directory / f"{index}.ptx", directory / f"{index}.lean"
            positive = probe_source(entry, profile, index)
            ptx.write_text(positive)
            translated = subprocess.run([executables[0], str(ptx), str(lean)], text=True, capture_output=True, timeout=30)
            if translated.returncode or not lean.is_file():
                raise AuditError(f"Accepted-form probe failed: {entry['opcode']}: {translated.stderr}")
            emitted = lean.read_text()
            for line in emitted.splitlines():
                if line.startswith("import "):
                    imports.add(line)
            generated.append("\n".join(line for line in emitted.splitlines() if not line.startswith("import ")))
            lean.unlink()
            negative = probe_source(entry, profile, index, negative=True)
            ptx.write_text(negative)
            rejected = subprocess.run([executables[0], str(ptx), str(lean)], text=True, capture_output=True, timeout=30)
            if rejected.returncode != 2 or "unsupported instruction" not in rejected.stderr or lean.exists():
                raise AuditError(f"Unknown-qualifier rejection failed: {entry['opcode']}: {rejected.stderr}")
            entries.append({**entry, "translation": "passed", "generated_typing": "pending",
                            "unknown_qualifier_rejection": "passed",
                            "positive_ptx_sha256": hashlib.sha256(positive.encode()).hexdigest(),
                            "negative_ptx_sha256": hashlib.sha256(negative.encode()).hexdigest(),
                            "generated_lean_sha256": hashlib.sha256(emitted.encode()).hexdigest()})
        joined = directory / "Inventory.lean"
        joined.write_text("\n".join(sorted(imports)) + "\n" + "\n".join(generated))
        checked = subprocess.run(["lake", "env", "lean", "--json", str(joined)], cwd=LEAN,
                                 text=True, capture_output=True, timeout=300)
        if checked.returncode or checked.stderr.strip():
            raise AuditError(f"Generated instruction typing failed: {checked.stdout}\n{checked.stderr}")
        for line in checked.stdout.splitlines():
            if json.loads(line).get("severity") == "error":
                raise AuditError(f"Generated instruction typing diagnostic: {line}")
    for entry in entries:
        entry["generated_typing"] = "passed"
    return {"paper": data["paper"], "local_spelling_count": len(entries),
            "local_canonical_count": len({entry['canonical'] for entry in entries}),
            "scope": "Finite frontend acceptance/rejection and generated typing; not per-op semantic correctness or paper parity",
            "manifest_sha256": hashlib.sha256(manifest_path.read_bytes()).hexdigest(), "forms": entries}
