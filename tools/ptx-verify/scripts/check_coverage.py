"""Validate coverage metadata structure, never infer proof success from metadata."""

from pathlib import Path
import tomllib

ROOT = Path(__file__).resolve().parent.parent
STATUSES = {"baseline", "partial", "planned"}


def validate(data, root=ROOT):
    if data.get("schema_version") != 1:
        raise ValueError("unsupported coverage schema")
    if data.get("exact_instruction_inventory") != "unconfirmed":
        raise ValueError("exact instruction parity requires a new evidence review")
    for group in ("capabilities", "cases"):
        entries = data.get(group, [])
        if not entries:
            raise ValueError(f"missing {group}")
        seen = set()
        for entry in entries:
            name = entry.get("id")
            if not isinstance(name, str) or not name or name in seen:
                raise ValueError(f"invalid or duplicate {group} id: {name!r}")
            seen.add(name)
            if entry.get("status") not in STATUSES:
                raise ValueError(f"{name}: invalid status")
            if not isinstance(entry.get("remaining"), str) or not entry["remaining"].strip():
                raise ValueError(f"{name}: missing remaining obligations")
            evidence = entry.get("evidence", [])
            if not isinstance(evidence, list):
                raise ValueError(f"{name}: evidence must be a list")
            if entry["status"] != "planned" and not evidence:
                raise ValueError(f"{name}: implemented work needs evidence")
            for item in evidence:
                if not isinstance(item, str):
                    raise ValueError(f"{name}: evidence path must be text")
                path = (root / item).resolve()
                if not path.is_relative_to(root.resolve()) or not path.is_file():
                    raise ValueError(f"{name}: invalid evidence path {item!r}")


def main():
    with (ROOT / "coverage.toml").open("rb") as source:
        data = tomllib.load(source)
    validate(data)
    print(
        f"Coverage inventory: {len(data['capabilities'])} capabilities, "
        f"{len(data['cases'])} cases; metadata validation only"
    )


if __name__ == "__main__":
    main()
