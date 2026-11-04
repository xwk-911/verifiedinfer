"""Generate clangd's compilation database from this project's Make dry run."""

import argparse
import json
from pathlib import Path
import shlex
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "make", nargs=argparse.REMAINDER,
        help="Make command and configuration arguments (default: make)",
    )
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    result = subprocess.run(
        [*(args.make or ["make"]), "--no-print-directory", "-B", "-n", "all", "test"],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    )
    entries = {}
    for line in result.stdout.splitlines():
        arguments = shlex.split(line)
        if "-c" not in arguments or "-o" not in arguments:
            continue
        source = arguments[arguments.index("-c") + 1]
        if not source.endswith(".c"):
            continue
        entries[source] = {
            "directory": str(root),
            "file": source,
            "arguments": arguments,
        }
    if not entries:
        raise SystemExit("No C compile commands found in the Make dry run")

    output = root / "compile_commands.json"
    temporary = output.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(list(entries.values()), indent=2) + "\n")
    temporary.replace(output)
    print(f"Wrote {output.name} ({len(entries)} source files)")


if __name__ == "__main__":
    main()
