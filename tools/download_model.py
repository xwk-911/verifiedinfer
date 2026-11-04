"""Download an HF checkpoint at a resolved revision and record file hashes."""

import argparse
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", default="HuggingFaceTB/SmolLM2-135M-Instruct")
    parser.add_argument("--revision")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    from huggingface_hub import model_info, snapshot_download

    revision = model_info(args.repo, revision=args.revision).sha
    output = args.output or Path("models") / args.repo.split("/")[-1]
    snapshot_download(
        args.repo,
        revision=revision,
        local_dir=output,
        allow_patterns=[
            "config.json", "generation_config.json", "model*.safetensors",
            "model*.index.json", "tokenizer*", "special_tokens_map.json",
            "added_tokens.json", "vocab.json", "merges.txt", "chat_template*",
            "LICENSE*",
        ],
    )
    files = {}
    for path in sorted(output.iterdir()):
        if path.is_file() and path.name != "verifiedinfer-manifest.json":
            with path.open("rb") as stream:
                digest = hashlib.file_digest(stream, "sha256").hexdigest()
            files[path.name] = {"bytes": path.stat().st_size, "sha256": digest}
    manifest = {"repository": args.repo, "revision": revision, "files": files}
    (output / "verifiedinfer-manifest.json").write_text(
        json.dumps(manifest, indent=2) + "\n"
    )
    print(f"{args.repo}@{revision} -> {output}")


if __name__ == "__main__":
    main()
