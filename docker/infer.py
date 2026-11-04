"""Compose's inference entry: prepare a pinned checkpoint, build, and generate."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

MODELS = {
    "smollm2": ("HuggingFaceTB/SmolLM2-135M-Instruct", "12fd25f77366fa6b3b4b768ec3050bf629380bac"),
    "qwen": ("Qwen/Qwen2.5-0.5B-Instruct", "7ae557604adf67be50417f59c2c2f167def9a775"),
}

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--model", default="smollm2", help="smollm2, qwen, local checkpoint, or HF repository")
parser.add_argument("--revision", help="Pinned revision for another HF repository")
args, generation_args = parser.parse_known_args()
root = Path(os.environ["WORKSPACE"])
model = Path(args.model)
if not (model.is_dir() and (model / "config.json").is_file()):
    repository, revision = MODELS.get(args.model, (args.model, args.revision))
    if not revision:
        parser.error("another HF repository requires --revision; local checkpoints do not")
    model = root / "models" / repository.split("/")[-1]
    manifest = model / "verifiedinfer-manifest.json"
    existing = json.loads(manifest.read_text()) if manifest.is_file() else {}
    if existing.get("repository") != repository or existing.get("revision") != revision:
        subprocess.run([sys.executable, "tools/download_model.py", "--repo", repository,
                        "--revision", revision, "--output", str(model)], check=True)
device = os.environ.get("VI_DEVICE", "cuda")
build = root / "build" / "container" / device
subprocess.run(["make", "--no-print-directory", "-s", f"CUDA={int(device == 'cuda')}",
                f"BUILD_DIR={build}", "all"], check=True)
os.execv(sys.executable, [sys.executable, "examples/generate.py", "--model", str(model),
                         "--device", device, "--binary", str(build / "vi-run"), *generation_args])
