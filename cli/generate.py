"""HF tokenizer frontend; all forward and sampling executes in the C engine."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

from transformers import AutoTokenizer


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--model", type=Path, required=True, help="Local HF checkpoint directory")
    parser.add_argument("--device", choices=["cpu", "cuda"], default="cpu")
    parser.add_argument("--binary", type=Path)
    parser.add_argument("--prompt", required=True)
    parser.add_argument("--max-new-tokens", type=int, default=32)
    parser.add_argument("--raw", action="store_true", help="Plain completion; no chat template")
    parser.add_argument("--ignore-eos", action="store_true", help="Fixed-length workload")
    parser.add_argument("--logits", type=Path, help="Optional FP32 logits dump for each output")
    args = parser.parse_args()
    if args.max_new_tokens < 0:
        parser.error("--max-new-tokens must be nonnegative")
    root = Path(__file__).resolve().parents[1]
    binary = (args.binary or root / ("build/cuda/vi-run" if args.device == "cuda" else "build/vi-run")).resolve()
    if not binary.is_file():
        parser.error(f"missing {binary}; build with make" + (" CUDA=1" if args.device == "cuda" else ""))
    tokenizer = AutoTokenizer.from_pretrained(args.model, local_files_only=True, trust_remote_code=False)
    if not args.raw and tokenizer.chat_template:
        ids = tokenizer.apply_chat_template([{"role": "user", "content": args.prompt}],
                                            tokenize=True, add_generation_prompt=True)
    else:
        ids = tokenizer.encode(args.prompt, add_special_tokens=True)
    if not ids:
        parser.error("prompt must tokenize to a nonempty sequence")
    eos = tokenizer.eos_token_id
    generation_path = args.model / "generation_config.json"
    if generation_path.is_file():
        eos = json.loads(generation_path.read_text()).get("eos_token_id", eos)
    eos_ids = [] if eos is None else eos if isinstance(eos, list) else [eos]
    if not args.ignore_eos and (len(eos_ids) > 32 or any(type(i) is not int or i < 0 for i in eos_ids)):
        parser.error("EOS configuration must contain at most 32 nonnegative token IDs")
    with tempfile.TemporaryDirectory(prefix="verifiedinfer-") as temporary:
        input_path = Path(temporary) / "prompt.ids"
        input_path.write_text(" ".join(map(str, ids)) + "\n")
        command = [str(binary), "--model", str(args.model.resolve()), "--device", args.device,
                   "--input", str(input_path), "--max-new-tokens", str(args.max_new_tokens)]
        if not args.ignore_eos:
            for token_id in eos_ids:
                command += ["--eos", str(token_id)]
        if args.logits:
            command += ["--logits", str(args.logits)]
        completed = subprocess.run(command, text=True, capture_output=True)
        if completed.returncode:
            raise SystemExit(completed.stderr.strip())
        tokens = [json.loads(line)["token"] for line in completed.stdout.splitlines()]
    print(tokenizer.decode(tokens, skip_special_tokens=True))


if __name__ == "__main__":
    main()
