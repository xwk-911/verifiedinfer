"""Compare cached/cold native logits and tokens, and report HF diagnostics.

Native runs must match byte for byte within one execution plan. Hugging Face
uses a different floating-point plan; its diagnostics are reported separately.
"""

import argparse
import json
from pathlib import Path
import subprocess
import tempfile
import time


def run_native(binary, model, input_path, device, *options):
    return subprocess.run(
        [
            str(binary), "--model", str(model), "--input", str(input_path),
            "--device", device, *options,
        ],
        text=True,
        capture_output=True,
        check=True,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--model", required=True, type=Path)
    parser.add_argument("--binary", type=Path, default=Path("build/vi-run"))
    parser.add_argument("--device", choices=["cpu", "cuda"], default="cpu")
    parser.add_argument("--prompt", default="The capital of France is")
    parser.add_argument("--tokens", type=int, default=4)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    if args.tokens < 1:
        parser.error("--tokens must be positive")

    import numpy as np
    import torch
    from transformers import AutoModelForCausalLM, AutoTokenizer

    torch.set_num_threads(1)
    tokenizer = AutoTokenizer.from_pretrained(
        args.model, local_files_only=True, trust_remote_code=False
    )
    history = tokenizer.encode(args.prompt, add_special_tokens=True)
    binary = args.binary.resolve()
    diagnostics = []
    with tempfile.TemporaryDirectory(prefix="vi-real-check-") as temporary:
        root = Path(temporary)
        input_path = root / "input.ids"
        input_path.write_text(" ".join(map(str, history)))
        cached_path = root / "cached.bin"
        start = time.perf_counter()
        generation = run_native(
            binary, args.model, input_path, args.device,
            "--max-new-tokens", str(args.tokens), "--logits", str(cached_path),
        )
        # Includes loading and startup; this is not a throughput benchmark.
        native_seconds = time.perf_counter() - start
        tokens = [json.loads(line)["token"] for line in generation.stdout.splitlines()]
        cached = np.fromfile(cached_path, dtype=np.float32).reshape(len(tokens), -1)
        hf = AutoModelForCausalLM.from_pretrained(
            args.model,
            dtype=torch.float32,
            local_files_only=True,
            trust_remote_code=False,
            attn_implementation="eager",
        ).eval()
        for step, token in enumerate(tokens):
            input_path.write_text(" ".join(map(str, history)))
            cold_path = root / "cold.bin"
            run_native(
                binary, args.model, input_path, args.device,
                "--forward-only", "--logits", str(cold_path),
            )
            cold = np.fromfile(cold_path, dtype=np.float32)
            assert cached[step].tobytes() == cold.tobytes(), (
                f"same-plan mismatch at output {step}"
            )
            with torch.inference_mode():
                reference = hf(
                    torch.tensor([history]), use_cache=False
                ).logits[0, -1].numpy()
            maximum_error = float(np.max(np.abs(cold - reference)))
            diagnostics.append({
                "position": step,
                "token": token,
                "hf_token": int(reference.argmax()),
                "hf_max_abs_diagnostic": maximum_error,
                "same_plan_logits_bitwise_equal": True,
            })
            # HF diagnostics catch gross loading/architecture mistakes. They do
            # not replace the mandatory native byte-equality check above.
            assert maximum_error < 0.01, (
                f"large HF diagnostic difference: {maximum_error}"
            )
            assert token == int(reference.argmax()), (
                f"greedy token differs from HF at {step}"
            )
            history.append(token)
    report = {
        "model": str(args.model),
        "device": args.device,
        "generated_tokens": tokens,
        "text": tokenizer.decode(tokens),
        "native_load_and_generation_seconds": native_seconds,
        "checks": diagnostics,
        "formal_proof": False,
        "cross_backend_bitwise_equivalence": False,
    }
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
