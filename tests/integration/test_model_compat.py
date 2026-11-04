"""Small real-format HF fixtures exercise architecture adapters and independent math.

Byte equality is REQUIRED for the same C/CUDA plan across prefix partitions.
HF uses a different FP32 reduction plan: comparisons to it are diagnostic only
and never evidence of exact equivalence or a formal proof.
"""
import argparse
import copy
import itertools
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

import numpy as np
from safetensors.numpy import load_file, save_file
import torch
from transformers import LlamaConfig, LlamaForCausalLM, Qwen2Config, Qwen2ForCausalLM


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-dir", type=Path, default=Path("build"))
    parser.add_argument("--device", choices=["cpu", "cuda"], default="cpu")
    args = parser.parse_args()
    binary = (args.build_dir / "vi-run").resolve()
    runner = (args.build_dir / "tests/integration/test_model_runner").resolve()
    torch.set_num_threads(1)
    comparisons = []
    with tempfile.TemporaryDirectory(prefix="vi-compat-") as directory:
        root = Path(directory)
        ids = [1, 2, 3, 4, 1]
        input_path = root / "input.ids"
        input_path.write_text(" ".join(map(str, ids)))
        logits_path = root / "logits.bin"

        def invoke(model_path, *extra, success=True):
            command = [str(binary), "--model", str(model_path), "--device", args.device,
                       "--input", str(input_path), "--forward-only", "--logits", str(logits_path), *extra]
            p = subprocess.run(command, text=True, capture_output=True)
            assert "Sanitizer" not in p.stderr, p.stderr
            if success and p.returncode:
                raise AssertionError(p.stderr)
            if not success:
                assert p.returncode == 1 and p.stderr.startswith("vi-run:"), (
                    f"invalid checkpoint must be cleanly rejected: {model_path}", p.returncode, p.stderr)
                return p.stderr
            values = np.fromfile(logits_path, dtype=np.float32)
            assert np.isfinite(values).all()
            return values

        cases = [("llama-tied", LlamaConfig, LlamaForCausalLM, True, False),
                 ("llama-bias", LlamaConfig, LlamaForCausalLM, False, True),
                 ("qwen2", Qwen2Config, Qwen2ForCausalLM, False, True)]
        for name, config_class, model_class, tied, bias in cases:
            torch.manual_seed(2026)
            config = config_class(vocab_size=41, hidden_size=16, intermediate_size=24,
                num_hidden_layers=2, num_attention_heads=4, num_key_value_heads=2,
                max_position_embeddings=32, rms_norm_eps=1e-5, rope_theta=10000.,
                hidden_act="silu", tie_word_embeddings=tied, attention_bias=bias,
                attention_dropout=0., use_sliding_window=False)
            config._attn_implementation = "eager"
            model = model_class(config).float().eval()
            model_path = root / name
            model.save_pretrained(model_path, max_shard_size="2KB" if name == "qwen2" else "5GB")
            # A non-contiguous physical layout (shards) must not change the model.
            actual = invoke(model_path)
            with torch.inference_mode():
                reference = model(torch.tensor([ids]), use_cache=False).logits[0, -1].numpy()
            error = float(np.max(np.abs(actual - reference)))
            # This bounds the diagnostic to catch gross implementation errors;
            # the exact acceptance requirement is the byte comparison below.
            assert error < 2e-5, (name, error)
            assert int(actual.argmax()) == int(reference.argmax()), name
            chosen = int(actual.argmax())
            stopped = subprocess.run([str(binary), "--model", str(model_path), "--device", args.device,
                "--input", str(input_path), "--max-new-tokens", "4",
                "--eos", str((chosen + 1) % 41), "--eos", str(chosen)],
                check=True, text=True, capture_output=True)
            assert len(stopped.stdout.splitlines()) == 1
            comparisons.append({"architecture": name, "hf_max_abs_diagnostic": error})
            for boundaries in itertools.product((False, True), repeat=len(ids) - 1):
                lengths, start = [], 0
                for end in range(1, len(ids) + 1):
                    if end == len(ids) or boundaries[end - 1]:
                        lengths.append(end - start)
                        start = end
                partitioned = invoke(model_path, "--chunks", ",".join(map(str, lengths)))
                assert actual.tobytes() == partitioned.tobytes(), (name, lengths)
            subprocess.run([str(runner), str(model_path), args.device], check=True)

            if name == "llama-tied":
                valid_path = model_path
                valid_config = json.loads((model_path / "config.json").read_text())

        # Reuse a tiny model's weights to test parser/feature rejection, not a
        # fake architecture alias that silently ignores unsupported behavior.
        for field, value in [("architectures", ["UnsupportedForCausalLM"]),
                             ("rope_scaling", {"rope_type": "linear", "factor": 2}),
                             ("num_key_value_heads", 3), ("hidden_act", "gelu"),
                             ("quantization_config", {"quant_method": "gptq"}),
                             ("head_dim", 3), ("qk_norm", True)]:
            bad = root / f"bad-{field}"
            shutil.copytree(valid_path, bad)
            changed = copy.deepcopy(valid_config)
            changed[field] = value
            (bad / "config.json").write_text(json.dumps(changed))
            invoke(bad, success=False)
        malformed = root / "malformed"
        shutil.copytree(valid_path, malformed)
        (malformed / "model.safetensors").write_bytes(b"\xff" * 8)
        invoke(malformed, success=False)
        for mode in ["shape", "missing", "nonfinite", "unknown", "overflow"]:
            bad = root / f"bad-{mode}"
            shutil.copytree(valid_path, bad)
            tensors = load_file(bad / "model.safetensors")
            if mode == "shape": tensors["model.layers.0.self_attn.q_proj.weight"] = np.zeros((1, 16), dtype=np.float32)
            if mode == "missing": del tensors["model.layers.0.self_attn.k_proj.weight"]
            if mode == "nonfinite": tensors["model.norm.weight"][0] = np.nan
            if mode == "unknown": tensors["unsupported.weight"] = np.ones((1,), dtype=np.float32)
            if mode == "overflow": tensors["model.embed_tokens.weight"][1] = np.finfo(np.float32).max
            save_file(tensors, bad / "model.safetensors")
            invoke(bad, success=False)
        for mode in ["extent", "duplicate", "dtype", "truncated", "index-traversal"]:
            bad = root / f"bad-{mode}"
            shutil.copytree(valid_path, bad)
            path = bad / "model.safetensors"
            payload = path.read_bytes()
            length = int.from_bytes(payload[:8], "little")
            header = json.loads(payload[8:8 + length])
            tensor_name = next(k for k in header if k != "__metadata__")
            if mode == "extent": header[tensor_name]["data_offsets"][1] = 2**63
            if mode == "dtype": header[tensor_name]["dtype"] = "I32"
            encoded = json.dumps(header).encode()
            if mode == "duplicate":
                entry = json.dumps(tensor_name).encode() + b":" + json.dumps(header[tensor_name]).encode()
                encoded = encoded[:-1] + b"," + entry + b"}"
            path.write_bytes(len(encoded).to_bytes(8, "little") + encoded + payload[8 + length:])
            if mode == "truncated": path.write_bytes(path.read_bytes()[:-16])
            if mode == "index-traversal":
                (bad / "model.safetensors.index.json").write_text(json.dumps({"weight_map": {"x": "../model.safetensors"}}))
            invoke(bad, success=False)
        # Every supported on-disk dtype, including BF16 trained checkpoints.
        half = root / "half"
        shutil.copytree(valid_path, half)
        tensors = {name: tensor.astype(np.float16) for name, tensor in load_file(half / "model.safetensors").items()}
        save_file(tensors, half / "model.safetensors")
        invoke(half)
        bf16 = root / "bf16"
        shutil.copytree(valid_path, bf16)
        from safetensors.torch import save_file as save_torch
        bf16_tensors = {name: torch.from_numpy(tensor).to(torch.bfloat16)
                        for name, tensor in load_file(bf16 / "model.safetensors").items()}
        save_torch(bf16_tensors, bf16 / "model.safetensors")
        invoke(bf16)
    print(json.dumps({"device": args.device, "same_plan_partition_checks": 48,
                      "hf_diagnostics": comparisons, "formal_proof": False}, indent=2))


if __name__ == "__main__":
    main()
