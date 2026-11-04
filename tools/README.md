# Tools

Run these commands from the repository root unless noted otherwise.

## Verification

- [PTX Verify](ptx-verify/README.md): translate PTX and check Lean kernel contracts.
- [QCP](QCP/README.md): C verification tooling.
- [LKV](LKV/README.md): Lean kernel verification reference.

Initialize the QCP and LKV submodules with:

```sh
git submodule update --init --recursive tools/QCP tools/LKV
```

## Development

Generate `compile_commands.json` for clangd from the current Make configuration:

```sh
python3 tools/generate_compile_commands.py
# Pass a custom Make command or configuration when needed:
python3 tools/generate_compile_commands.py make CUDA=1
```

## Models

Use the project Python environment. Downloading requires `huggingface_hub`;
reference checking also requires NumPy, PyTorch, and Transformers.

```sh
.venv/bin/python tools/download_model.py --repo HuggingFaceTB/SmolLM2-135M-Instruct \
  --output models/SmolLM2-135M-Instruct
.venv/bin/python tools/check_model.py --model models/SmolLM2-135M-Instruct \
  --binary build/vi-run --device cpu
```

Pass `--revision HASH` to pin a download; the downloader records its revision and hashes. The checker
compares cached and cold native runs and reports Hugging Face diagnostics.
Use `--help` for all options.

## NVIDIA compatibility

Extract matching userspace libraries into `build/`, then use them for one command:

```sh
python3 tools/setup_nvidia_compat.py
sh tools/with_nvidia.sh nvidia-smi
sh tools/with_nvidia.sh make CUDA=1 model-test
```

Use `--archive /path/to/NVIDIA-Linux-x86_64-<version>.run` to reuse a local archive.
