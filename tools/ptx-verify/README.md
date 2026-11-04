# PTX Verify

Translate PTX into Lean program data and verify kernels with separate Lean contracts.

## Setup

Requires Rust with edition 2024 support, Python 3, Git, and Lean **4.35.0**.
The setup script fetches the pinned Iris-Lean and Mathlib dependencies.

```sh
cd tools/ptx-verify
bash scripts/bootstrap.sh
```

If Lean is installed outside `PATH`, prefix commands with
`LEAN_TOOLCHAIN_DIR=/path/to/lean-4.35.0`.

## Run verification

```sh
bash scripts/check.sh
```

To also assemble the PTX examples with NVIDIA's assembler:

```sh
PTXAS=/path/to/ptxas bash scripts/check.sh
```

## Translate a kernel

```sh
cargo run --locked -- examples/copy.ptx /tmp/Copy.lean
```

Translation produces an AST; verification requires a Lean contract.
Build an existing contract from the `lean/` directory:

```sh
cd lean
lake build Ptx.Kernels.Copy
lake build Ptx.Kernels.SharedSwap
lake build Ptx.Iris.HeapProtocol
```

## Add a kernel

1. Put its PTX in `examples/` and generate `lean/Ptx/Generated/Name.lean`.
2. Add its specification and proof in `lean/Ptx/Kernels/Name.lean`, importing the
   generated module and reusing modules under `lean/Ptx/Rules/`.
3. Import the contract in `lean/Ptx.lean`. Add regression examples under
   `lean/Ptx/Tests/` and import them in `lean/Ptx/Tests.lean`.
4. Add the fixture to `CASES` in `scripts/check.py` and public theorems to
   `lean/Ptx/Tests/Audit.lean`, then run `scripts/check.sh`.

Supported input: PTX 7.0, `sm_70`, 64-bit addresses, and one CTA. Instructions
include scalar `u32` global/shared loads and stores, `u32/u64` integer arithmetic,
branches, loops, and full-CTA `bar.sync`. Unsupported instructions are rejected.
