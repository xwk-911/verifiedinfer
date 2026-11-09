# VerifiedInfer
VerifiedInfer aims to provide deterministic LLM inference and formally verify that its inference engine produces exactly the same logits and tokens as the corresponding open-source implementations for the same model, inputs, and initial sampling state.

```bash
./dev build

# bash
./dev run --rm engine bash

# Trained models: the first run automatically prepares the model and builds the CUDA engine
./dev run --rm engine generate --model smollm2 \
    --prompt "What is the capital of France?" --max-new-tokens 32
./dev run --rm engine generate --model qwen \
    --prompt "What is the capital of France?" --max-new-tokens 32

# C regression and model compatibility tests
./dev run --rm engine make test model-test

# QCP's prebuilt Rocq foundation; translate PTX, then check its supplied proof
./dev run --rm qcp check
./dev run --rm ptx translate examples/copy.ptx lean/Ptx/Generated/Copy.lean
./dev run --rm ptx verify Ptx.Kernels.CopyEventWitness \
    Ptx.CopyEvent.correct Ptx.CopyEvent.nonvacuous

# Export PTX for the project's CUDA operators
./dev run --rm engine make cuda-ptx
```

Model module boundaries and extension contracts are described in [model_executor](src/model_executor/README.md).

Compose provides separate `engine`, `coq`, `qcp` and `ptx` images. `qcp` reuses the
Coq toolchain image and adds the C symbolic executor and precompiled upstream
foundation. `ptx` owns its [image and workflow](tools/ptx-verify/README.md), including
Lean/Iris/Mathlib dependencies. Dependencies are installed at image build time;
QCP/PTX runtime services are offline. Compose orchestrates these environments
directly; no nested Docker daemon is needed. Project-specific QCP rules under
`proof/` remain separate from the image's upstream foundation.

## Related work

### LLM Inference

- Vosti: https://github.com/QDelta/Vosti
- ds4: https://github.com/antirez/ds4
- DeepInfer: https://github.com/deepseek-ai/DeepInfer

### GPU Kernel equivalence

- Kuiper/RESOLVE: https://arxiv.org/abs/2610.05683
- LARK: https://arxiv.org/pdf/2611.02028v1
- Volta: https://github.com/willtunnels/volta
- PTX in Lean: https://sf-tensor.com/papers/formalizing-ptx.pdf
- LKV: https://github.com/facebookresearch/lean_kernel_verify

### LLM model equivalence verification

- Emerge: https://arxiv.org/pdf/2603.21851
- Tensor Algebra Equivalence Checker: https://pldi26.sigplan.org/details/ARRAY-2026-papers/12/Tensor-Algebra-Equivalence-Checker
