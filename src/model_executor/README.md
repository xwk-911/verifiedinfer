# Model execution boundary

`model.c` implements the public lifecycle in `include/verifiedinfer/model_executor/`.
A model owns immutable checkpoint tensors and architecture-specific weight views.
Each state borrows its model and owns exclusive architecture-specific data; destroy
all states before their model. The returned runner borrows its state, and copying
it does not clone a request. No forward allocation or asynchronous return is added.

`model_registry.c` selects an implementation from both checkpoint `architectures`
and `model_type`. Repository aliases belong to `cli/` and the Docker convenience
entry. The registry currently accepts only the implemented Llama/Qwen2 subset.

`model_loader.c` reads checkpoint files, validates safetensors and exposes private
JSON readers through `model_json.h`. Each executor validates model semantics and
binds named tensors; generic I/O does not choose a Transformer computation graph.
`model_runner.c` validates the input suffix and dispatches to that executor. A
fatal compute error makes the state terminal, with no assumption of GPU rollback.

`models/llama_decoder.c` and its private header own the existing full causal
attention, RMSNorm, half-split RoPE and SwiGLU implementation and its KV layout.
Both Llama and Qwen2 registry entries reuse it. Shared/public state descriptors do
not contain dense K/V pointers. CPU reference and GPU operator implementations
live in `ops/`. The GPU backend uses C host scheduling, standalone PTX custom
kernels and cuBLAS linear operations; see [the operator backend](ops/README.md).
The PTX migration preserves the original arithmetic order and precision.

To add an architecture, supply its configuration validation, weight binding/free,
private state creation/free, forward and logical computed-token count callbacks,
then register it. Do not silently ignore unsupported checkpoint semantics. Add
reference/checkpoint and exact same-plan cache/partition tests. New callbacks
remain proof obligations; adding a registry entry is not a compatibility proof.
There are no placeholder DeepSeek/Qwen4 implementations.

The public forward still returns last-position logits. Greedy sampling, token
history, EOS and generation budget remain in the engine/sampler. `--forward-only`
is a CLI validation mode over the same model runner. The former tiny dense
architecture is a test-only fixture in `tests/support/tiny_transformer.*`; no mock
model or demo is shipped.

The current formal-proof migration status is recorded in
[`proof/architecture-migration.md`](../../proof/architecture-migration.md).
