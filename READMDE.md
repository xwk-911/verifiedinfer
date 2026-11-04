# Agentic Verified Optimization of Real-World LLM Inference

## C reproduction scaffold

Build with a C11 compiler and Make:

```bash
make demo
make dense-demo
make test
make sanitize
```

`make demo` runs the synthetic mock model; `make dense-demo` runs a tiny CPU
Transformer with deterministic untrained weights. Both use the same engine and
greedy sampler. They accept token IDs, without a tokenizer or checkpoint loader.

### Components and naming

- `engine/`: request lifecycle and forward/sample/commit orchestration.
- `model_executor/model_runner.h`: `vi_model_runner`, a borrowed model handle and
  synchronous forward function. `vi_model_input` carries a token suffix and its
  absolute starting position. This is a small C interface inspired by DeepInfer's
  engine/worker/ModelRunner separation, not a port of its GPU runtime.
- `model_executor/models/mock_model.h`: `vi_mock_model`, a token cache, rolling
  hash and call counter producing synthetic logits.
- `model_executor/models/dense_model.h`: `vi_dense_weights` (immutable, shareable)
  and `vi_dense_model` (per-request K/V cache and workspace).
- `memory/`: exclusively borrowed token buffers; no engine/model heap allocation.

The previous `vi_backend` / `vi_mock_backend` names and `VI_BACKEND_ERROR` have
been replaced by `vi_model_runner` / `vi_mock_model` and `VI_MODEL_ERROR`.
Concrete model headers are public under `include/verifiedinfer/`.

`vi_engine_init` now also borrows a logits workspace and its capacity.
`vi_output` contains a caller-provided logits pointer and capacity: vocabulary
size is model-dependent, with no 32-token scaffold limit. The scratch and output
arrays are separate so failed steps preserve previously published output.
Pointers, descriptors, and writable arrays must not overlap. Declared capacities
must describe real allocations; runtime NULL/size checks cannot establish that.

### Tiny dense architecture and reference execution

The fixture has vocabulary 40, hidden dimension 4, FFN dimension 6, context 8,
one layer and one attention head. Dimensions are configuration values, not
hardcoded in the implementation. Weights are contiguous row-major arrays;
`vi_dense_weights_init` creates named read-only views in the order documented
in `dense_model.h`. Count helpers check size arithmetic before buffer slicing.

For each token at absolute position `p`:

1. Add token embedding and learned position embedding to obtain `x`.
2. Apply RMSNorm; project Q, K and V; write K/V at position `p`.
3. Compute `softmax(Q K[0:p+1]^T / sqrt(hidden_size)) V[0:p+1]`.
4. Apply output projection and residual addition.
5. Apply RMSNorm, then `down(SiLU(gate(x)) * up(x))`, and residual addition.
6. Normalize the last processed row and apply the LM head to obtain logits.

There are no biases, RoPE, MoE or GPU kernels. In particular, learned absolute
positions differ from Vosti's rotary policy: no Vosti/DeepInfer numerical
equivalence is claimed. Unlike DeepInfer's hidden-state forward output followed
by its sample path, this minimal runner includes the LM head and returns one
logits row. Read-only weights can be shared, but each request needs its own cache,
workspace, history and runner state. Reinitialize a model to start a fresh cache.

The synchronous forward consumes exactly the suffix at `input.position ==
cache.len`. On success its committed cache length advances by the suffix length.
The engine then samples and appends one token, so at every successful output
boundary `history.len == kv_len + 1`. The final sampled token need not enter KV.
On forward failure the committed cache prefix and length remain unchanged;
unused cache rows and scratch may be overwritten, and a retry rewrites them.
EOS stopping is an explicit request policy; demos disable it to show four outputs.

### Validation and proof boundary

`make test` includes the original buffer/request/sampler/mock lifecycle tests and
a dense test with a hand-computable scalar case. An independent cold reference
materializes full-prefix Q/K/V and causal scores without calling the production
forward or its helpers. Tests compare logits and committed K/V bytes exactly for
all 128 partitions of each of three eight-token histories (384 partition cases),
and compare generated tokens and sampler state across interleaved requests with
shared weights. They also check invalid positions, capacities, finite weights,
numeric failure after partial suffix work, and successful retry. Compilation
disables FMA contraction with `-ffp-contract=off`; no tolerance comparison is used.
This is evidence for this CPU/compiler/libm arithmetic plan, not all platforms
or arbitrary configurations. `make sanitize` repeats the tests with ASan/UBSan.

Reference reading for this implementation: `Vosti/src/spec.rs`,
`Vosti/src/proof/model/dense_swiglu/semantics.rs`, and
`Vosti/src/proof/model/dense_swiglu/cache_fidelity.rs`; execution organization:
`DeepInfer/deepinfer/worker/model_runner.py` and
`DeepInfer/deepinfer/model_executor/models/deepseek.py`.

Research record for this iteration: this is a synchronous engineering baseline,
with no optimization or performance gain claimed. The existing canonical-prefix
method describes the desired cache invariant; no missing proof capability or
new reusable rule has been established here. The first C proof target remains
`vi_token_buffer_append`, followed by request transitions and canonical K/V
correspondence. **No project C proof has been checked with QCP/Rocq**, and the
independent C reference tests are not Vosti differential verification. C/libm,
compilation and future kernel/runtime contracts remain proof obligations;
asynchronous events, resource return and new-method reuse remain future work.

## Related work

### LLM Inference
- Vosti: https://github.com/QDelta/Vosti
- ds4: https://github.com/antirez/ds4
- DeepInfer: https://github.com/deepseek-ai/DeepInfer

### GPU Kernel equivalence
- Kuiper/RESOLVE: https://arxiv.org/abs/2610.05683
- LARK: https://arxiv.org/pdf/2611.02028v1

### LLM model equivalence verification
- Emerge: https://arxiv.org/pdf/2603.21851
- Tensor Algebra Equivalence Checker: https://pldi26.sigplan.org/details/ARRAY-2026-papers/12/Tensor-Algebra-Equivalence-Checker

## Verification tools

- **QCP**: [QualifiedCProgramming](https://github.com/QinxiangCao/QualifiedCProgramming)
- **RESOLVE**: [paper](https://arxiv.org/abs/2610.05683)
- **LKV**: [lean_kernel_verify](https://github.com/facebookresearch/lean_kernel_verify)
- **Volta**: [Volta](https://github.com/willtunnels/volta)

Initialize the tool submodules after cloning:

```bash
git submodule update --init --recursive
```
