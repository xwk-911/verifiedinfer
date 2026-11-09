# Model executor module split

This is an engineering refactor of the synchronous single-request baseline. It
introduces no optimization, new proof method, performance claim or weakened
numerical requirement. The existing registered architectures remain the supported
Llama/Qwen2 subset; the split does not add DeepSeek or another model family.

## Current source ownership

- `cli/vi_run.c` and `cli/generate.py` own command-line/tokenizer I/O.
- `model.c` owns public model/state lifecycle and device uploads.
- `model_diagnostic.c` owns typed internal text, string and shape diagnostics.
- `model_registry.c` maps architecture and model_type to an implementation.
- `model_loader.c` owns checkpoint I/O, JSON utilities and safetensors validation.
- `model_runner.c` checks inputs and dispatches synchronous execution.
- `models/llama_decoder.c` owns Llama/Qwen2 configuration, weight binding,
  private state allocation and forward; its private layouts are declared in
  `models/llama_decoder.h`.
- `ops/cpu.c` and `ops/cuda.cu` retain the original operator arithmetic/plan.
- The former untrained dense fixture is `tests/support/tiny_transformer.*` and
  is linked only into tests. Mock model/demo sources and public fixture headers
  have been removed. Test-local error/tie callbacks still exercise the runner
  contract; they are not shipped model implementations.

## Formal status

Pre-split forward, lifecycle, loader and engine proof work must be rebound to
this source layout before it can establish coverage of the refactor. Those
proof developments are maintained separately from this source change; this
commit does not claim that they certify the new implementation.

Source correspondence checks must reject stale paths/types rather than infer
that a rename proves equivalence. A full-goal checker must require the new
`model`, `model_registry`, `model_runner` and `llama_decoder` cases as well as the
existing obligations. The private layer-weight record still has 13 pointers;
ABI audits must read `models/llama_decoder.h` at its new location. No empty proof
stubs are presented as completed coverage.

Required migration work:

1. Bind the forward cases to `models/llama_decoder.c` and its private
   `vi_llama_state`/`vi_llama_weights` descriptors. The operator call order and
   FP32 math are retained, but changed C types require checked correspondence.
2. Specify and verify the generic model-state wrapper and runner dispatch,
   including ownership of `state->data`, borrowed model lifetime, initialization
   failure cleanup and terminal compute failures. Do not assume registry callbacks
   satisfy contracts without the corresponding model proofs.
3. Rebind lifecycle and checkpoint proofs to their split source functions.
4. Update the runner field from `model` to `state` in the engine's C view and
   regenerate affected VCs. Preserve the stronger reusable KV-initialization
   postcondition and every existing required goal.
5. Re-run the QCP workflow and independent final replay before reporting coverage.

The third address-foundation repair additionally requires a checked native type
environment. `scripts/prepare_canonical_type_names.py` stages fresh named-record
header views in `reports/canonical-type-names/`, preserving every other C token
and checking all 20 project record size/alignment outputs against actual headers.
It gives 17 anonymous typedef records stable, distinct tags without modifying
production headers. These named views are now applied under `QCP_examples/Current`
and the current source audit checks their correspondence. `NativeRecordLayouts.v`
binds source-derived field types, offsets, sizes and alignments for all 20 project
records; compiler probes compare both actual and named headers. Local type scopes,
third-party records where used, complete successful-lookup coverage and fresh
implementation proofs remain open. No historical proof certifies the new views.

The current runner additionally makes its static `execute` contract explicit in
the binder's program-environment resources. This does not discharge the internal
function proof or its code-address connection. See
[internal callback composition](internal-code-linking.md); the full goal requires
both `InternalCodeLinks.v` and `CRefinement.v`.

Source extraction, ABI interpretation, compiler, CUDA runtime, cuBLAS and the
QCP/Lean connection remain explicit boundaries. The refactor adds no new
assumptions or claims of completed proof coverage.

The model facade requires both build configurations. `model.c` contains the
CUDA upload/staging/cleanup path under `VI_ENABLE_CUDA`; default CPU
preprocessing omits it. `scripts/current_model_builds.py` therefore pins a
CPU-only `model` view and a CUDA-enabled `model_cuda` view, both with all
original C function-body tokens. The full checker requires both cases.
Compiler preprocessing comparisons (including contrary incoming macro settings)
passed; the two implementation proofs are still pending. Production code is
unchanged, and the CUDA-enabled host view needs no CUDA compiler to preprocess.

## Execution evidence

The local `build/refactor-llm-modules/` directory retains a pre-change source
snapshot, pre/post CPU and CUDA binaries, exact output comparisons and test logs.
Comparisons use the same backend/precision/flags and require identical stdout
(token IDs/cache positions) and every FP32 logits byte; CPU/HF/CUDA arithmetic
plans are not equated. These are execution tests, not formal proofs. Details and
completed check status are recorded there after verification.
