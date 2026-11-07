# PTX Verify

Translate PTX into Lean program data and verify kernels against independent Lean
contracts using fixed execution and memory semantics.

The delivered prototype has seven acceptance groups with checked, model-relative
VCs and complete execution witnesses. Its verdict is **prototype acceptance with
declared gaps**. The [acceptance report](docs/prototype-evidence.json) records exact
statements, assumptions, coverage limits and separate finite GPU evidence.

## Setup and acceptance

Requires Rust with edition 2024 support, Python 3, Git and Lean **4.35.0**.
Bootstrap fetches the pinned Iris-Lean revision and Mathlib dependencies.

```sh
cd tools/ptx-verify
bash scripts/bootstrap.sh
bash scripts/check_prototype.sh
```

If Lean is outside `PATH`, prefix these commands with
`LEAN_TOOLCHAIN_DIR=/path/to/lean-4.35.0`. To include NVIDIA assembly checks, set
`PTXAS=/path/to/ptxas`. GPU checks require an available compatible CUDA driver/GPU.
On CPU-only hosts, explicitly disable the hardware stage:

```sh
bash scripts/check_prototype.sh --gpu off
```

Acceptance runs the unchanged strict gate, generated-file checks, frontend
acceptance/rejection probes, real Lean assumption-audit regressions, prototype
build and dependency audit, and fresh finite GPU checks. It writes
`docs/prototype-evidence.json` with a source fingerprint; failures return nonzero
and write a failed report. CPU-only mode records GPU evidence as not run.

The strict and hardware gates are also available separately:

```sh
bash scripts/check.sh
PTXAS=/path/to/ptxas bash scripts/check.sh
bash scripts/check_gpu.sh --report docs/gpu-evidence.json
```

Structured JSON evidence is versioned. Raw `docs/*.log` output, Rust/Lean build
artifacts, downloaded dependencies and Python caches are generated locally and
ignored by Git. A fresh acceptance run regenerates its logs and reports.

## Translate and verify

```sh
cargo run --locked -- examples/copy.ptx /tmp/Copy.lean
cd lean
lake build Ptx.Kernels.Copy
lake build Ptx.Kernels.ReleaseAcquireMessageUniversal
lake build Ptx.Kernels.ReleaseAcquireMessageClient
```

Translation emits the original instruction data and a checked typing certificate.
Kernel correctness requires a separate specification and proof; successful
translation or typing alone does not establish safety, correctness or termination.

The [instruction inventory](instructions.toml) lists every accepted opcode spelling,
canonical alias, operand probe, backend, semantic source and limitation. Current
inventory checks cover 73 spellings / 72 canonical local forms. Correspondence
with the paper's 81-form inventory remains **unconfirmed**; the difference between
counts is not a missing-instruction count. Unsupported forms and combinations
are rejected explicitly.

## Source layout

- `src/`: Rust parser, typed AST and Lean data emitter.
- `examples/`: accepted PTX fixtures and intentionally invalid execution examples.
- `lean/Ptx/Generated/`: mechanically translated, checked program data.
- `lean/Ptx/ISA/`, `Event/`, `Scalar/`, `Ordered/`, `Shuffle/`, `Ampere/`,
  `Hopper/`: typing, source execution, byte/event memory and instruction semantics.
- `lean/Ptx/Kernels/`: independent specifications, source reconstruction,
  correctness proofs and legal execution witnesses.
- `lean/Ptx/Async/`, `Iris/`: modeled borrowing/completion protocols and checked
  Iris interfaces, including exclusive and native GenHeap interpretations.
- `lean/Ptx/Tests/`: semantic regressions, negative results and exact proof audit.
- `lean/PtxPrototype/`: isolated prototype assumptions and Lean metadata audit.
- `scripts/`: bootstrap, strict/prototype/GPU acceptance and audit regressions.

`lean/Ptx.lean` imports the strict library; `lean/Ptx/Tests.lean` imports regressions.
`lean/PtxPrototype.lean` is the independent prototype entry point. Dependency
versions are pinned in `lean/lean-toolchain`, `lean/lake-manifest.json` and bootstrap.

## Cases and supported scope

[prototype.toml](prototype.toml) registers exact correctness, non-vacuity and
instance theorems for all seven original acceptance groups:

- Copy/SharedSwap: integer byte outputs and observed frame preservation.
- Scalar matmul: represented real matrices, runtime K, guarded output indexing.
- Atomic dispatch: two CTAs with the supported relaxed GPU-scoped `add.u32`.
- Scalar online attention: independent natural-exp specification and empty keys.
- Three-kernel MoE: two-expert top-1 route/experts/combine in one sequential stream.
- Ampere tiled matmul: supported asynchronous copy/MMA layouts, zero K and masks.
- Hopper double-buffer GEMM: fixed 64x8 output, K up to 2^28 tiles, modeled byte
  values and borrowing protocol, including zero K and complete native witnesses.

The [coverage inventory](coverage.toml) records twelve capability groups and each
case's implementation gaps. A registered VC can be `strict-proof`,
`conditional-proof` or `unsupported`; its proof status applies to its printed
statement and scope. Implementation coverage remains separately marked partial.

Additional source-derived contracts cover all four shuffle modes under bounded
single-CTA output layouts and the two-thread release/acquire message fixture.
The latter allows arbitrary finite polling, oracle replies and trace order under
its actual initialization/layout precondition. Its native client interleaves the
same PTX instruction steps with the existing loan protocol: source acquire,
device completion and host acquisition remain distinct, and premature reclaim
is rejected.

## Temporary auxiliary lemmas

The production assumption registry is currently empty. Prototype permission to
leave auxiliary lemmas open does not weaken existing strict proofs.

Future temporary gaps must be named proposition axioms in
`lean/PtxPrototype/Assumptions.lean`, under `PtxPrototype.Assumptions`. Strict
`Ptx` sources cannot import prototype assumptions. Alternative proofs belong in
`PtxPrototype` modules imported by `lean/PtxPrototype.lean`; `prototype.toml` maps
original VC names to alternatives using `overrides`, and Lean checks their types.

Obtain exact checked registration metadata after declaring an auxiliary lemma:

```sh
python3 scripts/check_prototype.py --describe-assumption PtxPrototype.Assumptions.example
```

Replace `assumptions = []` with `[[assumptions]]` entries before
`[capability_claims]`. Each entry requires `name`, `role`, `statement`,
`type_sha256`, `purpose`, `review`, `affected_vcs` and `discharge_task`. Supported
roles describe arithmetic, indexing, collections, encoding or local semantic
interfaces. Impact lists must match actual transitive VC dependencies.

Top-level correctness, safety and legal-execution existence VCs must remain
proved theorems. Anonymous holes, unregistered axioms, changed statements/types,
stale impact lists and direct/renamed/definition/structure VC wrappers are
rejected. Fixed-program assumptions and `False` cannot be registered as auxiliary
gaps. These structural checks do not decide arbitrary semantic equivalence or
axiom consistency; the required statement review remains explicit. Conditional
proofs stay conditional until their assumptions are discharged.

## Extend the tool

1. Add PTX under `examples/` and generate its `lean/Ptx/Generated/Name.lean` data.
2. Write independent specifications and proofs under `lean/Ptx/Kernels/`, reusing
   the relevant fixed semantics and rules. Keep legal execution witnesses separate
   from universal correctness; report source safety separately from error-valued
   Iris `NotStuck` results.
3. Import production modules in `lean/Ptx.lean` and regressions in
   `lean/Ptx/Tests.lean`. Add exact public theorem/proof-field entries to
   `lean/Ptx/Tests/Audit.lean`.
4. Register the fixture in `scripts/check.py`. For new frontend forms, update
   `instructions.toml` and parser regressions; update `coverage.toml` and
   `prototype.toml` with actual claims and remaining limits.
5. Run the prototype acceptance command and inspect the report's statements,
   source fingerprint, negative evidence and hardware scope.

## Proof and runtime boundaries

- The Rust parser/compiler chain is not formally verified. Generated-file
  comparison and Lean typing check emitted data; kernel proofs interpret that
  data with the fixed Lean semantics.
- Floating-point proofs use represented exact-real values/fragments. `ex2` uses
  its declared real abstraction; IEEE rounding, NaNs/infinities and universal
  hardware logits/token equality are outside these proofs. Finite GPU checks
  compare exact bytes without tolerances and remain separate evidence.
- Current ordered forms cover fixed global u32 relaxed/acquire loads and
  relaxed/release stores with cta/gpu/sys scopes inside one device launch.
  Host/multi-device system scope, fences, extended patterns, ordered atomics and
  general ordered/shuffle/async/tensor composition remain unsupported.
- Iris interfaces have distinct ownership scopes. The ordered client uses
  exclusive whole-state OwnP; native byte GenHeap clients cover their declared
  source families. Fractional ordered byte transfer, complete source-to-region
  reservation coverage and general overlapping-kernel frontiers remain open.
- Physical allocation, CUDA runtime/command interpretation, full ISA weak/proxy
  conformance and scheduling progress remain explicit boundaries. Protocol scalar
  buffers are not physical PTX bytes. No throughput, latency or optimization
  novelty result follows from prototype acceptance.
- Hopper fixtures assemble, but current GPU evidence comes from sm_89 hardware
  and does not establish Hopper hardware behavior.

## Evidence and detailed documentation

- [Latest prototype acceptance](docs/prototype-evidence.json), including scoped
  theorem statements, assumptions, capabilities and instruction probes.
- [Latest prototype GPU checks](docs/prototype-evidence.gpu.json) and
  [PTX assembly evidence](docs/assembly-evidence.json).
- [Memory-model documentation](docs/memory-model.md).
- [Detailed implementation notes](docs/development-notes.md), preserving the
  previous README's milestone explanations.
- [Chronological research and validation record](docs/coverage.md), including
  proof boundaries, reuse evidence, validation checkpoints and goal accounting.
