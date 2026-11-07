# Coverage and evidence

The reference is SF Tensor's [Formalizing PTX in Lean to Prove GPU Kernel
Correctness](https://sf-tensor.com/papers/formalizing-ptx.pdf), especially sections
3–5, and the archived [PTX ISA 9.4](https://docs.nvidia.com/cuda/archive/13.4.2/parallel-thread-execution/index.html).
`coverage.toml` records current capabilities and outstanding obligations. The
paper reports 81 fixed instruction forms but does not enumerate every qualifier
combination; exact instruction-for-instruction parity is unconfirmed.

The inventory is not a proof certificate. `baseline` means the existing restricted
operational model has proofs; `partial` means some infrastructure exists but the
stated capability is incomplete; `planned` means it is not implemented. Copy,
SharedSwap, publication, scalar matmul and the scalar literal/shared helper have universal
contracts relative to the current ordinary-memory projection; no entry establishes full PTX compliance.

Latest Hopper source-value milestone: bounded positive-K complete source
scripts are now constructed from the actual initial ten-region byte pool,
with correct final real GEMM fragments and closed native GenHeap adequacy.
This closes the previously conditional source-prefix value witness. A combined
source/value/protocol script now also supplies source-matched device drain and
final acquire, retaining correct matrix fragments and returning all ten modeled
loans in the same state. Native public preparation now starts in the initial
no-loan protocol in that same language, seals the exact queue frontier and gates
source/device actions on it. Physical value/protocol/runtime refinement remains open.
Zero-K value/native construction is now also checked for arbitrary completed
zero-K sources. One bounded-K client contract covers zero and positive K under
the independent GEMM specification, with both successful-run correctness and
complete execution existence. The zero-K pool needs only output/barrier storage.
Full-source closed adequacy uses the retained whole-map helper. All seven
required cases remain partial; see the final research record for scope and tests.

## Semantic layers

1. `ISA/Syntax.lean` holds the original shared program data. `Semantics.lean`
   retains its original single-CTA executable semantics and epoch conflict monitor.
   Extracting constructors does not enlarge the accepted PTX language.
   The Rust frontend uses structured nodes in `src/ast.rs`, retaining integer
   widths and all register declaration types through serialization. `ISA/Typing.lean`
   validates the complete emitted program and constructs a proof-carrying typed
   instruction list; its erasure is the identical raw list. `TypedSemantics.lean`
   proves interpreter equality and register-value preservation for successful
   event executions from typed register files. This is not a verified frontend
   or a complete PTX type system. Integer literals and address offsets use `u64`
   rather than host-sized `usize`.
2. `ISA/Launch.lean` distinguishes thread/CTA identities and CTA-local shared
   locations. `ISA/Bytes.lean` provides little-endian u32 byte payloads and a
   universal round-trip theorem. Launch dimensions are descriptions, not proof of
   hardware launch limits or allocation safety.
3. `Event/Thread.lean` produces finite traces from the SAME generated integer
   programs under explicit load oracles. Local arithmetic/control semantics are
   reused from the operational interpreter. A barrier emits arrival/return events
   with a separate generation counter for each barrier resource. Their emission
   alone does not establish that participants match or that a return is allowed.
   Event kinds now parameterize their payload type while retaining the original
   concrete-byte default. `Scalar/Thread.lean` supplies a staged mixed integer/real
   backend over symbolic float fragments, with an integer conservative-extension
   theorem. Thirteen fixed f32 frontend forms now emit this typed scalar data;
   their launch-wide provenance is connected to the same generic memory predicates
   through `Scalar/Execution.lean`. `Scalar/Context.lean` supplies CTA dimensions
   for mov.u32 coordinate/size reads; provenance uses the actual launch block. FMA
   still has local trace proofs only.
   The online attention fixture has a parameterized mathematical invariant and
   actual initialization/update/normalization block proofs plus the complete
   inner and outer loops through store/return from PC 37, with local register
   frames and derived instruction counts. General PC=0 parameter/index/guard/address
   initialization now supplies that invariant, including separate masks/empty keys
   and a constructed local reply function for arbitrary real matrices. Arbitrary
   successful complete PC=0 runs are now reconstructed with candidate-local
   per-item replies and derived f32 tags; no input-oracle agreement is assumed.
   Global initial-read correspondence, memory contract and independent global
   nonvacuity remain open duties.
4. `Event/Execution.lean` requires launch-wide thread coverage, unique identities
   and trace provenance. Completion is separate. These definitions do not yet
   impose memory consistency, allocation validity or barrier matching by themselves.
   Graph payload and oracle metadata types are parameters, retaining the original
   defaults. Scalar provenance checks the actual mixed interpreter and full final
   float bank; it does not assert integer provenance for float code.
5. `Event/Memory.lean`, `Relations.lean`, and `Consistency.lean` define bytewise
   reads-from and ordinary weak generic-proxy memory conditions: partial coherence,
   causality, single-copy atomicity, SC-per-location, race taint, barrier participation
   and acyclic barrier control. The same definitions and proofs apply to concrete
   integer bytes and symbolic real fragments. They are predicates checked in Lean
   proofs, not new axiom declarations. NTA is omitted. Scoped relaxed RMW strength,
   observation chains and RMW atomicity are now part of the common predicates;
   acquire/release, scoped plain accesses, other proxies and fence.sc remain outside
   the accepted subset.
6. `Event/Witnesses.lean` constructs initial-before-write coherence witnesses using
   an explicit ranking of a selected execution. This construction does not restrict
   the allowed-execution predicates to ranked executions.
7. `Event/Observation.lean` provides projected ordinary generic-memory conditions
   for logical reads after synchronized completion; `Event/Contracts.lean` separates
   universal output contracts from non-vacuity. Copy/SharedSwap observe all allocated
   global bytes under its original bounds. Full augmented-graph correspondence,
   remaining existing-kernel refinement, allocation/UB obligations,
   further scalar kernel contracts, broader scalar/real-valued instructions and
   asynchronous device operations remain. `FloatLiteralsUniversal.lean` now has
   an all-candidate model-relative output contract plus non-vacuity; it is an
   auxiliary four-byte-output helper, not a scalar matmul acceptance case.
   `ScalarMatmulOutput.correct` and `ScalarMatmulEvent.nonvacuous` separately prove
   all-candidate matrix output/frame and complete consistent execution/observation
   existence under explicit bounded geometry, layout and symbolic initialization.

See [ordinary memory model boundaries](memory-model.md) for the rules and current
positive/negative proof evidence. Copy has a direct event-output contract,
completion witnesses and event-to-operational allocated-byte output inclusion.
SharedSwap also has an event contract, completion witnesses and general operational
output inclusion, including the original collective release.

## Implementation order and acceptance

- Preserve Rust/frontend, generated AST, existing Lean contracts and negative
  regressions at every step.
- Complete bytewise event relations, ordinary memory consistency and synchronization;
  demonstrate both allowed and forbidden litmus outcomes, and explicit witnesses
  for allowed executions. Do not filter all races out of the model.
- Preserve Copy/SharedSwap's event-to-operational output inclusion under their
  original preconditions when extending the supported subset. Both directions
  must be named accurately: operational-to-event inclusion alone would not have
  transferred the existing output guarantee to arbitrary event executions.
- Extend typed scalar operations, scoped atomics and shuffle. Prove affine,
  scalar matmul and atomic dispatch; then scalar online FlashAttention and
  same-stream three-kernel MoE composition.
- Add Ampere copy groups, waits and MMA layouts; prove tiled matmul with buffer
  reuse. Add Hopper TMA/proxies/mbarrier/WGMMA; prove a single-stage kernel before
  a two-stage double-buffered GEMM.
- Interpret in-flight access footprints, completion and publication in the existing
  Iris/host-device loan protocol. PTX device groups and CUDA API events have distinct
  meanings and require an explicit connection.

Each final kernel needs a parameterized universal correctness theorem, a
consistent complete execution for every admissible launch, a concrete admissible
launch, and targeted missing-synchronization/lifetime counterexamples where
applicable. Non-vacuity is not termination for all schedules. Build reusable rules
alongside each kernel, rather than postponing automation until all examples exist.

## Checks and trust boundary

`scripts/check.sh` checks formatting, Rust unit tests/lints, inventory structure,
generated AST reproducibility, Lean builds, public theorem axioms and deliberate
negative proof attempts. Inventory validation checks evidence paths and status
structure, not the truth or completeness of a capability. Add every new public
semantic theorem to `Tests/Audit.lean`.

Keep finite instance tests, universal Lean proofs, PTX assembly, and GPU execution
tests distinct. Assembly is optional when `ptxas` is unavailable; GPU execution
needs a working runtime and architecture-appropriate hardware. Neither test closes
the compiler/hardware trust boundary. Parser correctness is also not mechanically
proved by reproducible AST generation.

The event extension must explicitly document any omitted PTX axioms, ISA-level UB
assumptions, unsupported constructs and runtime assumptions. Real-valued float
correctness does not establish IEEE bit equality or exact logits/token equality.
Do not weaken the project's exact execution-comparison requirement.

Cluster Launch Control (not formalized in the reference), concurrent kernels,
multi-GPU execution and float bit reinterpretation are outside this parity target.

## Research record: event foundation

- Optimization instances: prefetch and deferred reclamation already share the
  abstract loan protocol. This change prepares their device-semantic connection;
  it does not implement or measure an additional optimization.
- Existing limitation: the operational interpreter has one mutable heap and an
  epoch monitor; the async-to-PTX bridge describes completed scalar copies, not
  in-flight PTX reads/writes or weak visibility.
- Method implemented so far: oracle-driven trace generation over shared program
  data, byte payloads and launch-qualified identities, with checked trace provenance.
- Reuse evidence so far: a theorem generates the actual Copy AST's trace for
  arbitrary scalar data, and local instruction meanings are reused. This is not
  yet a weak-memory soundness theorem or evidence of a novel research method.
- Performance/proof cost: no optimization benchmark or GPU correctness run in this
  stage; report actual check results separately. Required later measurements retain
  fixed model/precision/workload and separate baseline, unverified and verified
  variants, including throughput, TTFT, tail latency, memory and proof/agent costs.

## Research record: ordinary generic memory

- Optimization instances and missing ability: unchanged from the event foundation;
  completed scalar-copy data correspondence does not describe weak visibility or
  justify in-flight resource return.
- Method implemented: bytewise source witnesses, memory/control relations and
  ordinary generic-memory predicates; reusable unique-writer visibility and
  read-only consistency constructions. These are baseline formalization work,
  not a claim of a novel proof method.
- Reuse evidence: one read-only rule constructs checked executions for arbitrary
  scalar input. The same byte-access interface supports ordinary reads, uniform
  race classification and mixed-size relation checks. There is not yet evidence
  of reuse across actual optimized kernels.
- Boundary discovered: final `done` states alone permit circular exemptions for
  different barriers. A separate acyclic control-order condition excludes these
  traces; its exit edges do not establish memory visibility.
- Tests and proof scope: read-only non-vacuity and oracle rejection are universal
  Lean theorems; race classification tests and byte-footprint examples have their
  narrower stated scope. No device performance measurement or GPU equivalence
  claim has been added in this stage.

## Research record: publication and completion observation

- Optimization instances: the same prefetch and deferred-reclamation targets;
  this stage builds the synchronous publication baseline needed to connect them.
- Existing limitation: trace generation and conditional visibility rules alone
  did not construct a multi-thread memory witness or define synchronized output.
- Implemented method: reusable initial-coherence witness construction, explicit
  observer source/value/no-stale conditions and independent event contracts.
- Evidence at this stage: an actual translated `barrier_publish.ptx` has a provenance-checked
  two-thread completion and observation witness for arbitrary input and initial
  byte map. Output correctness quantifies over arbitrary reader answers and memory
  witnesses WITHIN the characterized trace family. It is not yet a universal
  arbitrary-candidate kernel contract or a Copy/SharedSwap transfer theorem.
- Reuse limits: observer unique-writer/frame rules and witness construction are
  generic; reuse on a second optimized kernel, performance gains and research
  novelty have not been established. No extra synchronization was inserted into
  an existing optimization to obtain a performance claim.
- Source boundary: the semantic reference is the archived PTX 9.4 documentation
  used by the paper. The live NVIDIA URL is mutable and is not the version pin.

## Research record: arbitrary-candidate coverage and Copy traces

- Existing limitation: selecting a plausible oracle/trace family did not establish
  that it represented every complete execution of the translated program.
- Implemented method: completed-run uniqueness for unbounded natural step counts,
  candidate trace lookup under unique thread IDs, and event-view transport of
  ordinary memory and observation predicates. Completion/control metadata remain
  explicit duties rather than consequences of event equality.
- Evidence: publication now has universal model-relative `Triple` and `Nonvacuous`
  proofs. They quantify over arbitrary candidates, all oracles, trace-list orders,
  memory witnesses and observer maps; the earlier family-coverage gap is closed.
- Reuse: the same completed-run theorem reconstructs Copy's 12-step active and
  7-step masked traces for the original general Config/Params. Byte-footprint
  bounds and original disjointness establish race freedom for arbitrary complete
  candidates, not a scalar-only sample. At that stage, Copy output refinement
  remained outstanding; the following record describes the output work.
- Negative checks: altered instruction counts, appended stores, and a matching
  event view with incomplete status do not become valid completed observations.
- Research/performance boundary: these are baseline proof-infrastructure results,
  not a new optimization or proof-method novelty claim. No performance or GPU
  equivalence result is asserted; the full paper-parity goal is unchanged.

## Research record: Copy byte outputs and existence

- Existing limitation: authentic traces and race freedom did not constrain output
  observations or show that the contract admitted any complete execution. The
  optional-cell model also left unknown frame bytes implicit.
- Implemented method: an explicit initialized-cell/byte relation with a stable
  arbitrary fallback, universal read/source and destination/frame rules, and an
  observation witness selected from each byte's actual unique writer. A selector
  must cover every emitted write; it cannot silently choose an initial source.
- Evidence: Copy's `correct` quantifies over every well-formed complete candidate,
  read oracle, source/coherence witness and permitted observation. `nonvacuous`
  constructs a consistent complete execution and observer for every launch in
  `Pre`, using the original general Config/Params and positive thread count.
  Empty inputs with positive count are included; the old zero-thread CPU case
  remains in the baseline, with an explicit no-launch bridge still required.
- Connection to the baseline: exact allocated-byte agreement is proved with any
  completed operational run, including unknown frame bytes under the same initial
  fallback. This conditional theorem does not establish general operational
  completion existence or the full output-inclusion obligation. The interleaved
  masked and reversed-layout test schedules supply actual completed runs for
  those finite instances only.
- Reuse and tests: the existing generic coherence witness and observer rules now
  cover both barrier publication and Copy. Regressions exercise u32 truncation,
  reversed layout, excess threads, empty input and nonzero unknown frame bytes;
  universal negatives reject wrong read/output bytes and stale initial sources,
  including equal-valued stale sources. Deliberately false truncation/frame
  claims must also be rejected by Lean during the normal check.
- Research/performance boundary: this closes baseline engineering obligations;
  no optimized kernel, new proof-method novelty, GPU exactness or performance
  result is claimed. The async in-flight connection and full parity goal remain.
- Validation on 2026-11-04: the full check passed with 9 Rust tests, 6 regenerated
  AST comparisons, 416 audited Lean declarations and 9 deliberate false claims
  rejected. PTX assembly was skipped because `ptxas` was not configured. No GPU
  execution or benchmark was run; check time and manual/agent cost were not measured.

## Research record: operational completion and output inclusion

- Existing limitation: Copy's output agreement required a completed operational
  execution as a premise. Safety, progress and finite-instance schedules did not
  by themselves construct one for every original configuration.
- Implemented method: generic local forward-instruction/work and single-thread
  interpreter projection rules, a strictly decreasing list potential, and a
  finite-completion construction from invariant preservation and concrete progress.
  `steps_run` converts the relational witness into a replayable interpreter schedule.
  No fairness, extra synchronization or new semantic axiom is assumed.
- Evidence: `CopyCompletion.complete_from_pre` covers every original Config and
  Pre, including flexible parameter bindings, arbitrary frame/shared data and
  zero threads. `CopyEvent.output_inclusion` proves that EVERY allowed event
  observation equals the encoded output of some actually completed operational
  run over the entire allocated global domain. The input representation re-encodes
  to the identical initial byte map, including uninitialized frame bytes.
- Zero-thread boundary: `zero_count_skip` derives empty input and identity output
  from the original precondition, with an empty action list and explicit rejection
  of a positive event launch. It is a host no-launch path, not a GPU zero-sized launch.
- Negative evidence: an actual one-instruction self-loop always has a next step,
  yet no finite execution completes and no strict rank can certify its unchanged
  state. Normal checks must reject both treating its back edge as forward and
  treating one successful step as completion. The masked all-candidate inclusion
  instance complements earlier concrete interleaved execution comparisons.
- Reuse/remaining work: these are generic rules plus their first kernel application;
  SharedSwap additionally needs collective barrier completion and shared visibility.
  Full PTX correspondence, in-flight async resource interpretation and the other
  parity cases remain. This is baseline engineering, with no new optimization,
  proof-method novelty, GPU exactness or benchmark result claimed.
- Validation on 2026-11-04: the full check passed with 9 Rust tests, 6 regenerated
  AST comparisons, 438 audited Lean declarations and 11 false claims rejected.
  PTX assembly was skipped because `ptxas` was not configured; no GPU execution,
  optimization benchmark, check-time or manual/agent-cost measurement was performed.

## Research record: SharedSwap barrier and shared visibility

- Existing limitation: Copy did not exercise internal shared-memory publication.
  Barrier helpers did not establish correctness of the existing exchange kernel.
- Implemented method: authentic complete traces over the original Config/Params,
  source/shared-load answers kept independent, bytewise writer uniqueness and
  causal publication through the original full-CTA barrier. Generic eligible-read
  visibility derives each shared value from the actual opposing write. The global
  observer selects only writes in its observation domain; internal shared writes
  do not need to be exposed as outputs.
- Evidence: `SharedEvent.correct` quantifies over all well-formed complete
  candidates, all read/source/coherence choices and permitted observations, with
  exact exchanged bytes and unchanged allocated-global frame. `nonvacuous`
  constructs a consistent complete execution and observer for every admissible
  original configuration, arbitrary represented initialization and shared fallback.
  The two-thread limit comes from the original `1-tid` kernel specification.
- Reuse: the same local completed-trace uniqueness, initial-coherence construction,
  unique-writer visibility and byte-observer rules now cover publication, Copy and
  SharedSwap. These are baseline formalization results, not proof-method novelty
  or reuse across measured asynchronous optimizations.
- Tests: original round-robin/reverse-layout executions match the finite byte
  observations; regressions cover u32 truncation and nonzero unknown frame bytes.
  Universal negatives reject wrong shared-load/output bytes and stale initial
  sources even at equal values. A forged trace omitting the barrier is rejected
  as not produced by this AST; this is distinct from a missing-barrier PROGRAM.
- Connection at that stage: finite comparisons did not establish general operational
  completion/output inclusion for SharedSwap. The following record closes that
  bridge with collective completion. Full PTX correspondence, ISA UB obligations and all
  later parity cases remain. No GPU execution, optimization benchmark or precision
  target change is claimed in this stage.
- Validation on 2026-11-04: full checks passed with 9 Rust tests, 6 regenerated AST
  comparisons, 489 audited Lean declarations and 13 false claims rejected. PTX
  assembly was skipped (`ptxas` not configured). GPU/optimization runs and manual/
  agent-cost measurements were not performed.

## Research record: collective completion and SharedSwap output inclusion

- Existing limitation: SharedSwap had universal event outputs and event witnesses,
  but only finite operational comparisons. Thread PC work alone does not decrease
  when the original collective release resumes waiting threads.
- Implemented method: reuse the generic invariant/progress completion construction
  and add one remaining-release component to the operational potential. Existing
  control invariants prove the release phase and actual rendezvous; no extra
  synchronization or fairness/termination assumption is added. A shared region
  representation rule proves allocated-byte agreement, including unknown frame
  bytes, from separately derived cell and byte postconditions.
- Evidence: `SharedCompletion.complete_from_pre` covers every original Config/Pre,
  including arbitrary shared initialization, initial register contents allowed by
  Pre and flexible parameter bindings. `SharedEvent.output_inclusion` quantifies
  over every permitted event candidate/observer and constructs an actual completed,
  replayable operational run with the same allocated-global bytes. No completed
  operational execution is an extra premise of this inclusion theorem.
- Reuse: Copy's representation/output bridge now uses exactly the same region
  rules as SharedSwap. Their existing contract statements and original Config/Pre
  conditions are preserved. The generic completed-execution/steps-to-run rules are
  also shared; SharedSwap supplies the separate collective progress argument.
- Tests: the actual release keeps PC potential at 12 while total work drops from
  13 to 12; the normal rejection suite must refute strict PC-work decrease. A
  custom original-precondition state exercises initialized shared data, stale
  register values, unused parameters and a shadowed parameter tail. Universal
  tests compare arbitrary event outputs with a replayable operational witness and
  with the original concrete round-robin run. A representation-only counterexample
  shows that unknown bytes still require the byte-frame duty.
- Research/performance boundary: baseline output bridges are complete relative to
  the current ordinary-memory/observer subset. Allocation/ISA UB, full PTX/observer
  correspondence, weak-memory extensions, the remaining parity kernels and the
  async runtime connection are outstanding. No GPU execution, optimization gain,
  new proof-method novelty or change to exact execution comparison is claimed.
- Validation on 2026-11-04: full checks passed with 9 Rust tests, 6 regenerated AST
  comparisons, 517 audited Lean declarations and 14 false claims rejected. PTX
  assembly was skipped (`ptxas` not configured). No GPU/optimization execution,
  check-time or manual/agent-cost measurement was performed.

## Research record: checked integer program data and type preservation

- Existing limitation: the Rust AST retained register declarations, but Lean output
  discarded them. The raw AST allowed arbitrary widths, register classes and
  branch targets, and had no type-preservation connection to either interpreter.
- Implemented method: retain the complete declaration environment in generated
  Lean data and require a decidable `ProgramTyped` certificate. Typed instruction
  subtypes carry the checked rule for each original instruction. Erasure preserves
  every instruction and its order; operational/event execution equality is proved
  against the existing fixed interpreters, with no new per-kernel semantics.
- Evidence: every existing generated fixture now carries a Lean-checked typing
  proof. Six original raw instruction lists were confirmed unchanged. Successful
  local instructions and arbitrary finite event runs preserve the declared value
  bounds, conditional on typed starting registers. Oracle loads are covered and
  still consume arbitrary Nat answers wrapped by the existing u32 semantics.
- Rule scope: checks cover u32/u64 and matching b32/b64 storage, predicate-only
  uses, declared parameter widths, 64-bit addresses/offsets, supported binary width
  combinations, branch bounds, barrier-ID bounds and unique declaration names.
  The current frontend deliberately uses stricter equal-width compatibility than
  the ISA's relaxed ld/st rules; see [PTX operand type checking](https://docs.nvidia.com/cuda/archive/13.4.2/parallel-thread-execution/index.html#operand-type-checking).
  Signed/floating frontend operands were still unsupported at that stage; the
  later float frontend record adds a fixed f32 subset without changing this
  integer layer's type rules.
- Tests: Rust preserves unused declarations and rejects register-class, parameter,
  address and arithmetic width confusion. Independent Lean negatives also reject
  malformed or duplicate emitted declarations. Mixed bit/unsigned execution
  exercises wide multiply, u64 arithmetic and predicates. The old missing-sync
  and out-of-bounds fixtures remain well typed while their separate execution
  checks reject them. A typed uninitialized read faults; a typed self-loop never
  completes, so the type certificate cannot stand in for safety or liveness.
- Frontend gap fixed: resolved shared-symbol addresses previously bypassed the
  u32 immediate bound applied to literals. They now obey the same bound; a
  regression exercises a symbol whose computed address exceeds that width.
- Reuse/remaining work: the same type certificate and interpreter connections apply
  to all existing fixtures; raw contract statements and original instruction
  forms are retained. At that stage, typed real-valued fragments/operations and
  scalar matmul were next obligations; the following record adds the local float
  backend, not a completed matmul case. Parser/source
  correspondence, full ISA type compatibility and allocation/UB remain external
  to these proofs. This is baseline formalization work, without an optimization
  benchmark, new proof-method novelty or change to exact logits/token requirements.
- Validation on 2026-11-04: full checks passed with 11 Rust tests, 6 regenerated AST
  comparisons, 542 audited Lean declarations and 18 false claims rejected. The
  original Copy/SharedSwap/Iris proofs still pass. PTX assembly was skipped because
  `ptxas` was not configured; no GPU run, optimization benchmark or manual/agent-
  cost measurement was performed.

## Research record: symbolic float fragments and mixed local semantics

- Existing limitation: integer bytes/registers cannot represent exact real-valued
  floats. Treating them as Nat values, or keeping stale integer/float values under
  the same register name, would silently invent bit reinterpretations.
- Implemented method: tagged real fragments with explicit f16/f32/f64 width and
  byte index; exact-real scalar mov/add/mul/FMA and typed read-oracle replies.
  The mixed interpreter delegates integer steps at the original PC, while float
  writes invalidate same-name integer data and integer completion drops shadowed
  float data. Event payload types are parameterized, with the old byte default.
- Evidence: fragment encoding is injective and decoding succeeds exactly for a
  complete encoding; integer bytes, width mismatch, reordering and torn f32
  fragments are rejected. Bank disjointness is preserved by arbitrary successful
  mixed executions. A universal step/run theorem preserves all original integer
  execution states/errors/events under the explicit embedding, and the existing
  arbitrary-data Copy trace is reused under this theorem.
- Local arithmetic evidence: a checked six-instruction program has a complete
  load/FMA/store/return trace for arbitrary real load answers, with output fragments
  encoding `a*b+c`. Finite f32 input literals have explicit range/non-finite guards;
  only source literals are decoded from bits. Negative zero denotes real zero.
  This follows the paper's [exact-real abstraction and symbolic-storage boundary](https://sf-tensor.com/papers/formalizing-ptx.pdf),
  not NVIDIA's rounded IEEE arithmetic. Source literal notation and fma forms are
  described in the archived [PTX ISA 9.4](https://docs.nvidia.com/cuda/archive/13.4.2/parallel-thread-execution/index.html).
- Tests: same-name cross-representation overwrites cannot expose stale data; real
  replies cannot feed integer loads and integer replies cannot feed float loads.
  Native f32 declarations are not integer registers. These local rules and the
  symbolic-fragment negatives are audited independently of the integer regressions.
- Remaining work at that stage: float PTX parsing/serialization, provenance-checked launch-wide
  float candidates, generic-memory/observer integration and parameterized kernel
  contracts remained. The following record implements frontend translation while
  retaining the global-proof obligations. The original local FMA program
  is NOT an accepted paper-parity case or a global memory-consistency witness.
- Research/performance boundary: this is baseline semantics infrastructure, with
  no optimization gain, new proof-method novelty, GPU bit-equality or numerical
  error claim. The exact logits/token comparison requirement is unchanged. Scalar
  matmul and all later parity cases remain in the active full goal.
- Validation on 2026-11-04: full checks passed with 11 Rust tests, 6 regenerated AST
  comparisons, 585 audited Lean declarations and 20 false claims rejected. PTX
  assembly was skipped (`ptxas` not configured). No GPU execution, optimization
  benchmark, check-time or manual/agent-cost measurement was performed.

## Research record: mechanical f32 translation and local provenance

- Existing limitation: the scalar real backend only consumed handwritten Lean
  instruction data. The PTX frontend could not produce it, and an emitter could
  lose declaration classes, float literal bits or branch PCs when mixing forms.
- Implemented method: structured f32 operands/operations, exact finite hexadecimal
  source literals and explicit integer wrappers in mixed scalar programs. Native
  f32 declarations and b32 storage are retained; the generated `Scalar.CheckedProgram`
  independently checks every instruction and literal guard. Pure integer programs
  retain their existing data format. Float programs explicitly identify the real
  abstraction in generated headers and CLI output.
- Accepted forms: mov.f32; rn add/mul/FMA; global/shared f32 load/store. Other
  qualifiers, floating predication, decimal/nonfinite literals and f16/f64 source
  forms remain unsupported. Source notation/type compatibility follow the archived
  [PTX ISA 9.4](https://docs.nvidia.com/cuda/archive/13.4.2/parallel-thread-execution/index.html);
  arithmetic retains the paper's exact-real abstraction, with no IEEE proof claim.
- Evidence: actual translated `float_fma.ptx` has a parameterized eight-step local
  trace for arbitrary real answers, thread IDs, bounded pointer values and flexible
  parameter bindings. Actual `float_literals.ptx` computes 1+2 and then times 3,
  emits a shared store of 9, consumes an independent shared-load answer and writes
  that answer globally. Both generated programs have checked type certificates.
- Negative evidence: Rust checks finite literal boundary patterns, register class,
  address width, qualifiers and mixed branch PCs. NaN/Infinity rejection is also
  enforced by uninhabitable Lean literal certificates. A complete local execution
  using shared-read answer 17 is explicitly proved; its write of 17 must later be
  excluded by global memory consistency, not silently replaced during translation.
- Reuse/remaining work: generated programs use the existing fixed scalar semantics
  and integer-local rules; no per-kernel meaning is emitted. Launch-wide float
  candidates, memory/observer contracts and scalar matmul remained outstanding
  at that stage. The following record connects the scalar execution layer and
  proves a contract for the literal/shared helper; FMA remains local. These
  fixtures are not paper-parity acceptance cases. Parser/source equivalence and full PTX-model correspondence remain unproved.
- Research/performance boundary: baseline frontend engineering only; no new
  optimization, proof-method novelty, numerical error bound, GPU bit-equality or
  performance gain is claimed. The full goal and exact logits/token comparison
  requirement are unchanged.
- Validation on 2026-11-04: full checks passed with 15 Rust tests, 8 regenerated
  AST comparisons, 599 audited Lean declarations and 22 false claims rejected.
  Coverage inventory validation and whitespace checks passed. PTX assembly was
  skipped (`ptxas` not configured); no GPU execution or performance measurement
  was performed.

## Research record: symbolic scalar events and universal shared-memory helper

- Existing limitation: `Event.Kind` accepted symbolic payloads but candidates,
  memory relations and observers still fixed concrete integer bytes. Local scalar
  traces could consume arbitrary shared-read answers without a global consistency
  proof. A chosen good oracle would not establish kernel correctness.
- Implemented method: parameterize the existing graph by payload and oracle
  metadata types, retaining byte/integer defaults and identical integer bodies.
  Generalize the same memory, causality, taint, coherence, witness, observation
  and event-view transport rules; no separate float memory axioms were introduced.
  `Scalar/Execution.lean` checks coverage, unique thread IDs and provenance using
  the actual scalar interpreter, including the full final float register bank.
- Instance: actual translated `float_literals.ptx` computes (1+2)*3, stores 9 in
  shared memory, reads an independent real answer and writes it globally.
  `FloatLiteralsMemory.lean` derives race freedom, source uniqueness and causal
  visibility from its emitted events. For every initial symbolic map and every
  reads-from/coherence witness, consistency forces the shared answer to be 9.
  A constructive memory/observation witness handles every bounded destination
  pointer, flexible parameter environment and initial symbolic map in the contract.
- Universal correctness: `FloatLiteralsUniversal.lean` reconstructs every complete
  provenance-checked candidate, independently of instruction count, unused oracle
  replies or trace-list order. The proof first extracts a typed reply from the
  actual load step, then uses completed-run uniqueness and event-view transport.
  `Scalar.Triple` proves output 9 and `Scalar.Nonvacuous` separately provides a
  complete consistent execution and synchronized observation. This is not a
  bounded execution check or a contract over one selected oracle.
- Reuse/negative evidence: the existing `unique_writer_visible` rule and
  `initial_co_conditions` construction handle symbolic real fragments without
  changing their reasoning rules. Tests include the concrete address-64 instance,
  rejection of shared answer 17 for all memory witnesses, missing/duplicate thread
  identities, a forged instruction count and an integer reply for a float load.
  Original Copy/SharedSwap contracts and event-to-operational bridges are retained.
- Remaining duties: this helper observes only its four-byte output domain; it is
  not a required paper-parity case. FMA's global contract, scalar matmul and the
  remaining full goal are still outstanding. Allocation/UB, valid 64-bit access
  footprints, full PTX/observer correspondence, parser correctness and runtime
  connection are not concluded by these model-relative results. IEEE rounding,
  GPU bit equality and the exact logits/token requirement are unchanged.
- Research/performance boundary: this is baseline semantics/proof infrastructure,
  not a new optimization or proof-method novelty claim. No optimization benchmark,
  GPU execution, manual/agent-cost or performance gain is claimed.
- Validation on 2026-11-04: the complete check passed with 15 Rust tests, 8
  regenerated AST comparisons, 645 audited Lean declarations and 22 deliberately
  false claims rejected. Nine new FloatMemory regression theorems cover the
  contract, non-vacuity, a concrete instance and negative provenance/memory cases.
  Updated inventory metadata (12 capabilities, 10 cases) and whitespace checks
  passed separately. PTX assembly was skipped (`ptxas` not configured); no GPU
  execution was performed.

## Research record: actual scalar matmul frontend and launch geometry

- Existing limitation: source operands only exposed tid.x, while the paper's
  scalar matmul assigns outputs using a 2-D grid of 2-D CTAs. Treating ntid as an
  oracle or silently assuming a unit CTA would invalidate output ownership.
- Implemented method: typed axis/special-register nodes for mov.u32 reads of
  tid.y/z, ctaid.x/y/z and ntid.x/y/z. Legacy tid.x data remains identical. The
  scalar context extends the existing integer context with explicit CTA shape;
  legacy local calls embed with a unit block, while launch-wide `Produced` and
  `WellFormed` use the actual launch block. New reads use the integer register
  update/invalidation rules and preserve disjoint integer/float banks.
- Geometry evidence: `Scalar/Geometry.lean` proves coverage and injectivity of
  CTA-coordinate times block-size plus thread-coordinate, and uniqueness of
  row-major output indices for valid 2-D launches. These mathematical theorems do
  not silently prove that the actual u32 multiply/add sequence cannot wrap.
- Actual required case: `scalar_matmul.ptx` mechanically generates 43 checked
  instructions over row-major f32 matrices, runtime M/N/K, masked edge threads,
  explicit zero initialization and an FMA loop that handles K=0. The independent
  specification in `ScalarMatmulSpec.lean` uses the source accumulation order.
  Rust tests inspect loop/back-edge/exit PCs in addition to type/qualifier rejection.
- Execution evidence: a concrete row=1, col=1, N=3, K=0 run completes without any
  load query for EVERY oracle, writing zero to C+16. A K=2 run checks four actual
  read addresses and oracle values 2,3,5,7, then writes 41 to that output address.
  These are local interpreter traces, not global consistency witnesses, GPU runs
  or a proof for arbitrary dimensions/K.
- Reusable memory rules: `Scalar/Memory.lean` derives immutable real-load values
  from actual represented initialization, eligibility and absence of writers;
  its observed-real-write rule uses actual write events, unique writers and
  observer eligibility. The existing float-literal universal contract now reuses
  this write rule and readback rule, with no new correctness premise.
- Negative evidence: frontend rejects wrong widths/destinations, unknown axes,
  unsupported special registers, direct special-register arithmetic operands and
  floating/predicated special reads. A unit-block local trace is proved produced
  and then rejected under a two-thread launch whose ntid.x differs, including
  through launch-wide well-formedness. Scalar register-bank preservation and the
  original integer embedding/Copy/SharedSwap regressions are retained.
- Remaining duties at that stage: matmul was marked partial. The actual
  arbitrary-K loop invariant, fixed-width index/address bounds, complete
  launch-wide consistency/observation witnesses and universal output contract
  still needed proofs. The following record closes the inner-loop execution
  and completed-suffix reconstruction obligations only.
  FMA's global contract, all later required cases, full PTX/model correspondence,
  allocation/UB and runtime connection remain in the original active goal.
- Research/performance boundary: baseline semantics/proof infrastructure; no new
  optimization or reusable proof-method novelty is claimed. Exact logits/token
  equality is unchanged; exact-real arithmetic is not IEEE/GPU bit-equality.
  No optimization benchmark or manual/agent-cost measurement was performed.
- Validation on 2026-11-04: full checks passed with 18 Rust tests, 9 regenerated
  AST comparisons, 673 audited Lean declarations and 23 false claims rejected.
  Updated coverage metadata and whitespace checks passed. PTX assembly was
  skipped (`ptxas` not configured). A fresh `nvidia-smi -L` check still failed
  with a driver/NVML library mismatch (NVML 580.178), so no GPU execution or
  differential result is claimed.

## Research record: parametric actual matmul loop and arbitrary completed suffixes

- Existing limitation: typed PTX, an independent matrix recurrence, index lemmas
  and concrete K=0/K=2 runs did not prove the runtime inner loop for arbitrary K.
  A single chosen input oracle or fuel value would not establish universal
  completed-trace behavior, and exact register-list shapes would obstruct reuse
  with actual initialization and unrelated bindings.
- Implemented method: `Scalar/Updates.lean` provides checked mixed-bank register
  update normal forms and modular arithmetic facts. The loop invariant names
  live values, PC, query count and bank disjointness while allowing arbitrary
  unrelated bindings. Each step is justified against the actual generated PTX
  through the fixed interpreter's integer/load/FMA/store rules.
- Loop evidence: `ScalarMatmulLoop.lean` proves one nine-instruction iteration,
  preserving the accumulation recurrence, both pointer expressions and counter.
  Pointer arithmetic uses the actual modulo-2^64 semantics; bounds are required
  for active load addresses, not for an unused pointer after the final iteration.
  A four-instruction exit proves final store, completion and query count. Induction
  constructs the suffix for every remaining iteration count, including K=0, with
  an explicit read-event list and final output equal to `prefixProduct`.
- Universal reconstruction: a successful completed run must execute a next step
  after each successfully produced running prefix. The actual load step yields
  its typed f32 reply. Induction extracts ALL remaining replies from arbitrary
  oracles, instruction counts and completed traces. Completed-run uniqueness then
  fixes the suffix length (9*K+4 from loop entry), emitted addresses/values and
  final accumulator. The helper used to name real replies cannot admit an
  integer or wrong-format reply via its default value.
- Reuse/evidence: the reusable prefix/step, load-reply and run-composition rules
  connect the original interpreter to symbolic block proofs. Tests prove the
  actual 32-instruction initialization prefix at one fixed matrix/address
  instance, and compose the loop proof with it for ALL real matrix data, retaining
  the actual extra register bindings. Generic K=0 accepts every oracle without
  querying it. Negative proofs reject an integer first reply and an f16 reply in
  the second iteration for every possible successful completed count. A near-2^64
  input checks that the unused one-past pointer may wrap to zero after a valid read.
- Remaining duties at that stage: these were local loop-execution and
  reconstruction results, not the matmul acceptance contract. General source
  initialization, edge masking, coordinate/layout and byte-footprint bounds, input
  representation/eligibility under the memory model, launch-wide output/frame,
  complete consistency/observation witnesses, allocation/UB and GPU tests remain.
  FMA's global contract and all later parity cases remain in the unchanged active
  goal. Typed local replies are not assumptions that matrix inputs were read
  correctly; that separate global memory proof is still required.
- Research/performance boundary: baseline proof infrastructure, with no new
  optimization, proof-method novelty, speedup or numerical/IEEE/GPU bit-equivalence
  claim. The exact logits/token requirement is unchanged. No optimization benchmark
  or manual/agent-cost measurement was performed.
- Validation on 2026-11-04: full checks passed with 18 Rust tests, 9 regenerated
  AST comparisons, 711 audited Lean declarations and 23 deliberately false
  claims rejected. The new loop modules and nine regression theorems passed;
  coverage metadata and whitespace checks passed. PTX assembly was skipped
  (`ptxas` not configured); no GPU execution or differential result is claimed.

## Research record: parameterized source entry, masking and full thread traces

- Existing limitation: the arbitrary-K loop theorem required an entry invariant.
  A concrete initialization prefix did not justify arbitrary runtime dimensions,
  CTA coordinates/shapes, thread coordinates or parameter environments. Component
  widths alone could not justify the source's u32 index multiply/add sequence.
- Implemented method: `ScalarMatmulInput.lean` separates typed runtime values,
  flexible parameter lookup, component widths and coordinate-product bounds.
  Index bounds are derived for valid threads in geometries with bounded dimensions
  and covered coordinate extents. `ScalarMatmulInit.lean` proves the actual first
  16 source instructions, including runtime ctaid/ntid/tid reads and exact indices.
  Each step is checked through the same fixed scalar semantics and source AST.
- Guards: the reusable `Scalar.Control.ge_branch_run` rule keeps both outcomes of
  the actual setp.ge/conditional-branch pair. `ScalarMatmulGuards.lean` proves
  row/column masking, actual return and zero emitted memory events/queries, for
  arbitrary load oracles. Row masks take 19 source steps; column masks take 21.
- Initialization and composition: `ScalarMatmulAddress.lean` checks the actual
  12-instruction address/stride/accumulator block. Modular arithmetic preserves
  the real source's u64 intermediate expressions; the result establishes the
  existing loop invariant. `ScalarMatmulThread.lean` composes the PC=0 prefix and
  arbitrary-K loop for all runtime dimensions and threads satisfying the stated
  width/address bounds. Active execution takes 36+9*K steps and emits the specified
  local dot-product trace. Separate reconstruction classifies EVERY successful
  completed source run into row-masked, column-masked or active cases, with no
  oracle or instruction count chosen as an assumption.
- Reuse/negative evidence: generic run splitting/composition and the same integer,
  special-register, FMA and register-bank rules connect all blocks. Tests use a
  2-D CTA/grid position, arbitrary u32-bounded K and real matrices, and an arbitrary
  unrelated parameter in a reordered environment. Exact row/column edge masks
  emit no memory events for every oracle. An actual source prefix with individually
  representable components wraps mathematical column 2^32 to zero; its index-bound
  certificate is rejected. The coordinate-product premise is retained explicitly.
- Remaining duties at that stage: this closed local source entry and masking, not the matrix
  acceptance contract. AddressBounds currently constrain starts of active accesses,
  not entire f32 byte footprints or allocation. Whole-launch region/layout duties,
  matrix input representation and eligibility, initial-value agreement, output/frame
  correctness, complete consistent execution/observation witnesses, full PTX/model
  correspondence and GPU evidence remain. FMA's global contract and all later
  parity cases remain in the original active goal.
- Research/performance boundary: baseline semantics/proof engineering, with no
  optimization, new proof-method novelty, numerical/IEEE/GPU bit-equivalence or
  speedup claim. The exact logits/token requirement is unchanged. No optimization
  benchmark or manual/agent-cost measurement was performed.
- Validation on 2026-11-04: complete checks passed with 18 Rust tests, 9 regenerated
  AST comparisons, 743 audited Lean declarations and 24 false claims rejected.
  Nine new initialization regressions cover arbitrary-K/data/extra parameters,
  completed counts, masked edges and actual coordinate wrap. Updated coverage
  metadata and whitespace checks passed. PTX assembly was skipped (`ptxas` not
  configured); no GPU execution or differential result is claimed.

## Research record: universal scalar matmul matrix-memory and output contract

- Existing limitation: full-source local traces did not connect load replies to
  initialized matrices or ensure legal byte footprints, unique output ownership,
  race freedom or observer output. Prescribing correct replies would hide that gap.
- Implemented method: `Scalar/Regions.lean` provides reusable four-byte word-region
  and disjointness rules, including empty regions. `ScalarMatmulConfig.lean` states
  bounded/covering 2-D geometry, u32 coordinate extents, complete u64 matrix ranges,
  four-byte alignment and C separation from nonempty input regions. Read-only A/B
  aliasing is allowed when both initial representations hold. No correctness,
  eligibility, no-race or chosen-reply hypothesis is added to the precondition.
- Source/model connection: every actual completed candidate event is classified
  as an A read, B read or uniquely owned C write, with exact serial/address/payload.
  `ScalarMatmulEvents.lean` derives all four byte bounds and alignment.
  `ScalarMatmulMemory.lean` derives race freedom for every reads-from witness and
  proves inputs and locations outside C unwritten. `ScalarMatmulInputs.lean`
  reuses immutable real-load rules to force arbitrary replies to matrix values.
- Universal contract: `ScalarMatmulOutput.correct` proves the independent matrix
  recurrence for every output cell plus preservation of every observed byte
  outside C, for all complete provenance-checked candidates and permitted memory/
  observer witnesses. Geometry coverage supplies every output owner. It does not
  prescribe trace order, load oracle, instruction count or coherence witness.
- Regression/reuse evidence: a 3x3x2 configuration uses a 2x2 grid of 2x2 CTAs,
  with 9 active and 7 masked threads. Under the contract, the observed C[0,0] is
  12 for constant input matrices 2 and 3; a nonzero frame byte is preserved. Lean
  rejects wrong output 11, zeroed frame and overlapping nonempty input/output
  regions, while allowing an empty K=0 input to share C's base. These are universal
  conditional regression theorems, not a constructed global execution or GPU run.
- Remaining duties at that stage: the separate complete consistent global
  execution/observation existence proof was pending, so scalar matmul remained partial. Physical
  allocation/UB, full PTX/observer correspondence, assembly/GPU differential
  evidence and all later parity cases remain in the unchanged active goal.
- Research/performance boundary: reusable baseline proof engineering; no new
  optimization, proof-method novelty, speedup, IEEE arithmetic or GPU bit-equality
  claim. Exact logits/token requirements are unchanged. No optimization benchmark
  or manual/agent-cost measurement was performed.
- Validation on 2026-11-04: full checks passed with 18 Rust tests, 9 regenerated
  AST comparisons, 796 audited Lean declarations and 24 false assertions rejected.
  The new matrix-memory regression module passed. PTX assembly was skipped
  (`ptxas` not configured); no GPU execution or differential result is claimed.

## Research record: complete consistent scalar matmul launch and observation

- Existing limitation: a universal output contract could still be vacuous. Local
  active/masked completion did not supply a duplicate-free, complete launch graph,
  valid bytewise reads-from/coherence or permitted final observation.
- Implemented method: reusable `ISA/Enumeration.lean` enumerates arbitrary 3-D
  geometries with exact validity membership and no duplicate thread identities.
  `ScalarMatmulCandidate.lean` reuses actual PC=0 active/masked source completion
  for each valid thread, retaining the actual input oracle and complete final
  register state. Classical choice selects already-proved completed runs; no
  completion, memory consistency or matrix correctness is assumed as a new axiom.
- Memory/observation evidence: `ScalarMatmulWitness.lean` chooses initial reads-from
  only for this existence witness. Actual input encodings agree with initialized
  matrix bytes; no input byte is written. Existing writer uniqueness and absent
  barriers supply a valid initial-before-write coherence witness. Generic
  `writerSelector`/`unique_writers_observation` rules select actual emitted writers
  per byte, preserving the initial map elsewhere, for any requested global domain.
  A separate parameterized `Scalar.Nonvacuous` theorem covers every admissible
  M/N/K, bounded 2-D geometry, flexible parameter environment and represented
  initial map. Universal correctness continues to quantify over arbitrary replies
  and memory witnesses.
- Regression/reuse evidence: the 3x3x2 configuration now has a complete consistent
  execution/observation witness that observes C[0,0]=12 and the nonzero frame byte.
  A second configuration has K=0 and A=B=C, requires no input representation,
  starts with nonzero output-region bytes and has a permitted completed execution
  observing zero. An incorrect A-load reply of 17 cannot satisfy memory conditions.
  This reuses source completion, immutable-input reasoning and the same generic
  coherence/observer predicates used by integer Copy/SharedSwap.
- Remaining duties: this closes matmul's universal correctness and nonvacuity
  under the current symbolic-real/ordinary-memory projection. Scalar matmul remains
  partial in the broader inventory because physical allocation/UB, full PTX/
  observer correspondence and assembly/GPU differential evidence remain open.
  Nonvacuity does not prove all-schedule termination or CUDA runtime correctness.
  Atomics/shuffle, FlashAttention/MoE, Ampere/Hopper, stream composition and the
  Iris/runtime connection remain in the unchanged active goal.
- Research/performance boundary: baseline proof engineering with reusable rules;
  no new optimization, proof-method novelty, speedup, IEEE or GPU bit-equality
  claim. Exact logits/token requirements are unchanged. No optimization benchmark
  or manual/agent-cost measurement was performed.
- Validation on 2026-11-04: the complete verifier gate passed (18 Rust tests,
  9 regenerated AST comparisons, full Lean build and 24 deliberately false claims
  rejected). After adding the new theorem audit entries, a separate complete Lean
  dependency audit checked all 822 declarations against the same foundational
  axiom whitelist. The 3x3x2 existence/output/frame, wrong input reply and K=0
  aliasing/output regressions compiled. Coverage metadata and whitespace checks
  passed. PTX assembly was skipped (`ptxas` not configured); no GPU execution
  or differential result is claimed.

## Research record: true scoped RMW events and atomic-dispatch source entry

- Existing limitation: ordinary reads and writes were exclusive event kinds, and
  moral strength required a single thread. Treating a GPU atomic as a weak load
  and later store would lose its scope and indivisible read/write relationship.
  A fixed ticket assignment would assume the dispatch property to be proved.
- Implemented method: `ISA/Scope.lean` describes CTA/GPU/system inclusion in the
  current single-device model. A true `Kind.rmw` carries scope and before/after
  payloads with equal length by construction. The scalar interpreter evaluates
  address/increment before destination assignment, queries one integer reply,
  normalizes it to u32, emits one RMW event and increments the query count.
  Existing mixed-bank invalidation is preserved. The prior read/write-exclusivity
  helper now requires a no-RMW premise; Copy/SharedSwap/matmul derive that fact
  from their actual source traces rather than assuming it.
- Frontend/source evidence: the two explicit qualifier spellings of relaxed
  GPU-scoped global u32 atomic add translate to typed scalar data. Unmodeled scopes,
  semantics, operations, widths, predication and bad operands fail closed. The
  actual 15-instruction `atomic_dispatch.ptx` has a Lean type certificate and a
  source-prefix theorem for arbitrary u64 addresses, flexible parameter bindings,
  contexts and integer oracle replies. Full source runs check tickets 0 and 1,
  locally possible 17, increment overflow and large oracle-value normalization.
  Destination/increment aliasing and real-reply rejection are checked separately.
- Common memory extension: scope-bearing events participate in moral strength
  only when both scopes include the peer thread and footprints match. Observation
  order may traverse RMWs, while relaxed observation does not automatically create
  cross-CTA base causality. RMW atomicity is an additional field of the SAME
  `GenericMemoryConditions`; source, coherence, races, single-copy atomicity,
  SC-per-location and observer conditions remain shared. Event-view transport and
  generic witnesses were extended. No-RMW strength/observation reductions are
  proved, and all existing kernel proofs are checked under the extended model.
- Consequences/nonvacuity: `Event/AtomicRules.lean` derives self-sourcing rejection
  from SC-per-location and excludes two mutually scoped RMWs both sourcing
  initialization, using coherence's chosen order. It does not assume which CTA
  goes first. The unsplit representation excludes the internal read-to-own-write
  step from inter-operation from-read edges; reads-from-self remains represented.
  `Tests/AtomicMemory.lean` independently checks actual two-instruction provenance,
  a well-formed complete one-thread launch, ALL memory conditions and a permitted
  observation of counter=1 from initialization zero. This positive case guards
  against excluding every RMW through a spurious self cycle. Full correspondence
  to PTX and to a split-RMW presentation remains open; the representation choice
  is not reported as such a correspondence proof.
- Remaining duties at that stage: atomic dispatch remained partial. General completed branch
  reconstruction, bytewise ticket uniqueness, universal counter=2/x=1/y=2 plus
  frame, and two-CTA complete consistent execution/observation witnesses remain.
  The single-RMW positive case does not substitute for them. Acquire/release,
  other atomic forms, cluster scope, shuffle and all later parity cases remain
  in the unchanged goal. No physical allocation/UB, PTX assembly or GPU evidence
  is established by local traces or by the consistency predicates alone.
- Research/performance boundary: baseline semantics/proof engineering and reusable
  atomic reasoning rules. No optimization, proof-method novelty, speedup, IEEE or
  GPU bit-equality claim. The exact logits/token target is unchanged; no
  optimization benchmark or manual/agent-cost measurement was performed.
- Validation on 2026-11-04: the complete verifier gate passed with 20 Rust tests,
  10 regenerated AST comparisons, full Lean build, 876 audited declarations and
  26 deliberately false assertions rejected (including atomic float destination
  and narrow pointer). New source, aliasing/wrap, single-RMW well-formedness,
  consistency, completion, observation and self-read regression theorems passed.
  `cargo fmt --check`, coverage metadata and whitespace checks passed. PTX
  assembly was skipped (`ptxas` not configured); no GPU/differential result.

## Research record: arbitrary dispatch branches and bytewise ticket uniqueness

- Existing limitation: selected local runs for replies 0/1/17 did not justify all
  completed source executions. The initial atomic rules alone did not exclude
  mixed-size/tainted reads from actual dispatch candidates or prove both returned
  tickets, and prescribing a uniform u32 source would assume a missing property.
- Local method: a reusable fixed-interpreter integer-store rule and equality/
  branch rule keep both branch outcomes. `AtomicDispatchBody/Thread.lean` prove
  the actual full 15-instruction source for arbitrary contexts, u64 parameters,
  integer replies and unused oracle answers. Reconstruction extracts a typed
  first reply from every completed run and fixes its final state, emitted events
  and count: 11 steps for normalized ticket 1, 10 otherwise. Real replies cannot
  yield a completed run for any count. The no-job path is retained.
- Layout/provenance: a separate Config describes three separated/aligned four-byte
  cells with full u64 bounds and the two-CTA geometry. The only initialized value
  required is counter=0. An independent counter=2/x=1/y=2 plus frame specification
  is stated. Event reconstruction derives each counter RMW and conditional job
  write from actual source traces. Reusable footprint bounds account for both
  equal-length RMW projections. Layout derives mixed-size exclusion and counter
  eligibility without assuming that output writes are already race-free.
- Memory method: coherence at one byte chooses the order of the two actual RMWs.
  The new generic SC-per-location rule excludes reading the later modification
  at ANY shared byte, and the existing self-source rule excludes one's own write.
  Source-derived writer inventory forces the first RMW to read initialization
  on each byte. The generic cross-byte RMW rule forces the second to read the
  first modification on every byte. Integer-fragment reconstruction then proves
  the two normalized tickets are {0,1}, in either order, for arbitrary complete
  candidates, oracles, counts and reads-from/coherence witnesses. No fixed CTA
  assignment, uniform source, inter-CTA causality or global no-race premise is
  introduced. These are baseline rules, not a novelty claim.
- Regression/reuse evidence: `AtomicDispatchCandidate.lean` constructs complete
  local two-CTA candidates for ANY integer reply assignment and flexible runtime
  parameter bindings. `Tests/AtomicDispatch.lean` instantiates an admissible layout
  with reordered parameters and an unrelated binding. Every constant reply
  assignment is locally well-formed/complete but inconsistent for EVERY memory
  witness. It also checks that any completed ticket-1 source run takes 11 steps
  and any real first reply precludes completion. False claims that ticket 1 takes
  10 steps or that a valid u64 start suffices for a complete four-byte footprint
  are included in the rejection gate.
- Remaining duties at that stage: atomic dispatch remained partial. The final universal counter/
  output/frame contract and separate legal complete two-CTA execution/observation
  witnesses are still pending. Local candidate construction and negative
  consistency do not substitute for them. Full PTX/observer correspondence,
  physical allocation/UB and assembly/GPU differential evidence remain open, as
  do acquire/release, other atomic/shuffle forms and all later original goal items.
- Research/performance boundary: baseline semantics/proof engineering and reusable
  rules; no optimization, proof-method novelty, speedup, IEEE or GPU bit-equality
  claim. Exact logits/token requirements remain unchanged. No optimization
  benchmark or manual/agent-cost measurement was performed.
- Validation on 2026-11-04: complete checks passed with 20 Rust tests, 10
  regenerated AST comparisons, full Lean build, 931 audited declarations and
  28 deliberately false assertions rejected. New arbitrary-source completion/
  reconstruction, ticket, local-candidate and consistency-rejection theorems are
  included in the audit. Coverage metadata and whitespace checks passed. PTX
  assembly was skipped (`ptxas` not configured); no GPU execution/differential
  result is claimed.

## Research record: universal atomic-dispatch output and repeated-write witnesses

- Existing limitation: bytewise ticket uniqueness did not yet prove job output,
  the final counter modification or frame preservation. The observer rule for a
  unique writer could not select between two counter modifications. The earlier
  initial-coherence constructor required at most one writer per byte and a
  strict read-to-write ranking inappropriate for an unsplit RMW's own update.
- Universal method: `AtomicDispatchAssigned.lean` derives the two actual traces'
  job assignment from source coverage, unique thread identities and the ticket
  theorem; it is not a launch premise. It reconstructs the four events, including
  both RMWs. `OutputMemory` derives unique x/y writers, untouched frame and byte
  observer eligibility. No global race-free property is assumed.
- Latest counter: the second RMW's byte-zero source must be the first RMW. Initial
  bytes disagree and self-sourcing is forbidden. Coherence comparison at any other
  byte plus SC-per-location prevents reversing this order. A generic
  `observer_latest_writer` rule excludes all earlier modifications, including
  initialization, without discarding any actual counter writer.
- Contract: `AtomicDispatchOutput.correct` establishes the independent u32
  counter=2/x=1/y=2 postcondition plus equality to the arbitrary fixed initial map
  at every observed byte outside the three cells. It quantifies over all complete
  source candidates, oracles, counts, trace-list orders, memory witnesses and
  permitted observations under the existing layout/initialization precondition.
- Constructive groundwork: `RankedWitness.lean` proves a sufficient constructor
  for repeated writes and RMWs under the SAME memory predicates, using actual
  values/edge ranks, write-rank injectivity and race exclusion. Distinct-operation
  from-read edges are ranked; no rank(event)<rank(event) obligation is imposed
  on an RMW's own update. `RankedObservation.lean` selects a rank-maximal actual
  writer per byte from a checked complete finite inventory, preserving the
  initial fallback elsewhere. These duties certify a chosen witness and do not
  restrict the allowed executions in the universal contract.
- Regression/reuse evidence: a concrete dispatch domain observes all 256 global
  bytes, with only the counter initialized to zero and other bytes set to 165.
  The contract checks output bytes 2/1/2 and rejects a stale counter value 1, a
  wrong job value and zeroed frame. These are conditional regression theorems,
  not a two-CTA existence witness. Separately, the ranked constructors admit an
  actual well-formed completed single-RMW source and an observation of 1. This
  uses the existing source/memory instance to guard against vacuous RMW rules.
- Remaining duties at that stage: atomic dispatch remained partial until the separate legal
  complete two-CTA execution/observation witness is constructed for every
  admissible launch. The single-RMW instance does not substitute for that
  obligation. Full PTX/observer correspondence, physical allocation/UB and
  assembly/GPU differential evidence remain open, as do all later original goal
  items. No requested acceptance case or proof boundary is removed.
- Research/performance boundary: reusable baseline proof engineering. No new
  optimization, proof-method novelty, speedup, IEEE or GPU bit-equality claim.
  The exact logits/token target is unchanged. No optimization benchmark or
  manual/agent-cost measurement was performed.
- Validation on 2026-11-04: the complete verifier gate passed with 20 Rust tests,
  10 regenerated AST comparisons, full Lean build, 975 audited declarations and
  28 deliberately false assertions rejected. New universal dispatch output/frame
  and latest-counter proofs, three conditional output/frame rejection regressions,
  ranked consistency/observation rules and their single-RMW positive instance all
  compiled and passed the dependency audit. Coverage metadata and whitespace checks
  passed. PTX assembly was skipped (`ptxas` not configured); no GPU execution or
  differential result is claimed.

## Research record: independent two-CTA dispatch consistency and observation

- Existing limitation: the universal counter/output/frame contract could still be
  vacuous for the two-CTA kernel. Local complete candidates and the ranked
  constructor's single-RMW instance did not establish consistency for two
  modifications, their job writes and a permitted final observation.
- Source/race method: `AtomicDispatchRace.lean` reuses source event reconstruction
  and layout to show all reads access the counter, while x/y accesses are writes.
  A source-checked assignment yields unique job writers and morally strong
  counter RMWs, excluding races without a memory-consistency premise. The
  assignment used for the existence proof is constructed from actual local
  source runs with chosen replies; it is not obtained from the consistency
  theorem or added to the launch precondition.
- Consistency construction: `AtomicDispatchWitness.lean` chooses reads-from
  initialization for the first RMW and from its actual write for the second.
  The initial counter representation and emitted bytes justify every read
  value. It proves monotone program/control edges, injective ranks of actual
  writers, strict reads-from ranks and distinct-operation from-read ranks.
  Reusing `ranked_co_conditions` then discharges ALL common memory predicates,
  including RMW atomicity. The internal RMW read/write does not need a strict
  self-rank edge. No consistency or desired postcondition is assumed.
- Observation/reuse: the proven complete four-event inventory feeds the existing
  rank-maximal byte-writer selector, yielding the SAME observer conditions and
  preserving arbitrary fixed initial bytes outside writes. The generic
  construction works with either job assignment. Canonical actual-source
  candidates choose either CTA as the first RMW, and parameterized nonvacuity
  covers every admissible layout, flexible parameter environment and initial
  symbolic map satisfying only counter=0. The universal contract continues to
  quantify over every consistent complete candidate.
- Regression evidence: both CTA orders have well-formed COMPLETE source
  candidates, memory witnesses and permitted observations at the concrete
  admissible launch. Combining these independent existence results with the
  universal contract observes 2/1/2 and the nonzero frame byte 165. These
  replace neither execution tests on real hardware nor full PTX correspondence.
- Remaining duties: atomic dispatch now has universal correctness, separate
  global nonvacuity and concrete positive/negative regressions under the current
  model. Its broader inventory status remains partial because full PTX/observer
  correspondence, physical allocation/UB and assembly/GPU differential evidence
  remain open. Nonvacuity is not all-schedule termination. Acquire/release,
  additional atomic/shuffle forms, FlashAttention/MoE, Ampere/Hopper, stream
  composition and Iris/runtime connections remain in the unchanged full goal.
- Research/performance boundary: reusable baseline semantics/proof engineering;
  no new optimization, proof-method novelty, speedup, IEEE or GPU bit-equality
  claim. The exact logits/token target is unchanged. No optimization benchmark
  or manual/agent-cost measurement was performed.
- Validation on 2026-11-04: complete checks passed with 20 Rust tests, 10
  regenerated AST comparisons, full Lean build, 995 audited declarations and
  28 deliberately false assertions rejected. Parameterized independent
  consistency/nonvacuity, both CTA-order positive witnesses, output/frame
  observations and the reused race/region rules compiled and passed the audit.
  Coverage metadata and whitespace checks passed. PTX assembly was skipped
  (`ptxas`/`nvcc` unavailable on PATH). Fresh hardware diagnostics found an NVML
  driver/library mismatch (library 580.178); CUDA `cuInit(0)` returned 804,
  reported by the driver as `CUDA_ERROR_COMPAT_NOT_SUPPORTED_ON_DEVICE` /
  forward compatibility attempted on unsupported hardware. No GPU execution
  or differential result is claimed, and no driver modification was attempted.

## Research record: scalar online attention invariant and actual arithmetic blocks

- Instance: `scalar_flash_attention.ptx` computes one output element per thread
  of a 2-D grid, with runtime key/dimension loops and online normalization.
  This 76-instruction scalar baseline targets the paper's attention capability;
  it does not copy an unavailable paper artifact or claim an optimized kernel.
- Existing limitation: the eight-form float frontend lacked subtraction,
  maximum, exponential and division. Scalar matmul's additive prefix invariant
  did not express the changing scale of online softmax's numerator/denominator.
  Existing global memory rules were not missing a new memory qualifier here.
- Reusable method: `RealMath.lean` explicitly abstracts ex2 by exp(log(2)*x).
  `AttentionSpec.lean` states natural-exp attention independently;
  `OnlineSoftmax.lean` proves both rescaled prefix sums, preservation under each
  update, a positive nonempty normalizer and normalization equivalence for
  arbitrary real score/value functions and finite lengths. The source's scale
  obeys alpha=log(2)*scale, so no rounded log2(e) literal is treated as exact.
  First-score initialization avoids a negative-infinity sentinel. Empty key
  rows have the explicit output-zero convention.
- Source connection: four fixed f32 forms extend the shared typed frontend and
  interpreter; generic bank-disjointness and the integer conservative-extension
  proofs still compile. Register aliases are allowed. Exact arithmetic rules
  prove the ACTUAL generated source's three initialization instructions, nine
  rescaling instructions, and division/store/return tail for arbitrary entry
  bindings. The tail's nonzero divisor follows from the prefix invariant.
  Division by zero faults as outside this finite-real fragment, not as an IEEE
  result. The whole source still must be shown to establish that invariant;
  block entry conditions are not new launch preconditions.
- Regression/reuse evidence: new maximum 1 after initial score/value 0/4 and
  next score/value 1/10 yields normalizer=3/2, accumulator=12 and output=8.
  This is checked both mathematically and on the actual nine-instruction block.
  Tests also cover arbitrary single-key values and equal scores, positivity,
  division-by-zero rejection and independent attention equivalence. Actual
  entry-to-return tests cover N=0 and row/column masks for every reply oracle,
  proving completion without any input/scale reads on those paths. Frontend
  tests preserve branch targets and reject unsupported modifiers, operands and
  types; separate negative Lean attempts check ex2/max register-type errors.
- Remaining duties: arbitrary completed source reconstruction through nested
  loops, initial Q/K/V/scale read correspondence, bounded geometry and complete
  byte layout/race duties, all-candidate output/frame correctness and independent
  complete consistency/observation witnesses. This acceptance case stays partial.
  The new math/block theorems do not establish those obligations, full PTX
  correspondence, allocation/UB freedom or GPU execution. All later original
  goal items remain unchanged.
- Research/performance boundary: reusable baseline semantics/proof engineering,
  with 498 lines across the new math/spec/block/test files plus shared interpreter,
  typing and arithmetic-rule changes. This is not a new proof-method or speedup
  claim. No optimization benchmark, GPU bit-equality check or manual/agent-cost
  measurement was performed; the original exact logits/token target is unchanged.
- Validation on 2026-11-04: complete checks passed with 23 Rust tests, 11
  regenerated AST comparisons, full Lean build, 1049 audited declarations and
  30 deliberately false assertions rejected. Coverage metadata and whitespace
  checks passed. PTX assembly was skipped because ptxas is unavailable; no GPU
  execution or differential result is claimed. The previously diagnosed CUDA
  driver/runtime failure remains an external test limitation.

## Research record: actual attention dot loop and register frames

- Existing limitation: the online invariant and arithmetic blocks did not prove
  that the PTX dot-product loop completes with the expected score, nor preserve
  the outer softmax/scale state across integer control instructions and loads.
  Cross-bank invalidation means silently treating the integer and float register
  maps as independent would lose a semantic obligation.
- Method: `Scalar/RegisterFrame.lean` frames BOTH register banks outside a
  changed-name list. Integer updates/control preserve unrelated float slots
  under the established bank-disjointness invariant; float updates invalidate
  same-name integer slots and frame the rest. Frame composition is generic.
  These are local register facts, not a memory permission or a global frame.
- Actual source proof: `ScalarAttentionDot.lean` proves the nine-instruction dot
  iteration at PCs 43--51, loop exit at PCs 43/44, and induction over remaining
  iterations. It derives `9*D+2` steps to PC 52, `2*D` load events, arbitrary
  initial oracle-query offsets and the exact symbolic dot product. The actual
  scale multiply extends this to `9*D+3` steps/PC 53 and scale*dot. Read addresses
  have explicit start bounds; unused one-past pointers keep u64 modular behavior.
  Full byte/physical allocation bounds are separate. Oracle hypotheses specify
  a chosen local run; they do not assume global read-value correspondence.
- Reuse/regressions: both dot iteration/exit and softmax initialization/update
  reuse the same register-frame rules. Dot frames preserve arbitrary outer
  scale/max/normalizer/accumulator, output/index/extra registers. Tests exercise
  the actual final aligned u64 word followed by unused-pointer wrap to zero,
  query offset 7, arbitrary real data and retained outer state. D=0 completes
  the internal loop without reads for every oracle; this is not a claim that
  the full masked D=0 kernel reaches that loop. A separate source test checks
  the scale multiply at PC 52 against independent dot semantics.
- Remaining duties: entry/outer-loop execution, reconstruction of EVERY
  successful complete candidate without selecting its replies/count, Q/K/V/scale
  initial-read correspondence, byte layout/race/UB duties, universal global
  output/memory-frame correctness and independent complete memory/observation
  witnesses. Forward local completion does not discharge those obligations or
  establish GPU execution. The attention acceptance case and full goal remain
  partial/active; no acceptance requirement is removed.
- Research/performance boundary: baseline proof engineering, not a new
  optimization or novel ownership method. The new frame/dot/test files add 534
  lines, plus two softmax-block frame rules. Lean reported 4.1 seconds to check
  the dot module with cached dependencies; this is not an end-to-end timing.
  No benchmark, IEEE/bit-equality
  claim or manual/agent-cost measurement was performed; exact logits/token
  requirements are unchanged.
- Validation on 2026-11-04: complete checks passed with 23 Rust tests, 11
  regenerated AST comparisons, full Lean build, 1076 audited declarations and
  30 deliberately false assertions rejected. Parameterized dot completion,
  scaled-score correctness, register frames, final-word/wrapping and zero-D
  regressions all compiled and passed the dependency audit. Coverage metadata
  and whitespace checks passed. PTX assembly was skipped (ptxas unavailable);
  no GPU execution or differential result is claimed. Existing CUDA runtime
  diagnostics remain an external test limitation; no driver changes were made.

## Research record: source-local nested attention loop through store/return

- Existing limitation: parameterized dot and arithmetic-block proofs did not
  compose the actual outer key loop, distinguish uninitialized first-item state
  from later updates, advance K/V/index state or justify reaching normalization.
  The previous turn made concrete proof/test progress; it was not a wait or a
  status-only continuation.
- Method/source connection: `ScalarAttentionOuterUpdate.lean` proves PCs 53--68
  for both branches: six instructions for the first item and thirteen later.
  `ScalarAttentionOuter.lean` proves the loop guard/dot preparation, reuses the
  actual dot-loop/scale proof, loads V, selects initialization/update, and advances
  pointers/index back to PC 37. The register-frame monotonicity rule composes
  existing frame certificates without forgetting cross-bank invalidation.
- Initialization/invariant: the loop invariant requires softmax registers only
  when the current index is nonzero. The actual first-item path establishes them
  from its score/value; no caller preinitialization is added. An explicit test
  proves max/l/u are absent at the actual PC 37 state. Later iterations preserve
  the online-prefix state. Guard exit then derives a positive divisor from that
  invariant and reuses the actual normalization/store/return proof.
- Completion/specification: induction on remaining keys derives all iteration
  counts and input events, with query index firstQuery+(2*D+1)*j including the V
  load. From PC 37, N>0 takes N*(9*D+26)-2 instructions and stores the independent
  natural-exp attention output with alpha=log(2)*scale. The positive-key premise
  describes this loop entry; N=0 remains the source's separate early-store path,
  whose existing full-source regression is retained. Layout hypotheses bound
  read starts, not complete physical allocation/UB safety.
- Concrete evidence: the actual N=2/D=1, unit-CTA PC=0 source prefix initializes
  runtime state and reads scale. The proven nested suffix then completes the
  whole source in 105 instructions with seven input reads and output 8. It covers
  first initialization, subsequent update and a changed maximum, with explicit
  Q=1, K=[0,1], V=[4,10], base-2 scale=1. The independent natural-exp spec yields
  8 separately. Negative proof attempts reject counting the first item as a later
  update (75 rather than 68 suffix steps) and omitting the V load from the next
  query index (3 rather than 4). The corrected missing-V assertion was also
  checked independently after the complete gate.
- Remaining duties: general PC=0 parameter/geometry/guard/address initialization,
  reconstruction of arbitrary successful complete source candidates without
  selecting their replies/counts, initial Q/K/V/scale read correspondence, full
  byte layout/race/UB duties, the all-candidate global output/memory-frame
  contract and independent complete consistency/observation witnesses. Local
  completion under explicit reply hypotheses is not global nonvacuity. The
  concrete full-source run is not a parameterized PC=0 or global-memory theorem.
  All remaining original goal capabilities and acceptance cases remain intact.
- Research/performance boundary: baseline proof engineering, not a new
  optimization, ownership method or speedup. The three new outer-loop/test files
  add 642 lines plus a generic register-frame rule. With cached dependencies,
  Lean reported 2.5 seconds for the outer module and 2.7 seconds for its initial
  test build (3.7 seconds when rebuilt by the final gate). No optimization
  benchmark, IEEE/GPU bit-equality check or manual/agent-cost measurement was
  performed. Exact logits/token requirements are unchanged.
- Validation on 2026-11-04: complete checks passed with 23 Rust tests, 11
  regenerated AST comparisons, full Lean build, 1096 audited declarations and
  32 deliberately false assertions rejected. The parameterized nested suffix,
  both update branches, independent spec, uninitialized-state and full PC=0
  positive instance compiled and passed the dependency audit. Inventory and
  whitespace checks passed. PTX assembly was skipped (ptxas unavailable); no GPU
  execution or differential result is claimed. The existing CUDA runtime failure
  remains an external test limitation; no driver modification was attempted.

## Research record: parameterized attention PC=0 entry and local completion

- Existing limitation: nested-loop completion started from a PC 37 invariant;
  only one concrete full-source instance established how parameters, geometry,
  bounds guards, output address and scale load reached that point. It did not
  give general PC=0 execution or a reply function for arbitrary real inputs.
  The preceding goal turn changed authoritative proofs/tests and was progress.
- Shared indexing: `Scalar/Indexing.lean` holds the same fixed-width coordinate
  bounds and launch-derived row/column lemmas previously local to matmul. The
  matmul input module keeps its existing type/theorem names as an alias and
  checked wrappers, so existing source, output and nonvacuity proofs remain.
  Attention uses that common index-arithmetic capability, not a separate meaning
  for CTA coordinates or relaxed overflow assumptions.
- Actual source prefix: `ScalarAttentionInput/Init/Guards/Address/Entry.lean`
  proves generated PCs 0--36: all eight parameter reads, runtime 2-D indexing,
  row/column guards, modular output and loop addresses, zero initialization,
  key-count guard and scale load. Extra runtime parameter bindings are allowed.
  The resulting actual state satisfies the previously proved loop invariant
  without requiring initialized online registers for its first item.
- Completion/reply construction: `ScalarAttentionOracle.lean` constructs a
  typed f32 reply function, decoding each query after scale into a key index and
  Q/K/V slot. Separate slot/reply lemmas cover arbitrary dimensions and real
  input functions. `ScalarAttentionThread.active_execution` composes the actual
  prefix with nested-loop completion from PC=0 for arbitrary runtime dimensions,
  real matrices/scale and bounded indices/addresses. For N>0 the derived count
  is 35+N*(9*D+26), with exact-real natural-exp attention output. This is a
  constructed LOCAL execution, not a global memory-consistency witness.
- Masks/empty keys: row and column masks complete in 21/23 instructions with no
  memory events or queries. Empty keys complete in 32, read no matrices/scale,
  and need ONLY the output-start bound. No unused-input validity is added to
  that path. Completion uniqueness also reconstructs EVERY successful complete
  empty-key run's count and zero-write event under those conditions.
- Regression/reuse evidence: a non-unit 2-D CTA test has row=2/col=3, extra
  bindings, arbitrary real Q/K/V/scale, N=2/D=4, a derived 159-step full-source
  execution and output at 4140. Empty-key tests place unused input pointers at
  2^64-1, prove the nonempty read bounds FALSE, and still construct completion
  for EVERY oracle. Both masks, arithmetic index overflow rejection and the
  arbitrary-complete empty shape are checked. New negative proof attempts reject
  omitting the output row stride and using local tid.x as the global column.
- Remaining duties: nonempty arbitrary-completed-candidate reconstruction without
  preselecting replies/counts, initial Q/K/V/scale memory correspondence, complete
  four-byte bounds/alignment, race/UB duties, the all-candidate global output/
  memory-frame contract and independent complete consistency/observation
  witnesses. Read-start bounds do not establish physical allocation safety.
  The attention case stays partial; local oracle construction is not global
  nonvacuity. The full original goal and exact logits/token target are unchanged.
- Research/performance boundary: baseline source/proof engineering and shared
  arithmetic-rule reuse, not a new optimization or ownership method. New
  indexing/input/prefix/oracle/thread/test files total 969 lines, with the old
  matmul input module delegating shared lemmas. Cached Lean checks reported
  2.0 seconds for loop entry, 1.3 seconds for the thread module and 1.4 seconds
  for entry regressions in the final build; these are not end-to-end or GPU
  benchmark timings. No manual/agent-cost measurement, speedup claim or IEEE/
  bit-equality experiment was performed.
- Validation on 2026-11-04: complete checks passed with 23 Rust tests, 11
  regenerated AST comparisons, full Lean build, 1133 audited declarations and
  34 deliberately false assertions rejected. Existing matmul output/nonvacuity
  modules rebuilt successfully after indexing extraction. Inventory/whitespace
  checks passed. Fresh hardware checks found no ptxas/nvcc, an NVML 580.178
  driver/library mismatch and CUDA cuInit=804
  (`CUDA_ERROR_COMPAT_NOT_SUPPORTED_ON_DEVICE`). PTX assembly was skipped; no
  GPU execution or differential result is claimed. No driver changes were made.

## Research record: arbitrary attention source reconstruction and first GPU checks

- Existing limitation: general attention completion selected an input oracle.
  Nonempty runs still lacked reconstruction for EVERY successful completed
  source candidate. Repeated Q loads could not be identified with immutable
  inputs before memory reasoning. The preceding goal turn was implementation
  progress; all original acceptance requirements remain active.
- Source method: generic per-item score iteration, `Scalar/Replies.lean`, and
  `ScalarAttentionDotTrace/Reads/Trace/SourceTrace.lean` derive actual f32 reply
  tags, query slots, exact counts and full events from arbitrary completed
  PC=0 runs, without selecting their oracle or count. Scale, Q, K and V formats
  follow from successful source loads. Completion uniqueness and register-frame
  rules are reused across nested dot/online loops. All four branches retain
  their previously derived counts and masks/empty-key behavior.
- Positive/negative evidence: a locally complete source reads Q=0 then Q=1
  from the same address, produces 8, and differs from uniform-input result 7.
  This candidate is deliberately NOT claimed globally consistent. Integer scale
  and an f64 final V reply cannot complete. Identifying actual replies with
  initialized Q/K/V/scale, full byte/race/UB duties, the all-candidate global
  output/frame contract and separate legal complete global witnesses remain.
- Hardware access: existing workspace libraries matching kernel driver
  580.173.02 made cuInit succeed on the RTX 4060 Laptop sm_89; the default host
  libraries had yielded cuInit=804. No driver or root configuration was changed.
  The existing CUDA container supplied ptxas 12.8.93, which accepted twelve
  fixtures. `docs/assembly-evidence.json` records sources/hashes and tool version.
- Discovered limitation: the first owned GPU test stalled on the old publication
  source. Its reader/writer reached different static `bar.sync 0` instructions,
  violating the instruction's aligned requirements. That owned process was
  terminated with SIGTERM; it was not a watchdog timeout. The exact source/hash
  and observed failure are retained in `docs/gpu-barrier-divergence.json`.
  Assembly acceptance and abstract event consistency did not catch this issue.
- Correction and remaining method gap: publication now joins at one common
  barrier PC. Producer/consumer source proofs use 9/10 steps; their emitted
  abstract events and universal model-relative contracts remain. A shared static
  barrier-site certificate and actual old-source prefixes reaching PCs 5/9 are
  checked. The former source remains a negative fixture. General dynamic
  aligned-instruction/warp convergence legality is still absent from the global
  model; a single-static-site sufficient certificate does not solve that problem
  or reject all legitimate multi-site programs.
- Reproducible finite tests: the standard-library driver/JIT runner compares
  eleven outputs/frames byte for byte and checks one output-free loop's return.
  Cases cover Copy, SharedSwap, publication, FMA, literals, matmul with K>0 and
  K=0/aliasing, two-CTA atomic dispatch, and attention with a changed maximum,
  equal scores and empty keys/aliasing. Matrix/attention host references use
  exact rationals on selected inputs, with no error tolerance. Publication's
  unused consumer load may be optimized away; only its producer output/frame
  is externally checked. Reports include source hashes and device/library
  details. The bounded runner's timeout path was separately exercised: exit 124
  and an explicit failed-timeout JSON report. No negative divergent kernel is
  launched by the positive suite.
- Validation on 2026-11-05: the complete gate passed 23 Rust tests, twelve AST
  regeneration comparisons, the full Lean build, 1172 audited declarations and
  35 deliberately false assertions rejected, followed by all eleven exact-byte
  GPU comparisons and one completion-only test. The separate assembly report
  covers twelve fixtures. Source reconstruction first passed an intermediate
  1163-declaration gate; barrier-site regressions add nine audited declarations.
- Research/performance boundary: baseline source/proof engineering and model
  defect discovery, not a new optimization or ownership method. Six new reply/
  trace/test files total 623 lines; barrier-site helper/tests add 74, and the
  GPU runner/launcher add 276. Cached Lean builds reported about 1.8 seconds for
  source reconstruction and 3.4 seconds for its tests, not end-to-end timings.
  No optimization benchmark, manual/agent-cost comparison, universal IEEE/
  approximation proof or performance claim was produced. Ada sm_89 testing is
  not Hopper hardware coverage. Exact logits/token requirements, all remaining
  goal capabilities, and the unconfirmed exact 81-form inventory are unchanged.

## Research record: universal attention memory/output and independent nonvacuity

- Existing limitation: arbitrary completed-source reconstruction still permitted
  per-item Q replies to differ at the same address. It did not identify Q/K/V/
  scale with initial memory, prove full word bounds/race freedom, establish the
  observed output/frame contract or construct a legal complete global witness.
  The previous goal turn changed proofs, hardware testing and barrier evidence;
  it was progress. The full original goal remains active.
- Layout without unused-read assumptions: `ScalarAttentionConfig.lean` covers
  runtime output coordinates and complete four-byte words, with explicit bounds,
  alignment and output/read-region separation. Read-only regions may overlap
  subject to compatible initial representations. Read layout and initial data
  are conditional on M>0, D>0 and N>0: masked/empty-key paths do not acquire
  spurious input bounds, alignment or separation requirements. Allocation and
  physical launch limits remain distinct from mathematical word bounds.
- Actual events and ownership: read-list indexing identifies Q/K/V slots across
  both nested loops. `ScalarAttentionEvents.lean` reconstructs launch-wide event
  regions and the unique final output-write serial from arbitrary completed
  candidates, with arbitrary oracles, instruction counts and trace-list order.
  `ScalarAttentionMemory.lean` derives input immutability, overlapping-writer
  identity, absence of RMWs and race freedom. These reuse the same region,
  coordinate-injectivity and byte/race rules as matmul; race freedom is not a
  precondition or a new restriction on the general memory model.
- Input/output method: shared immutable-load rules identify actual scale/Q/K/V
  replies with represented initial data. Repeated Q loads therefore agree.
  Generic finite-support dot/average congruence connects the reconstructed
  candidate answer to the independent natural-exp attention specification with
  alpha=log(2)*scale. The universal current-model contract proves every output
  coordinate and preserves observed bytes outside O for every complete candidate,
  reads-from/coherence choice and permitted observer. No input oracle is selected
  by that contract.
- Separate existence proof: `ScalarAttentionCandidate/Witness.lean` enumerate
  every valid thread, construct its actual PC=0 source execution, prove the
  constructed read payloads against initial memory, and build initial reads-from,
  coherence and permitted observations. This does not assume consistency or the
  desired postcondition. It reuses the same launch enumeration, initial-read
  consistency and unique-writer observation rules as the matmul witnesses.
- Concrete regressions: a 2x2 grid of 2x2 CTAs with M=3/N=2/D=3 covers nine output
  cells, both masks and non-unit indexing. Independent complete global witnesses
  observe 7 and preserve a nonzero frame byte. N=0 allows Q=K=V=O and an unaligned
  unused scale at 2^64-1, without initial read data, and has a legal completed
  witness producing zero. Inconsistent repeated Q, wrong scale, wrong output and
  zeroed frame are rejected. False assertions also reject treating a bounded
  read start as a whole-word bound, live scale/output overlap and requiring input
  reads on the empty-key path. Arithmetic layout predicates now have explicit
  decidability instances so the gate checks refutation, not missing instances.
- Hardware: added the same M=3/N=2/D=3, 2-D grid/block attention case to the exact-
  rational driver/JIT comparisons. The RTX 4060 Laptop sm_89 run passed all nine
  output cells plus guards byte for byte. The updated GPU report records twelve
  exact-byte cases and one completion-only test. No PTX fixture changed; the
  existing twelve-fixture ptxas report remains applicable, subject to hash check.
- Research/performance boundary: baseline proof engineering and reuse, not a new
  optimization or ownership method. The eight new attention proof modules plus
  their memory tests total about 1300 lines. Cached Lean reported approximately
  1.4 seconds for input-value rules, 1.4 seconds for the independent witness and
  1.5 seconds for its initial memory tests; these are not end-to-end timings.
  No optimization benchmark, manual/agent-cost comparison, throughput/latency/
  memory benefit, novelty claim or universal IEEE/bit-equivalence result was
  measured. Exact logits/token requirements are unchanged.
- Remaining goal duties: physical allocation/UB, full PTX/observer correspondence,
  general aligned-barrier legality, broader atomics/shuffle, Ampere/Hopper async
  features, same-stream multi-kernel composition/MoE and the runtime/Iris in-flight
  resource bridge remain. The exact paper 81-form inventory remains unconfirmed;
  current-model attention correctness plus existence is not full paper parity.
- Validation on 2026-11-05: the complete gate passed 23 Rust tests, twelve AST
  regeneration comparisons, the full Lean build, 1272 audited declarations and
  38 false assertions rejected by evaluation. The new eight proof modules and
  their regression theorems, two generic congruence rules and two arithmetic
  decidability instances added 100 audited declarations. Separately, all twelve
  exact-byte GPU comparisons and one completion-only check passed. The nine
  positive GPU fixture hashes and twelve assembly-report fixture hashes match
  the current PTX sources. Inventory validation, Python compilation and whitespace
  checks passed. PTX assembly was not rerun because no fixture changed; its
  previously recorded result remains assembly evidence, distinct from GPU execution.

## Research record: actual source PCs and checked integer barrier admission

- Existing limitation: the generic byte graph matched barrier resources and
  generations but discarded the generating instruction PC. Hardware testing had
  exposed the old publication source's different-PC aligned-barrier use; a
  static source-site certificate and a corrected fixture did not themselves
  add source-aware admission to the model. The preceding goal turn added the
  universal attention memory/output theorem, independent global witnesses and
  GPU evidence; it was progress. The full original goal remains active.
- Reusable instrumentation: `Event/SourceRun.lean` annotates every event with
  the actual pre-step state's PC for arbitrary finite step functions. Successful
  plain executions have annotated counterparts, annotated executions erase to
  the identical plain execution/events, and each annotation has an actual
  generating step. `Event/Origins.lean` connects this to the integer interpreter,
  its existing source-provenance predicate and candidate lookup. Source PCs are
  computed from the actual program/oracle/count, not supplied as assumptions or
  unconstrained metadata. Barrier source extraction proves the corresponding
  instruction carries the matched resource.
- Dynamic source rule: every same-CTA/resource/generation arrival/return pair
  must have equal source PCs. Different generations may use different sites.
  The static `uniqueBarrierSites` check is proved sufficient for arbitrary
  provenance-checked candidates; it is not required of all source programs.
  This models the same-instruction obligation of the pinned PTX aligned-barrier
  rule, not full SIMT/warp convergence, early-exit timing or all ISA UB conditions.
- Admission and reuse: `Event/Checked.lean` bundles provenance, source matching
  and existing graph-memory conditions. Universal graph contracts imply checked
  contracts; checked nonvacuity still needs an independent source-aligned witness.
  `Kernels/SourceChecked.lean` lifts Copy, SharedSwap and publication contracts
  AND complete memory/observation witnesses. Their caller preconditions gain no
  new source-alignment premise. These use the same instrumented execution and
  static-certificate rule, not separate per-function source assumptions. The
  graph-only API remains a clearly identified weaker admission baseline.
- Negative regression: the actual generated archived divergent source has a
  complete two-thread source candidate with checked local provenance and exactly
  the positive publication candidate's abstract events. A real matched arrival/
  return pair originates at writer PC 9 and reader PC 5. Checked admission rejects
  that candidate for EVERY initial memory, reads-from and coherence choice.
  A deliberately forged common-PC assertion is rejected by evaluation.
- Positive regression: a hand-authored four-instruction Lean source uses
  `bar.sync 0` at PCs 0 and 2 in successive generations. Its unique-static-site
  check is FALSE, but actual source matching, CTA coverage, completion, memory
  consistency and synchronized observation preserving arbitrary initial global
  bytes are proved independently. False assertions reject demanding a single
  static site and attributing the second return to the first PC. This semantic
  regression is not a new generated PTX/GPU fixture or required acceptance case.
- Validation on 2026-11-05: the complete gate passed 23 Rust tests, twelve AST
  regeneration comparisons, the full Lean build, 1328 audited declarations and
  41 deliberately false assertions rejected by evaluation. The new reusable
  origin/checked rules, three kernel families and positive/negative regressions
  add 56 audited declarations. Inventory/whitespace checks passed. No PTX fixture
  or GPU harness changed; the existing GPU and assembler reports are retained
  separately and their fixture hashes are checked rather than claiming a new
  hardware validation of this admission layer.
- Research/performance boundary: model repair and baseline proof engineering,
  not a new optimization, ownership protocol or novelty result. Five new source/
  checked/test modules total 563 lines, plus shared candidate-lookup and static
  certificate helpers. Cached Lean reported 652 ms for integer origins, 441 ms
  for the checked interface, 1.4 seconds for kernel bridges and 1.3 seconds for
  source regressions; these are not end-to-end or GPU benchmark timings. No
  throughput, latency, memory-benefit or manual/agent-cost comparison was measured.
  Exact logits/token requirements are unchanged.
- Remaining goal duties: connect mixed scalar-source origins/admission, broaden
  SIMT/ISA legality and full PTX/observer correspondence, then continue scoped
  atomics/shuffle, Ampere/Hopper async features, same-stream multi-kernel/MoE
  composition and the runtime/Iris in-flight resource bridge. Physical allocation
  and runtime/compilation assumptions remain explicit. The exact 81-form paper
  inventory remains unconfirmed; the full objective has not been narrowed.

## Research record: mixed scalar source origins and checked kernel witnesses

- Existing limitation: integer source-aware admission computed actual barrier
  PCs, but the mixed interpreter's float bank and actual launch block were not
  connected to that layer. The prior goal turn added integer origin/erasure
  rules, checked contracts and independent positive/negative witnesses; it was
  progress. The original full objective remains active.
- Actual mixed semantics: `Scalar/Origins.lean` instantiates the same generic
  source-run instrumentation on the actual scalar step function. Construction
  and erasure preserve the complete state, including both register banks, and
  event-origin extraction uses actual scalar provenance and launch block.
  The private integer skeleton is not used as the meaning of a mixed program.
  A delegate-fetch lemma exposes only the local integer instruction lookup.
- Barrier origin rule: `Scalar/Thread.lean` proves that a scalar barrier event
  must originate at the actual `.integer (.barrier bid)` instruction. Delegated
  integer events retain their source identity; float arithmetic/loads/stores,
  special-register reads and atomic RMWs cannot manufacture barrier events.
  `Event.BarrierKind` is generalized across payload types, so both interpreters
  use the same barrier-source relation. Static unique-site checking is proved
  sufficient, with dynamic per-generation PC matching still the admission rule.
- Checked interfaces and reuse: `Scalar/Checked.lean` combines actual provenance,
  source matching and the unchanged generic memory/observer predicates.
  `Kernels/ScalarSourceChecked.lean` supplies checked contracts and independent
  checked nonvacuity for scalar matmul, atomic dispatch, scalar attention and the
  literal/shared helper. Caller preconditions and output/frame formulas are
  unchanged. These reuse the generic instrumentation, source-origin extraction
  and certificate/nonvacuity bridge; no new alignment premise is passed by the
  caller and no desired output is assumed by witness construction.
- Mixed positive regression: a typed hand-authored semantic program reads
  `%ntid.x`, branches using the actual block size two, executes f32 move/add and
  encounters `bar.sync 0` at PCs 7 and 9 in two successive generations. Full
  scalar execution, float-bank preservation, CTA coverage, completion, source
  matching, memory consistency and observations preserving arbitrary initial
  global bytes are independently checked. Its static unique-site certificate is
  false. Replacing the actual block with the unit block takes a different path
  and the recorded eight-step run faults; the actual source PC cannot silently
  be computed with a unit block.
- Mixed negative regression: embedding the archived generated divergent source
  into the scalar interpreter has actual complete local runs and full launch
  provenance. Writer/reader source PCs 9/5 reject checked admission for every
  memory and coherence choice. Evaluated false assertions reject a forged common
  source, the wrong unit-block result and attributing the second phase to the
  first PC. The mixed hand-authored program is a Lean semantic regression, not
  an additional generated PTX or GPU fixture.
- Existing kernel instances: complete checked matmul and attention witnesses
  retain their observed values 12/7 and nonzero frame bytes. Empty-key attention
  still admits aliased Q/K/V/O and an unused invalid scale, producing zero.
  Both atomic ticket assignments retain counter/job bytes 2/1/2 and the frame.
  The literal/shared helper retains output 9 through the new checked contract.
- Validation on 2026-11-05: the complete gate passed 23 Rust tests, twelve AST
  regeneration comparisons, the full Lean build, 1393 audited declarations and
  44 false assertions rejected by evaluation. The mixed-origin/checked rules,
  four kernel bridges and regression theorems add 65 audited declarations.
  Inventory, Python compilation and whitespace checks passed. No PTX fixture or
  GPU runner changed; source hashes are checked against the existing nine-fixture
  GPU and twelve-fixture assembly reports, without claiming a new hardware test.
- Research/performance boundary: baseline model repair and proof engineering,
  not a new optimization or ownership protocol. Five new mixed-source/checked/
  test modules total 532 lines, plus core delegate/source lemmas and a polymorphic
  barrier-kind definition. Cached Lean reported 1.4 seconds for origins, 1.6
  seconds for the checked interface, 2.0 seconds for kernel bridges and 1.9 seconds
  for mixed source regressions. These are not end-to-end or GPU timings. No
  throughput/latency/memory benefit, manual/agent-cost comparison, universal IEEE
  proof or new GPU bit-equivalence result was measured. The exact logits/token
  target is unchanged.
- Remaining goal duties: same-stream multi-kernel composition and the three-
  kernel MoE case, broader atomics/shuffle, Ampere/Hopper async/MMA, actual
  in-flight resource/runtime/Iris connections, physical allocation and fuller
  PTX/SIMT/observer correspondence remain. Source checks do not settle all ISA UB
  conditions. The exact paper 81-form inventory remains unconfirmed.

## Research record: completed stream composition and finite-domain publication

- Existing limitation: per-kernel observers constrained only finite domains,
  while a successor needs an initial global byte map. Copying the raw observer
  function would import unconstrained outside-domain bytes; copying only selected
  outputs without proving write coverage could silently discard actual writes.
  There was no ordered multi-kernel execution relation or separate composition
  nonvacuity rule. The previous goal turn added actual mixed-source origins,
  checked kernel bridges and independent witnesses; it was progress.
- Publication method: `Event/Publication.lean` requires coverage of EVERY actual
  global write byte, uses observed bytes on the boundary domain and retains the
  initial map elsewhere. It proves the resulting map is a permitted ordinary
  observation on ANY finite global domain. Outside-domain locations are unwritten,
  so initialization cannot hide a newer modification. This extends the existing
  observer projection, not an assumed result about the full PTX augmented graph.
- Stream model/rules: `Scalar/Stream.lean` separates persistent global bytes from
  each launch's fresh shared initialization. A completed step carries actual
  source-checked provenance, memory consistency, completed observation and proved
  write coverage. Successors receive its published global map. Ordered-run
  append/splitting and consequence rules prove universal postconditions; separate
  nonvacuity rules construct a predecessor execution, derive the intermediate
  precondition and then construct the tail. Event IDs remain local to each step
  record rather than being conflated across kernels. The boundary follows the
  paper's ordinary same-stream publication model; CUDA implementation, other
  proxy boundaries and full PTX correspondence remain explicit open duties.
- Reuse/effects: actual source provenance derives publication coverage for scalar
  matmul, attention and the literal/shared helper in `Kernels/StreamEffects.lean`.
  A shared payload-location lemma identifies every written byte offset. A generic
  decode-to-representation rule connects existing observed-real contracts to a
  successor's complete symbolic input encoding. No desired read oracle, whole-
  pipeline success or unexplained source-effect assumption is added to inputs.
- Generated-entry baseline: `StreamPipeline.lean` composes actual literal/shared
  PTX (publishing A=9) with actual scalar matmul at M=N=K=1, proving C=9*B for
  arbitrary represented real B and initial heaps, plus frame-byte preservation.
  Independent component nonvacuity and the proved intermediate input condition
  construct a complete checked pipeline. A concrete B=2 instance starts with
  uninitialized A/C, produces 18 and preserves the nonzero frame. First-stage
  completion changes A, so resetting the successor to the stale initial heap is
  rejected. Other regressions reject omitted global write publication, raw
  unobserved poisoned payloads and carrying shared state across launches. The
  evaluated byte regressions project raw-bit constructors, avoiding an unsupported
  decision procedure for equality of arbitrary symbolic real values.
- Hardware: the existing driver runner can now queue a launch without an immediate
  host completion wait. All existing tests keep their prior wait behavior. The
  new chain queues both already-loaded entries on one default stream, waits once
  after both, and compares a 24-byte arena containing A=9, B=2, C=18 and three
  guard words. The RTX 4060 Laptop sm_89 run passed all thirteen exact-byte cases
  and the existing completion-only smoke check. The report records both entries
  and absence of an intermediate host synchronization. No PTX fixture changed;
  the existing twelve-fixture assembler result is retained separately.
- Scope and cost: this is baseline completed-boundary semantics and proof
  engineering, not a new optimization, runtime proof or ownership protocol.
  Five new publication/stream/effect/pipeline/test modules total 493 lines plus
  the reusable real-decode rule. Cached Lean reported 643 ms for initial
  publication, 2.7 seconds for the generated-entry pipeline and 1.3 seconds for
  stream regressions; these are not end-to-end timings. No throughput, latency,
  memory benefit or manual/agent-cost comparison was measured. Finite exact-byte
  testing does not establish arbitrary-input IEEE/GPU equivalence. Exact logits/
  token requirements are unchanged.
- Remaining goal duties: the two-entry chain is NOT the required three-kernel
  top-1 routing/expert/combine MoE implementation. That case remains planned,
  alongside broader atomics/shuffle, Ampere/Hopper async/MMA, in-flight resource/
  runtime/Iris bridges and fuller allocation/ISA/SIMT/observer correspondence.
  The full original objective and unconfirmed exact 81-form inventory are intact.
- Validation on 2026-11-05: the complete gate passed 23 Rust tests, twelve AST
  regeneration comparisons, the full Lean build, 1442 audited declarations and
  47 evaluated false assertions rejected. New publication/stream/effect/pipeline
  and regression theorems add 49 audited declarations. The separate GPU run
  passed thirteen exact-byte comparisons and one completion-only check. The
  nine positive GPU fixture hashes and twelve assembly-report fixture hashes
  match current sources. Inventory validation, Python compilation and whitespace
  checks passed. Assembly was not rerun because no PTX fixture changed.
- Agent-accounting snapshot at 2026-11-05 01:42:17 UTC: the goal ledger reported
  2,990,390 cumulative tokens versus 2,907,902 at this continuation's start, a
  difference of 82,488. This is an interim accounting snapshot, not final billed
  usage or a controlled agent-cost comparison; monetary/manual costs were not
  measured.


## Round: actual three-kernel MoE source and routing traces (2026-11-05)

- Instance: two-expert normalized top-1 routing, dense linear experts and gather
  from expert-partitioned storage, with deterministic expert-0 tie breaking.
  Three real typed PTX entries now replace the planned-only placeholder. The
  source lengths are 23/57/41 instructions; these are our fixtures, not a claim
  that the paper artifact or exact 81-form inventory was recovered. Unit combine
  weight, no bias/packing/capacity and top-1 are explicit specification choices.
- Prior limitation: the scalar frontend lacked floating comparison; the proved
  literal-to-matmul stream baseline had no actual routing, expert selection or
  expert-plane gather. A generated AST or finite GPU run alone cannot establish
  represented-memory agreement or complete legal global execution existence.
- Implemented: one fail-closed `setp.gt.f32` form preserves predicate destination
  and operand order in Rust/Lean data. Its real ordered-comparison step, flag
  bounds/tie, bank and frame rules reuse existing scalar updates. Wrong types,
  unmodeled qualifiers, unordered/Boolean/dual-predicate comparisons, predication
  and nonfinite inputs are rejected. This is the thirteenth fixed frontend float
  form, with no new IEEE/NaN semantics or unexplained axioms.
- Independent specification: `MoeSpec.lean` defines selection, ordered dense
  expert output, u32 routes, sparse expert-plane results and final Y. It proves
  score maximality, deterministic ties, layout uniqueness/bounds and K=0 output.
- Actual routing proof: `MoeRouteSelect.lean` handles both data-dependent source
  branches, store and return for arbitrary ready states. `MoeRouteThread.lean`
  connects actual PC=0 parameter reads, dynamic 1-D indexing, masks, wide address
  arithmetic and both gate loads. It constructs active/masked local traces
  (22/11 steps) and reconstructs arbitrary successful completed source counts,
  typed replies and events. All pointer-byte and fixed-width index bounds remain
  explicit. The masked path produces no data events. No correct gate oracle is
  assumed for reconstruction, and no claim is made that these local replies
  already agree with initial gate memory. Concrete non-unit CTA/block tie and
  zero-row/aliased pointer instances exercise actual source execution.
- Reuse: comparison uses the common integer/real bank discipline and frame
  rules. Route proof uses fixed-interpreter local, comparison/branch, load,
  run-composition and complete-run-uniqueness rules already used by matmul,
  atomic dispatch and attention. This is baseline capability engineering, not
  an ownership/synchronization research contribution or measured optimization.
- GPU evidence: five new chains load all modules first, queue route/expert/
  combine on one default stream, wait once and compare whole arenas. Checks
  cover mixed/tie routing, both expert planes (including untouched sentinels),
  negative/subnormal gates, masks, K=0, N=0, M=0 and unused-input aliases. Host
  expected routing/dots are computed independently with exact fractions on
  selected f32-exact cases; no tolerance or weakened logits/token target is used.
  Assembly and GPU execution reports are separate from formal evidence.
- Remaining: gate replies versus represented initial memory, active launch
  enumeration/geometry, global layout/alias/race duties, expert/combine full
  source reconstruction, per-stage universal output/frame contracts, independent
  complete legal global witnesses and their MoE stream composition. The case is
  partial; five successful GPU chains are not substituted for those proofs.
  Broad atomics/shuffle, Ampere/Hopper, in-flight Iris/runtime/proxy/ISA bridges
  and the unconfirmed paper instruction inventory remain in the original goal.
- Cost: no throughput/latency/memory benefit, end-to-end proof timing, monetary/
  manual cost or controlled agent comparison was measured. The new MoE modules
  and tests are baseline proof work; source test results are distinct from proof
  checking and from hardware evidence. Exact-real proofs do not establish
  arbitrary-input GPU/IEEE or cross-kernel-plan bit equivalence.
- Validation: the final complete gate passed 26 Rust tests, formatting/clippy,
  fifteen generated-AST comparisons, the complete Lean build, 1494 audited
  declarations and 51 evaluated false assertions rejected. The five new proof/
  test modules total 652 lines and add 52 audited theorem declarations. Initial
  masked/active routing source builds and regressions were checked separately;
  the aggregate gate reruns them. An initial negative harness attempted mixed
  instruction equality without a decision instance; the final regression
  instead decides a computable projection of the actual combine load pointer,
  and must be logically refuted rather than merely fail elaboration.
  Separate sm_89 execution passed eighteen exact-byte comparisons plus one
  completion-only loop test, and CUDA 12.8.93 ptxas accepted all fifteen fixtures.
  All twelve positive GPU source hashes and fifteen assembler source hashes
  match current PTX. Python compilation, metadata validation and whitespace
  checks passed. Existing non-ptx-verify user changes were left untouched.
- Agent-accounting snapshot at 2026-11-05 02:18:28 UTC: the goal ledger reported
  3,188,063 cumulative tokens versus 2,993,349 at this continuation's recorded
  start, a difference of 194,714. This is an interim ledger snapshot, not final
  billed usage or a controlled agent-cost comparison. The goal remains active;
  no unfinished obligations were removed or marked complete.


## Round: universal route memory, complete witnesses and u32 stream publication (2026-11-05)

- Instance/limit: the previous MoE round supplied actual source and complete local
  routing traces, but arbitrary read replies were not tied to initial gate bytes.
  Successful local execution or correct chosen expert alone cannot establish
  global consistency. The required three-stage MoE contract is still incomplete.
- Source and layout: the route config now constrains one-dimensional ownership,
  full four-byte bounds/alignment, live gate/route region separation and output
  coverage. Actual PC=0 reconstruction supplies all read/write events. Layout
  proves read-only gates, unique route writers and race freedom rather than
  assuming them as new preconditions. M=0 admits unaligned aliased G=R and no
  gate initialization; source parameters still have their declared word bounds.
- Universal contract: every complete provenance-checked route candidate, memory
  witness and permitted observer now satisfies the independent u32 top-1 Routes
  specification and preserves the observed frame. Every real gate reply is
  identified from represented initial memory through the existing polymorphic
  agreement predicates. No desired oracle, new axiom or weaker output goal was
  added to the precondition. Full physical allocation, runtime, SIMT/ISA and
  observer correspondence remain explicit boundaries.
- Independent witness: all valid launched IDs are enumerated once, active and
  masked PC=0 executions are constructed, and separate memory/observation
  conditions are proved. The universal output theorem is not used to assume
  legal existence. Both correctness and nonvacuity are also available through
  actual mixed-program source-aware checked admission.
- Stream: u32 representation/publication rules complement existing exact-real
  rules. Actual route writes derive full observer coverage, and the singleton
  stream theorem publishes Routes to the successor initial heap with a whole-
  heap frame, including unobserved bytes. Independent component nonvacuity
  constructs a completed route boundary. This is one MoE stage, not a substitute
  for the expert/combine contracts or full three-stage composition.
- Reuse evidence: the payload-independent immutable-read/unique-writer race rule
  is used by route and scalar matmul. Matmul's public no-race theorem and original
  output/frame contracts are retained. Reusable u32 observation and generic
  word-payload region rules avoid special route-byte axioms. These are baseline
  engineering improvements, not an ownership/synchronization novelty claim or
  measured optimization.
- Regressions: a 3-token, 2-CTA/non-unit-block launch with one masked thread has
  universal mixed/tie routes [0,1,0], a preserved nonzero frame and a separate
  complete checked legal witness. A real locally complete wrong-gate candidate
  is rejected globally even when its expert selection is unchanged. The M=0
  unaligned alias/uninitialized-gate instance has a separate complete checked
  witness. The actual route stream has a legal intermediate-memory witness and
  rejects stale routing and publication omitting the final byte of a u32 word.
- Remaining: expert/combine source reconstruction, their universal memory/
  output/frame contracts and independent complete legal witnesses, then the
  full MoE stream precondition and composition. Reuse the scalar FMA-loop proof
  through an explicit actual-code fragment correspondence when extending the
  expert stage; a mathematical dot-product lemma alone will not prove the PTX.
  Broader atomics/shuffle, Ampere/Hopper and in-flight Iris/runtime/proxy/ISA
  bridges and the unconfirmed 81-form inventory remain in the original goal.
- Cost: no optimization throughput/latency/memory benefit or controlled manual/
  agent-cost comparison was measured. New route proof modules are baseline
  engineering; formal proof checking and previous finite execution evidence are
  reported separately. Exact logits/token and hardware bit-equality requirements
  were not weakened. No source PTX or GPU harness changed this round.
- Validation: the complete gate passed 26 Rust tests, formatting/clippy, fifteen
  regenerated-AST comparisons, the full Lean build, 1579 audited declarations
  and 54 evaluated false assertions rejected. The new ten modules total 936
  lines and add 81 audited theorem declarations; four reusable u32/word helpers
  add four more audited theorems. The prior matmul/attention/atomic/stream
  contracts and complete witnesses were rebuilt with the common helper changes.
  New route output, witness and stream modules each checked in approximately
  1.1–1.2 cached Lean build seconds; these are individual cached module timings,
  not end-to-end performance or proof-cost comparisons. Metadata validation,
  Python compilation and whitespace checks passed. No GPU or assembly rerun
  was needed for these proof-only changes: all twelve positive GPU and fifteen
  assembler fixture hashes still match the retained successful reports.
- Agent-accounting snapshot at 2026-11-05 02:40:01 UTC: the goal ledger reported
  3,376,968 cumulative tokens versus 3,190,046 at this continuation's start, a
  difference of 186,922. This is an interim ledger snapshot, not final billed
  usage or a controlled cost comparison. The full original goal remains active;
  only the route component advanced, with no remaining MoE/async/ISA obligations
  removed or declared complete.


## Round: source-certified shared FMA loop and actual expert entry instances (2026-11-05)

- Instance/limit: expert computation needs the same scalar dot-product loop as
  matmul, but at different source PCs and after the u32 route query. The prior
  matmul proof hardcoded PC32/query0 and expert source used different temporary
  register names. Re-proving the same arithmetic/control loop per kernel would
  leave a large duplicated semantic proof and obscure the query-origin duty.
- Reusable rule: `Scalar/FmaLoop.lean` parameterizes actual code, fragment entry
  PC, prior query count, arbitrary K/layout/data and remaining iterations. A
  checked eleven-slot `Fragment` certificate covers every guard/load/FMA/index/
  branch/store/return instruction and its actual absolute targets. The rule is
  proved from the fixed scalar interpreter. `FmaLoopTrace.lean` reconstructs all
  typed f32 replies, exact count, events and final accumulator from arbitrary
  successful completed local executions. No source certificate comes from an
  oracle, and no desired output, execution bound or new axiom is assumed.
- Reuse evidence: existing matmul iteration/finish now instantiate this proof at
  PC32/query0 while retaining prior public invariant and theorem statements.
  The matmul loop module shrank from 292 to 164 lines. Expert loop temporaries
  were renamed to the same canonical register names; mechanically generated
  expert source validates the same rules at PC46/query1. Its 57-instruction
  source count and control/data operations are unchanged. `MoeExpertsLoop.lean`
  connects arbitrary-K local execution to the independent expert recurrence.
  This is baseline proof engineering, not a new optimization or ownership/
  synchronization research contribution.
- Actual source instances: fixed M=N=3/K=2, CTA=(1,1,0), block=(2,2,1), tid=0
  executes PC0 with the u32 route read at136, both expert branch paths and their
  sparse plane addresses. All real X/weights remain arbitrary. Expert 0 takes
  62 steps and writes H[0,2,2] at288; expert 1 takes 68 steps and writes H[1,2,2]
  at324, with five queries in either case. A K=0/X=W=H source instance completes
  in 50 steps, makes only the route query, and stores zero without X/W reads.
  These are local execution witnesses, not global consistency witnesses.
- Regressions: altered loop branch and omitted output-store certificates fail;
  an entry with one route query cannot reset its query origin to zero. Integer
  and f64 replies cannot satisfy the f32 loop's complete execution. Another
  source retains the certified loop but changes PC0 to return, proving that a
  fragment certificate alone does not establish whole-entry correctness. The
  evaluated query-count negative was checked to be logically refuted, not an
  elaboration/resource failure.
- Hardware: after the expert temporary-name change, CUDA 12.8.93 ptxas accepted
  all fifteen PTX fixtures. The CUDA driver runner was rerun on sm_89; eighteen
  exact-byte comparisons and the separate completion-only smoke check passed,
  including all five full MoE chains. Reports were refreshed with current source
  hashes. The exact-real theorem and finite tests remain separate evidence; no
  universal IEEE/GPU equivalence or performance result is claimed.
- Remaining: parameterized expert PC0/route-load/selection/layout reconstruction
  for all admissible geometry/dimensions and arbitrary successful read oracles;
  full four-byte/alignment/region and initial X/W/R correspondence; universal
  expert output/frame and independent complete legal global witnesses. Combine
  and full three-stage MoE composition then remain, together with the original
  broader atomics/shuffle, Ampere/Hopper, async/Iris/runtime/ISA obligations and
  unconfirmed paper 81-form inventory. Local fragment start-address bounds are
  not substituted for the complete global layout duties.
- Cost/target: no throughput/latency/memory benefit, monetary/manual cost or
  controlled agent comparison was measured. The large concrete source-prefix
  reductions use a higher elaborator heartbeat allowance; this is a proof-check
  resource setting, not an added logical assumption or a kernel execution bound.
  The independent specifications and exact logits/token requirements remain.
- Validation: the final complete gate passed 26 Rust tests, formatting/clippy,
  fifteen regenerated-AST comparisons, the full Lean build, 1618 audited
  declarations and 56 evaluated false assertions rejected. The four new modules
  total 674 lines and provide 36 audited theorems; three matmul fragment/adaptor
  theorems add three more. Existing universal matmul/route/attention/atomic and
  stream contracts and their independent witnesses rebuilt successfully. New
  generic fragment and reply-reconstruction modules first checked in 2.8/1.4
  cached Lean seconds; actual source-prefix regression checking required about
  33 seconds in an intermediate build. These are cached module observations,
  not an end-to-end proof-cost or agent/performance comparison. After the PTX
  rename, all fifteen assembler fixtures and eighteen GPU exact-byte cases plus
  one completion-only case were rerun successfully; all twelve GPU and fifteen
  assembly source hashes match current files. Metadata validation, Python
  compilation and whitespace checks passed. Other project work was untouched.
- Agent-accounting snapshot at 2026-11-05 03:01:24 UTC: the goal ledger reported
  3,460,786 cumulative tokens versus 3,378,893 at this continuation's start, a
  difference of 81,893. This is an interim ledger snapshot, not final billed
  usage or a controlled cost comparison. The original goal remains active;
  expert local-loop progress does not complete MoE or remove outstanding duties.


## Round: parameterized expert PC=0 entry and source classification (2026-11-05)

- Instance/limit: the prior expert loop was universal at its entry invariant,
  but its PC=0 connection had only fixed-dimension instances. The missing duties
  were actual parameter/index/mask execution, the preceding u32 route load,
  expert-dependent plane selection and derived address/loop initialization.
- Implemented: declared word inputs and parameter matching, actual 17-step
  parameter/index prefix, both source masks and returns. Row/column masked
  execution completes in 20/22 steps with no data event or query and needs no
  data-address bound. Runtime CTA/block/thread values remain parameters, with
  explicit index-overflow bounds rather than a unit-block substitution.
- Route/selection: the actual pointer and integer load produce a wrapped u32
  value and increment the query index. Successful integer-source execution
  supplies the integer-reply constructor; no valid-route oracle is assumed.
  Normalized routes >=2 execute the return in 27 steps with only the route read.
  Valid 0/1 routes execute both actual branch paths and the six expert-1 plane
  instructions. Plane arithmetic retains modular behavior until bounds apply.
- Addresses/loop: actual PC34--45 pointer, stride and accumulator instructions
  establish the common PC46/query1 FMA invariant with natural expert-plane
  addresses. Output/read-start bounds are explicit; X/W bounds are conditional
  on k<K and impose no unused-read conditions at K=0. Complete local execution
  follows the independent expert recurrence for all real data and arbitrary K.
- Reconstruction: arbitrary successful complete source runs are classified into
  row mask, column mask, invalid route or either valid expert. The route reply
  is derived from the actual first load and all valid-body event/count facts
  come from the common FMA reconstruction. Expert 0/1 counts are 44/50+9*K.
  No successful whole launch, global consistency or correct input oracle is
  inserted into preconditions. Source completion is not global nonvacuity.
- Reuse evidence: integer-load stepping/type-extraction and register-frame
  updates are reusable scalar rules. The generalized unsigned comparison rule
  handles register/immediate operands; the old register-only rule delegates to
  it, preserving existing callers. Expert execution reuses the previously
  certified FMA rules. This is baseline engineering, not a new ownership/
  synchronization method or measured optimization.
- Tests: all-oracle completed-source reconstruction at a non-unit CTA/block
  instance, raw 2^32+1 route normalization to expert 1, invalid route 17 without
  float accesses, and M=0/N=0 with unaligned X=W=R=H=1, maximum u32 K and no
  memory queries. Negative assertions check expert-1 step count and plane
  address. Existing fixed-data/all-real-data and K=0 tests remain in the gate.
- Remaining: full four-byte/alignment/live-region proofs, actual X/W/R initial
  memory agreement, derived unique writers/race freedom, universal observed
  expert output/frame and independent complete legal global witnesses; combine
  source/memory and full three-stage MoE composition. Broader atomics/shuffle,
  Ampere/Hopper, async/Iris/runtime/ISA duties and the unconfirmed exact 81-form
  inventory remain in the original goal, without a smaller completion target.
- Cost/boundary: no throughput/latency/memory benefit or controlled manual/agent
  comparison was measured. The new source proofs use fixed semantics and the
  prior independent spec; no new axiom, numerical tolerance or weaker logits/
  token target was added. No PTX or GPU harness changed this round, so finite
  hardware evidence remains separate and is checked by source hash.
- Validation: the complete gate passed 26 Rust tests, formatting/clippy, fifteen
  regenerated-AST comparisons, the full Lean build, 1660 audited declarations
  and 58 evaluated false assertions rejected. Eight new modules total 953 lines
  and provide 38 audited theorems; four reusable scalar rules add four more.
  Existing matmul/route/attention/atomic/stream contracts and independent legal
  witnesses rebuilt with the shared rule changes. Parameterized expert address
  initialization and its regression module checked in approximately 3.1/1.7
  cached Lean seconds; these are individual module observations, not end-to-end
  proof-cost or performance measurements. Metadata validation, Python compilation
  and whitespace checks passed. No PTX/GPU-runner change required another native
  run: all twelve positive GPU and fifteen assembly fixture hashes still match
  the previously successful reports. Other project work was left untouched.
- Agent-accounting snapshot at 2026-11-05 03:27:41 UTC: the goal ledger reported
  3,547,611 cumulative tokens versus 3,463,300 at this continuation's start, a
  difference of 84,311. This is an interim ledger snapshot, not final billed
  usage or a controlled cost comparison. The original goal remains active;
  full expert source progress is not a global MoE correctness/nonvacuity claim.


## Round: expert universal memory contract and independent publication (2026-11-05)

- Instance/limit: the prior expert theorem reconstructed all complete source
  traces but did not constrain their route/float replies by initial memory.
  Its local execution witnesses did not establish global consistency or an
  observable selected-expert output. These missing obligations are closed for
  the current ordinary-memory, exact-real model in this round.
- Implemented modules: `MoeExpertsConfig/Events/Memory/Inputs/Output/Candidate/
  Witness/Stream`. The configuration states full live-byte regions/alignment,
  64-bit footprint bounds, launch coverage and separation. Actual events derive
  these access bounds. Invalid-route candidates are retained while immutable
  R/X/W and unique H writers establish race freedom; route agreement is derived
  afterwards, avoiding a valid-route precondition that would restrict candidates.
- Input/output proof: a common `immutable_u32_load` uses all four bytes and
  bounded injectivity to recover the normalized route. Immutable real reads
  establish X/W replies. The arbitrary-K recurrence matches the independent
  selected-expert specification. Universal correctness preserves every observed
  byte outside selected H words, including unselected expert-plane words.
- Nonvacuity/publication: separately construct all actual completed source
  traces, initial reads/coherence and a consistent complete finite observer.
  Checked admission uses source provenance. Actual writes derive publication
  coverage; selected H results reach successor initialization while every other
  heap byte is retained. The stream nonvacuity theorem is separate from its
  correctness theorem. Neither theorem assumes the desired output or an already
  legal completed execution in its input precondition.
- Reuse evidence: the payload-independent read-only-input/unique-writer race
  rule is now used by matmul, route and expert. Expert global reconstruction
  uses the existing common FMA fragment at PC46/query1. The new u32 immutable
  read theorem is a reusable byte-agreement rule. This is baseline verification
  engineering; no new async ownership method or research novelty is claimed.
- Regressions: 3x3x2 data with 2x2 CTAs and 2x2 threads, mixed routes [0,1,0],
  selected results [12,20,12], and preserved unselected-plane sentinels. A typed
  wrong-route canonical candidate is locally complete and globally rejected
  for any reads-from/coherence witness; wrong X replies are rejected too.
  K=0 permits X=W=H without any float representation, and M=0/N=0 permits all
  bases=1, K=2^32-1 and uninitialized inputs. Stream tests reject stale heaps
  and omitted output bytes. Negative evaluator cases cover live overlap,
  full-word wrap, insufficient second-plane storage and wrong high u32 bytes.
- Remaining: combine full-source/global memory/independent legal witnesses and
  complete three-stage composition. The MoE case remains `partial`. Broader
  atomics/shuffle, Ampere/Hopper, the concrete async/Iris/runtime connection,
  full ISA/observer correspondence and unconfirmed exact 81-form inventory are
  still part of the original goal. No smaller completion target was introduced.
- Cost/boundary: no performance optimization, throughput/latency/memory benefit,
  controlled manual/agent comparison or new arbitrary IEEE/bit equality result
  was measured. Exact logits/token requirements remain unchanged. No PTX or GPU
  runner changed this round. All twelve positive GPU source hashes and fifteen
  assembly source hashes match the earlier successful reports; those eighteen
  exact-byte cases plus one completion-only case are retained finite evidence,
  not a newly executed GPU suite or a consequence of these exact-real proofs.
- Next implementation step: certify combine's actual PC=0 parameter/index and
  mask prefixes, u32 route read, expert-plane address selection, single H load
  and Y store/return. Then derive route agreement before selected-H input
  agreement, unique Y writers and the universal gather output/frame contract;
  construct its independent checked complete witness and publication. Compose
  route/expert/combine using the existing append/nonvacuity rules, deriving
  preservation of X/W/R/H input bytes from each stage's frame and layout
  separation rather than assuming successor initialization.
- Validation: the complete gate passed 26 Rust tests, formatting/clippy, fifteen
  regenerated AST comparisons, the full Lean build, 1763 audited declarations
  and 64 evaluated false assertions rejected. A high-u32-byte negative was
  corrected to inspect the integer-byte projection: direct symbolic-byte
  equality lacked a decidable instance, so that diagnostic was not accepted as
  a successful rejection. The corrected evaluator proves the proposition false.
  Eleven new expert global/test modules total 1360 lines and 101 theorems;
  the two reusable integer-memory rules bring this round's audit additions to
  103. Individual cached expert global modules checked in approximately
  1.7--2.3 Lean seconds, and stream publication in 1.9 seconds. These are module
  observations, not end-to-end performance or controlled proof-cost comparisons.
  Metadata validation, Python compilation and tracked/untracked whitespace
  checks passed. Existing matmul, route, attention, atomic and stream contracts
  and independent legal witnesses passed the same gate. Other project work was
  left untouched.
- Agent-accounting snapshot at 2026-11-05 04:01:48 UTC: the goal ledger reported
  3,747,258 cumulative tokens versus 3,549,462 at this continuation's recorded
  start, a difference of 197,796. This interim snapshot includes the global
  proof work across the context continuation; it is not final billed usage or
  a controlled cost comparison. The full original goal remains active. Expert
  stage completion does not complete MoE, broader instruction support or the
  runtime/Iris proof boundary.


## Round: full combine and composed three-kernel MoE (2026-11-05)

- Instance/limit: route and expert had current-model universal contracts and
  independent legal witnesses, but combine's actual source and global contract
  and the three-stage successor-initialization argument were missing. Finite
  queued GPU chains did not close those proof obligations.
- Source: sixteen `MoeCombine*` modules connect actual PC=0 parameters, 2-D
  indices, masks, u32 route load, both expert-plane paths, H/Y addresses and
  load/store/return. Valid branches take 38/41 steps, masks 18/20, invalid routes
  25 after one R read. Arbitrary successful completion supplies the integer and
  f32 reply types and the actual three-event gather trace. Full four-byte bounds,
  alignment and source-aware checked admission remain explicit.
- Global combine: immutable R/H and unique Y writers imply race freedom even
  before route agreement. Four-byte u32 consistency identifies the selected
  route; selected H representation identifies the exact-real gathered answer.
  Universal output/frame correctness and complete checked consistency/observer
  witnesses are independent. Only selected H values require initialization.
  Actual Y write coverage establishes successor publication and whole-heap frame.
- Pipeline: `MoePipeline` composes actual route/expert/combine with independent
  dimensions/layouts/launches connected by equality fields. Entry requires G/X/W
  only. Route output and frame derive expert R/X/W input; expert output and
  frame derive combine R/H input. The final result implies independent
  `Moe.Post`, preserving every global byte outside R, selected H and Y words.
  Separate nonvacuity constructs legal completed boundaries and uses the same
  readiness lemmas. Observer domains cover actual writes and shared memory is
  initialized separately for each stage. No precomputed R/H/Y or assumed
  already-complete launch is inserted into the pipeline precondition.
- Reuse: existing unsigned compare/branch, typed load extraction, scalar update,
  immutable-read/unique-writer race, full-u32 agreement, exact-real observation
  and stream append/split/publication rules support the gather and composition.
  Conditional cross-stage X/W versus R separation permits dead-region aliases.
  This is baseline engineering, not a new asynchronous ownership protocol,
  performance optimization or claimed research novelty.
- Tests: poison R/H/Y before the stream and prove those representations absent;
  mixed [0,1,0] routes give [12,20,12] Y rows and retain unselected-plane sentinels
  across non-unit expert/combine launches. Separate legal pipeline witnesses
  cover K=0/X=W=H, N=0 dead aliases, and M=0/all pointers=1/maximum u32 K with
  every byte preserved. N=0 still executes route, so live R/G remain aligned.
  Gather tests construct locally complete typed-but-wrong R/H candidates and
  reject their memory conditions for every rf/co; invalid route 17 exits without
  H. Incomplete Y coverage, overlap, full-word wrap, stage inventory order and
  poisoned-entry assertions are also checked. The inventory-order assertion is
  a structural negative, not a theorem excluding every alternative stage order.
- Remaining: the three-stage current-model mathematical contract and independent
  complete legal pipeline now exist. The case remains partial at the full
  coverage boundary: physical allocation/UB, full PTX/observer/runtime/proxy and
  augmented-graph correspondence, universal IEEE behavior and arbitrary GPU bit
  equality are not established. Broader atomic/shuffle forms, Ampere async
  copy/MMA, Hopper TMA/mbarrier/WGMMA, the actual in-flight Iris bridge and the
  exact unconfirmed 81-form inventory remain required by the original goal.
- Cost/boundary: no throughput, latency, memory benefit, controlled manual/agent
  comparison or new hardware run was measured. Exact logits/token requirements
  are unchanged. No PTX or GPU runner changed, and all twelve positive GPU and
  fifteen assembly source hashes match the existing successful reports. Their
  eighteen exact-byte cases plus one completion-only case remain finite
  evidence separate from these exact-real proofs. Other project work is intact.
- Validation: the complete gate passed 26 Rust tests, formatting/clippy, fifteen
  regenerated-AST comparisons, the full Lean build, 1887 audited declarations
  and 72 evaluated false assertions rejected. Twenty new source/global/pipeline/
  test modules total 2183 lines and 124 explicitly audited theorems. Source body
  and whole-entry modules checked in approximately 1.6/1.5 cached Lean seconds,
  gather witness tests in 2.1 seconds and the full pipeline regression module in
  3.7 seconds. These are module observations, not end-to-end proof cost or
  performance measurements. Metadata validation, Python compilation and
  tracked/untracked whitespace checks passed. No new axiom, unsafe declaration,
  unproved assumption or numerical tolerance was added. Existing contracts,
  independent witnesses and asynchronous/Iris regressions passed the same gate.
- Agent-accounting snapshot at 2026-11-05 04:31:39 UTC: the goal ledger reported
  3,876,727 cumulative tokens versus 3,749,247 at this continuation's recorded
  start, a difference of 127,480. This is an interim snapshot, not final billed
  usage or a controlled agent/manual comparison. The full original goal remains
  active. The next required case is Ampere tiled matmul with actual async-copy/
  MMA semantics and proof boundaries; MoE current-model completion is not
  substituted for those or for full ISA/runtime correspondence.


## Round: Ampere cp.async source identities and wait graph (2026-11-05)

- Instance/limit: the next required Ampere tiled matmul needs asynchronous
  transfer events outside issuer PO. The ordinary scalar graph and existing
  abstract host-stream loans did not provide source-level copy identities or
  committed/uncommitted group frontiers. Treating a copy as an ordinary store
  at issue would give the wrong synchronization model.
- Implemented: strict Rust AST/parser/serializer support for the explicit sm_80
  non-bulk copy/group forms, plus typed `Ampere.Instr` data. A separate source
  interpreter preserves existing scalar PCs and semantics while recording
  actual copy bytes, ordinals and group counters. Shared-symbol allocation now
  honors 4/8/16-byte alignment with padding and overflow checks; old align-4
  fixtures retain their generated offsets. Optional operands/qualifiers, bulk
  copies and MMA remain rejected. No instruction/directive is silently erased.
- Source evidence: arbitrary finite source runs preserve/extend their copy
  ledger and never fabricate entries. Source emission and final-ledger lookup
  correspond in both directions for well-formed candidates. The byte oracle
  supplies candidate payloads, not an assumed initialized-memory value; future
  memory consistency must constrain those payloads. Source completion alone
  remains distinct from legal memory execution.
- Graph evidence: separate copy-read/write nodes do not belong to issuer PO.
  Source-before-issue, intra-copy, own-group wait and CTA propagation relations
  compose through the existing generic path rules. A no-wait/no-outgoing-path
  theorem prevents bar.sync alone from publishing a copy. Commit/barrier events
  and peer-thread waits are explicitly excluded as copy completion. Tests use
  actual generated complete source traces and distinguish recent and open
  groups rather than assuming all prior instructions completed at a wait.
- Reuse/new method: scalar source execution, typed programs, byte payload
  accessors and path closure are reused. Evolution/source-origin lemmas support
  arbitrary loop counts and later buffer reuse. This is semantic infrastructure
  and baseline engineering, not a new proven async ownership method, measured
  performance optimization or replacement for the tiled-MMA case.
- Tests: accepted/rejected frontend forms retain cache, width, address offsets,
  target and instruction slots. Unsupported types/optional operands/counts and
  padding overflow fail closed. Three generated fixtures cover waited copy,
  multiple committed/open groups and missing wait. Their source/graph proofs
  include actual completion and the absence of false copy publication without
  a wait. A malformed sixteen-byte reply is rejected; older program and proof
  regressions remain in the complete gate.
- Remaining: generalized augmented rf/co/taint/observer and construct predicates,
  allocation/UB and source-aware barrier legality, universal copy data agreement
  and independent legal complete memory witnesses. Then implement packed f16
  operands, actual MMA fragment/warp collective semantics and the complete
  arbitrary-tile/K-loop kernel, including safe shared-buffer reuse. Hopper,
  broader atomics/shuffle, the concrete Iris/runtime bridge and the exact
  unconfirmed 81-form inventory remain in the full original goal. The new
  async-copy helper is partial; Ampere tiled matmul remains planned.
- Native evidence: the full GPU suite was rerun on the existing sm_89 device.
  The new waited-copy test compares all sixteen output bytes and a nonzero
  four-byte guard. Missing-wait source is never executed. Assembly uses each
  fixture's actual target: fifteen prior sm_70 and three new sm_80 fixtures.
  The reports distinguish assembly, finite execution and current formal scope.
  No throughput/latency/memory improvement, controlled agent/manual comparison,
  arbitrary IEEE/bit equivalence or weakened logits/token target is claimed.
- Validation: the complete gate passed 30 Rust tests, formatting/clippy, eighteen
  regenerated-AST comparisons, the full Lean build, 1951 audited declarations
  and 79 evaluated false assertions rejected. Six new Ampere source/graph/test
  modules total 698 lines and 64 explicitly audited theorems. Source-rule and
  provenance modules checked in approximately 1.0/2.1 cached Lean seconds;
  generated-source regression checks took 2.6 seconds. These are module
  observations, not end-to-end proof cost or optimization measurements. Latest
  coverage metadata independently validates twelve capabilities/eleven cases;
  Python compilation, theorem-audit completeness and tracked/untracked whitespace
  checks pass. Existing scalar, MoE, atomic, stream and Iris proofs remain in the
  same gate. No new axiom or numerical tolerance was added.
- Hardware validation: CUDA 12.8.93 ptxas accepted eighteen fixtures at recorded
  per-fixture targets. The full native suite passed nineteen exact-byte cases
  and one completion-only test on the RTX 4060 Laptop sm_89. Thirteen positive
  GPU source hashes and eighteen assembly hashes match current files. The
  no-wait fixture is excluded from native execution. Other project work and
  system drivers were left untouched.
- Agent-accounting snapshot at 2026-11-05 04:56:54 UTC: the goal ledger reported
  4,010,428 cumulative tokens versus 3,879,868 at this continuation's recorded
  start, a difference of 130,560. This interim snapshot is not final billed
  usage or a controlled comparison. The original goal remains active; source
  and copy-order foundations do not complete augmented memory/observer rules,
  packed-f16/MMA, the full tiled kernel or the required Iris/runtime connection.


## Round: graph-generic memory and Ampere visibility fragment (2026-11-05)

- Instance/limit: async copy nodes are outside issuer PO and need distinct logical
  agents for moral strength as well. Reusing ordinary EventId/thread equality
  would silently grant a copy the issuer's same-thread guarantees. Ordering-only
  copy lemmas cannot constrain data or synchronized final observations.
- Method: `MemoryGraph/Core.lean` parameterizes the existing generic-proxy memory
  rules by actual nodes, agents, PO and base order. Physical owners remain available
  separately for scope membership. A proved source encoding is isomorphic to
  optional writer nodes. The fragment includes read/write projections, rf/co,
  observation/RMW chains, causality, races, mixed-size relaxation, taint,
  single-copy/RMW atomicity and SC-per-location. It introduces no new model axiom.
- Preservation/reuse: `Ordinary.lean` proves an iff for the complete old generic
  memory conditions against the new fragment plus the old barrier participation
  and control obligations. It also proves synchronized observer equivalence.
  The original ordinary predicates and kernel contracts are unchanged. Generic
  byte-visibility rules, race symmetry, unique-writer consistency witnesses and
  actual-write-selected complete observation witnesses work for either source
  encoding and arbitrary node types. A rank certifies one chosen witness only;
  universal correctness is not restricted to rank-ordered executions.
- Ampere: `Ampere/Memory.lean` adapts actual candidate kinds, nodes, completion,
  PO and base paths. Copy agents differ from thread agents and from different
  copy identities; copy nodes are not RMWs, and copy writes are not morally
  strong with thread events. The waited unique-copy visibility rule quantifies
  over every rf/co satisfying the memory fragment, provided eligibility, the
  actual wait/PO edge and the unique write have been proved. It assumes no read
  value, artificial issuer PO or desired scheduling order.
- Evidence/limit: `Tests/MemoryGraph.lean` constructs independent consistent memory
  and complete global observation witnesses on a small graph for an arbitrary
  natural-number byte value. For all legal rf/co, its ordered read selects the
  write; removing completion order produces a race and taint/ineligibility.
  This is a model-level regression, not a complete legal PTX source witness.
  Two additional evaluated false propositions reject confusing copies with their
  issuer and confusing two copy agents. Eight new modules total 957 lines and
  add 77 explicitly audited theorem declarations.
- Outstanding: source-aware async construct/barrier legality, deriving actual
  helper-wide eligibility and uniqueness, universal source/output/frame proofs
  and independent complete legal source/memory witnesses remain open. MMA/f16
  layouts, required Ampere tiled matmul, Hopper, Iris/runtime/ISA connections and
  the unconfirmed exact 81-form inventory remain in the original active goal.
  This fragment is not full PTX admission or a completed Ampere acceptance case.
  No numerical tolerance or logits/token target was weakened.
- Native evidence: no PTX fixture, Rust frontend or GPU/assembler harness changed
  in this round. All 13 prior GPU-report source hashes and all 18 assembly-report
  fixture hashes were checked unchanged; native execution was not rerun. Existing
  reports remain finite execution/assembly evidence, separate from these proofs.
- Performance and cost: this work adds verification infrastructure; no throughput,
  latency, memory, novelty or agent-ablation result is claimed. The continuation
  began at the recorded ledger of 4,014,019 cumulative tokens. Validation and a
  final cost snapshot are recorded below after the aggregate gate completes.
- Validation: the aggregate `scripts/check.sh` gate passed: 30 Rust tests,
  eighteen regenerated AST comparisons, the complete Lean build, 2028 audited
  declarations and 81 evaluated false assertions rejected. Coverage metadata,
  Python compilation, complete new-theorem audit entries and tracked/untracked
  source whitespace checks passed. GPU and PTX assembly were not rerun; the
  unchanged native evidence hashes above were verified separately.
- Cost snapshot at 2026-11-05 05:18:43 UTC: the goal ledger reports 4,158,250
  cumulative tokens, a difference of 144,231 from the recorded continuation start
  of 4,014,019. This includes the prior context and implementation/debugging/checks
  in this continuation; final reporting adds more tokens. No cost cap was set.
  The original goal remains active.


## Round: source-aware Ampere barrier/control admission (2026-11-05)

- Previous turn: progress. The graph-generic memory/observer fragment and its
  ordinary equivalence adapter were implemented and passed the aggregate gate.
  This round addresses the next missing construct obligation rather than calling
  that fragment full async PTX admission.
- Instance/limit: source-local barrier returns are emitted without waiting for
  peer threads. Matching a barrier resource and generation in the event graph
  alone can therefore accept different source PCs. Allowing completed peers to
  exempt one another can also invent a circular execution. Async event slots
  must remain in source positions and in the relevant control order.
- Method: `Ampere/Origins.lean` uses the shared SourceRun instrumentation on the
  actual Ampere interpreter and its full state. Plain/located execution erasure
  and event provenance are proved for arbitrary finite counts. Every barrier
  arrival/return originates at a scalar barrier instruction at the actual PC.
  `SourceAligned` requires matched synchronization events to share that PC.
  Unique static sites suffice, but are not required: dynamic matching can accept
  different source sites in separate generations. Source PCs are not supplied
  by the oracle or recovered from a replacement scalar execution.
- Checked admission: `Ampere/Checked.lean` combines source production, actual
  barrier-PC matching, participation by all CTA traces or justified exited-peer
  exemptions, control acyclicity and the augmented memory fragment. Control
  includes all async base edges and the separate exit-before-return edges.
  Control acyclicity implies base acyclicity. Exiting does not complete a copy;
  exit control edges are not memory-causality edges. A rank is only a sufficient
  construction for an individual witness, not a universal execution restriction.
- Source reconstruction: `Ampere/Trace.lean` proves full-state run splitting,
  successful prefix/step inversion and uniqueness of completed finite source
  runs. Pending copy ledgers and query positions are preserved; no fixed fuel
  bound, termination guarantee or desired reply is assumed. These rules prepare
  reconstruction of arbitrary complete copy-helper traces.
- Evidence/reuse: the actual generated sixteen-byte helper has source-PC
  alignment at PC 5, full-CTA participation and an acyclic control graph including
  copy read/write and wait edges. A second source with matching barrier numbers
  at PCs 6 and 3 has complete, provenance-checked traces and is rejected by
  source matching. A two-thread different-resource source has complete produced
  traces and passes participation (each can claim the other exited), but its
  concrete two-edge control cycle rejects checked admission for every rf/co.
  A repeated-barrier source with intervening commit/wait_all has distinct static
  sites and is dynamically aligned by generation; its two-thread source coverage
  and local completion are independently proved. These reuse the shared located
  execution framework and existing scalar barrier-origin theorem.
- Tests: `Tests/AmpereOrigins.lean` contains the positive and negative source
  cases; two additional evaluated false propositions reject dropping async PC
  slots and identifying divergent source PCs. Four new modules total 612 lines,
  with two additional candidate-lookup lemmas in Source. The gate audits all 59
  new theorem declarations. Malformed or circular source cases are Lean-only
  regressions and were not submitted to the GPU.
- Remaining boundary: the helper's existing source-only launch uses a sentinel
  initial map; its source/construct evidence does not assert that those oracle
  payloads form a legal complete memory execution. A fixed represented input
  map, derived eligibility/unique writes, universal helper value/frame correctness
  and an independent full source/rf/co/observer witness are still required.
  Remaining async ISA/UB/storage obligations, MMA/f16 layouts, tiled matmul,
  Hopper, Iris/runtime/ISA bridges and the exact unconfirmed 81-form inventory
  stay in the original active goal. No new semantic axiom or relaxed numerical
  target was introduced.
- Native/performance evidence: no PTX, frontend, native harness or native report
  changed. All 13 GPU fixture hashes and 18 assembly fixture hashes were checked
  unchanged; native execution/assembly were not rerun. No throughput, latency,
  memory, novelty or agent-ablation result is claimed. This is verification
  infrastructure and baseline source admission, not an optimization experiment.
- Cost: this continuation began at the recorded ledger of 4,160,289 cumulative
  tokens. The final validation and cost snapshot follow after the aggregate gate.
- Validation: `scripts/check.sh` passed 30 Rust tests, eighteen regenerated AST
  comparisons, the full Lean build, 2087 audited declarations and 83 evaluated
  false assertions rejected. Coverage metadata, Python compilation, complete
  new-theorem audit entries and tracked/untracked source whitespace checks passed.
  The native fixture hashes above were separately verified unchanged.
- Cost snapshot at 2026-11-05 05:36:39 UTC: the goal ledger reports 4,239,889
  cumulative tokens versus 4,160,289 at this continuation's start, a difference of
  79,600. Final reporting adds more tokens. No budget cap was set. The original
  full goal remains active; this round does not complete the Ampere case.


## Round: universal actual cp.async helper data/frame proof (2026-11-05)

- Previous turn: progress. Actual Ampere source-PC instrumentation and checked
  barrier/control admission were implemented and passed the aggregate gate.
  This round addresses the source/data bridge that those construct facts lacked.
- Instance/limit: the actual generated helper issues one sixteen-byte copy and
  uses four shared u32 loads/global stores after commit/wait/barrier. Its original
  concrete source trace did not constrain the independent copy/read oracle data.
  Neither source completion nor an ordering path implies input/output values.
- Independent specification: `CpAsyncCopySpec` specifies sixteen-byte copy and
  preservation of every other observed global arena byte. Layout is explicit:
  one CTA/thread, a bounded finite global arena, sixteen-byte aligned source,
  four-byte aligned destination and disjoint input/output ranges. Four bounded
  represented u32 inputs prepare a separate legal-execution existence proof.
  No expected output or desired read value appears in the precondition.
- Source reconstruction: `CpAsyncCopyTrace/Source` prove actual parameter setup,
  issue/commit/wait/barrier, four load/store pairs and return. Copy payload and
  scalar replies are independent throughout source execution. For any successful
  complete finite run, prefix/step inversion derives payload length sixteen,
  integer replies at queries 1..4 and exactly fifteen source instructions.
  There is no caller fuel bound, termination premise or assumed reply shape.
  Both addresses and the four scalar values are parameters.
- Graph connection: `CpAsyncCopyGraph` constructs a separately source-produced
  representative family, and proves every complete well-formed candidate has
  exactly one launched trace and the same augmented memory view as some family
  member. `Ampere.memoryGraph_eq` proves this view depends on actual events,
  recorded copies and completion, not unused oracle metadata. This transports
  arbitrary rf/co and observer conditions without selecting a sequential witness.
- Memory proof: actual read/write classifications, generic graph footprint bounds
  and source-derived wait/PO paths establish input immutability, unique tile and
  output writers and race freedom for every rf. Async writes and scalar accesses
  remain different agents. In particular tile-copy/load ordering uses the actual
  own-group wait; it is not silently issuer PO or same-agent strength. Eligibility
  is derived from race freedom and is not a kernel precondition. Copy-read value
  agreement forces all sixteen payload bytes to the initial source; unique-writer
  visibility then forces the four shared read values and final output bytes.
- Universal result: `CpAsyncCopyCorrect.correct` proves the actual source's
  CheckedTriple against the independent Post for every admitted complete source
  candidate, rf/co and synchronized observer on the full finite global arena.
  All sixteen destination bytes equal the initial source bytes; every other arena
  byte is preserved. Physical allocation/UB, full ISA/runtime/observer
  correspondence and any wider SIMT geometry remain outside this helper result.
- Tests: the represented sample is [7,max-u32,42,99] with source 64, destination
  128 and a 160-byte arena. Correct and wrong-answer/wrong-payload candidates have
  separate actual source coverage and local completion proofs. The two malformed
  candidates are rejected by memory constraints for every rf/co using the derived
  eligibility, not an additional caller assumption. Two evaluated false assertions
  reject forgetting the copy's query and treating its payload as a single word.
  Seven new modules total 836 lines; reusable graph footprint/view rules plus the
  new source/memory/spec/test proofs add 54 explicit theorem audit entries.
- Nonvacuity remains required: the positive sample has source and represented
  input evidence, but no independent complete checked source/rf/co/observer
  witness has yet been established. Universal output correctness is not reported
  as nonvacuity. The next construction will choose represented input words,
  derive byte agreement, certify one explicit memory witness and then obtain its
  observation from actual writes. The helper remains partial and does not replace
  the required Ampere tiled MMA matmul. MMA/f16, Hopper, Iris/runtime/ISA bridges,
  the exact unconfirmed 81-form inventory and all other original goal duties stay
  active. No numerical target or original goal scope was weakened.
- Native/performance evidence: no PTX, Rust frontend, GPU/assembly harness or native
  report changed. All thirteen GPU and eighteen assembly fixture hashes were
  checked unchanged; native execution/assembly were not rerun. No performance,
  novelty or agent-ablation result is claimed for this baseline proof work.
- Cost: this continuation began at the recorded ledger of 4,242,040 cumulative
  tokens. Final gate validation and a cost snapshot follow when it completes.
- Validation: `scripts/check.sh` passed 30 Rust tests, eighteen regenerated AST
  comparisons, the full Lean build, 2141 audited declarations and 85 evaluated
  false assertions rejected. Coverage metadata, Python compilation, complete
  new-theorem dependency audit entries and tracked/untracked source whitespace
  checks passed. Existing GPU/assembly fixture hashes were separately verified.
- Cost snapshot at 2026-11-05 06:06:33 UTC: the goal ledger reports 4,339,829
  cumulative tokens versus 4,242,040 at this continuation's start, a difference of
  97,789. Final reporting adds more tokens. No budget cap was set. The original
  goal remains active; helper nonvacuity and the full Ampere case are unfinished.


## Round: complete copy witnesses and MMA fragment foundation (2026-11-05)

- Previous turn: progress. The actual copy helper gained arbitrary-complete-run
  source reconstruction and an all-candidate output/frame theorem. This turn
  closes its independent nonvacuity obligation and begins the required MMA layer.
- Copy instance/limit: universal partial correctness alone does not demonstrate
  that the source, memory and observer constraints admit any completed behavior.
  A source-only local trace is insufficient; an observer output cannot simply
  be set to the desired postcondition.
- Witness construction: `CpAsyncCopyPayload` assembles sixteen bytes from the four
  bounded words represented by the fixed initial map and proves the bytewise
  representation. It also proves uniqueness of every actual writer. The
  `CpAsyncCopyControl` family certifies actual issue/internal/wait/barrier/PO base
  edges with a rank, full-CTA participation and absence of circular exited-peer
  exemptions, independently of payload/scalar values.
- `CpAsyncCopyWitness.memory_witness` chooses explicit bytewise sources: the copy
  reads initialization; scalar shared loads read its independent copy-write node.
  Actual value agreement, read-source rank and absence of stale/future sources
  certify InitialCo through the existing graph-generic consistency constructor.
  Source provenance, barrier-PC alignment and control obligations are separately
  assembled into checked admission. The observer uses actual emitted writers and
  retains initial bytes elsewhere via the generic unique-writer construction.
- Independent nonvacuity: `CpAsyncCopyGraph.nonvacuous` now constructs a complete
  checked source/rf/co/observer execution for every launch under the SAME Pre as
  universal correctness. It neither invokes the output theorem nor adds an oracle
  equality, output hypothesis or narrower launch precondition. The represented
  [7,max-u32,42,99] sample has a concrete checked candidate and observer; copied
  first/high bytes and an untouched guard are derived from Post. This completes
  the helper's current-model universal/nonvacuity/instance evidence, not full
  ISA/storage/runtime correspondence or the required tiled MMA acceptance case.
- MMA instance/limit: tiled matmul needs all 32 lanes' distributed f16 operands
  and f32 accumulators to denote the same matrices. Treating lane registers as
  already-assembled matrices would omit missing/duplicated coordinates and
  packed-half ordering. The coordinate reference was checked against
  [NVIDIA PTX ISA 9.5 section 9.7.16.5.8](https://docs.nvidia.com/cuda/parallel-thread-execution/).
- MMA method: `MmaLayout` proves inverse coordinate/owner maps and bijections for
  A/B/C. `MmaFragments` proves gather/scatter identities for arbitrary element
  types and exact-real matrix-step arithmetic for all matrices. `MmaPacked`
  reversibly groups scalar slots into four A and two B logical f16 pairs per lane.
  `PackedF16` encodes two existing symbolic f16 values, proves exact decode/encode
  correspondence and injectivity, and rejects integer storage. No IEEE bit
  reinterpretation or new numerical assumption is introduced.
- Regressions: coordinate boundary/high-row/high-K cases, labeled packed halves,
  arbitrary-cell identity-matrix multiplication with a nonzero accumulator, a
  final-cell numeric result and symbolic f16 storage rejection are proved. Four
  additional evaluated false assertions reject misplaced A/B/C coordinates and
  accepting integer bits as a packed float pair. Nine new modules total 590 lines;
  these and the refactored sample-input lemma add 68 explicitly audited theorems.
- Frontier: these MMA layout/storage/arithmetic facts do NOT constitute actual
  MMA parsing, named register-bank execution, source/warp matching or a legal
  mma.sync execution witness. The frontend still rejects MMA. Actual tiled source,
  K-loop accumulation, shared-buffer reuse, full universal/nonvacuity and native
  evidence remain required for the [paper's Ampere case](https://sf-tensor.com/papers/formalizing-ptx.pdf).
  The original Hopper, broader instruction, Iris/runtime/event connection and
  unconfirmed exact 81-form inventory duties remain active. No accepted goal
  requirement or exact logits/token target was weakened.
- Native/performance evidence: no PTX fixture, Rust frontend, native harness or
  native report changed. The thirteen GPU and eighteen assembly fixture hashes
  were separately checked unchanged; native execution/assembly were not rerun.
  No performance, novelty or agent-ablation result is claimed for this baseline
  formalization work. The MMA arithmetic existence lemma is mathematical only,
  and is not reported as source execution evidence.
- Cost: this continuation began at the recorded ledger of 4,341,972 cumulative
  tokens. Final gate validation and a cost snapshot follow after completion.
- Validation: `scripts/check.sh` passed 30 Rust tests, eighteen regenerated AST
  comparisons, the full Lean build, 2209 audited declarations and 89 evaluated
  false assertions rejected. Coverage metadata, Python compilation, complete
  new-theorem dependency audit entries and tracked/untracked source whitespace
  checks passed. Existing native fixture hashes were separately verified.
- Cost snapshot at 2026-11-05 06:27:20 UTC: the goal ledger reports 4,443,088
  cumulative tokens versus 4,341,972 at this continuation's start, a difference of
  101,116. Final reporting adds more tokens. No budget cap was set. The original
  goal remains active; full MMA source/warp/tiled-kernel integration is unfinished.


## Round: MMA source/register/warp integration (2026-11-05)

- Instance and previous limit: the required Ampere tiled matmul needs actual
  source loads, packed register operands and a whole-warp arithmetic operation.
  The preceding round supplied only layout/packing mathematics. Treating a
  single lane's output oracle as matrix arithmetic would admit arbitrary results.
- Frontend: add the exact f16 m16n8k16 row.col/f32 MMA form and global/shared b32
  word loads, preserving all four operand vectors and actual source slots. The
  first pass tracks operand braces. Strict arity, declaration/type, duplicate D,
  target, unsupported shape/format/qualifier, predication and malformed vector
  regressions reject unsupported inputs. D/C aliasing remains accepted. Rust
  stores the register vectors behind boxes to keep AST variants bounded; Clippy
  passes with warnings denied.
- Source method: packed word loads choose a symbolic f16 pair or integer bytes,
  emit the corresponding memory read, and clear conflicting register banks.
  Scalar and MMA overwrites also invalidate stale packed representations. MMA
  captures six input pairs and four old accumulators before writing D, advances
  the actual PC/query/call counters once, and emits actual entry/return events.
  PC, warp, lane and dynamic ordinal come from execution and launch geometry,
  independently of the output oracle. Integer bits do not become packed f16.
- Warp method: mandatory `CheckedConditions.mma` matches actual source-located
  events from all 32 lanes at the same CTA/warp/PC/call ordinal, and constrains
  each output with packed fragment arithmetic. `matched_mma_output` connects
  represented actual inputs to the independent parameterized matrix step. It
  supplies a reusable operation rule, not a kernel correctness assumption.
- Control method: MMA rendezvous enters `ControlEdge` acyclicity, alongside base
  and exited-peer edges, while remaining absent from memory `BaseEdge`. The
  source/participation reference is the [NVIDIA MMA instruction
  description](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#warp-level-matrix-instructions-mma).
  No undocumented memory fence is granted. A synthetic mixed MMA/barrier cycle
  is rejected, and the rendezvous is proved not to be a memory base edge in that
  graph. This graph-level negative is not labelled a source witness.
- Reuse: existing copy correctness and independent memory/source witnesses still
  compile with the stronger checked interface; absence of MMA is derived from
  their actual code/events. General bank invalidation applies to scalar, word
  and MMA writes. The matrix rule is parameterized over represented A/B/C,
  rather than specialized to the numerical smoke test. No novelty claim is made.
- Formal instances: the generated 25-instruction probe completes locally with
  unrelated output answers, but a one-lane launch is rejected by checked MMA
  admission for every rf/co. Tests exercise old-C capture with D/C aliasing,
  integer/float invalidation of packed inputs, distinct D and actual metadata.
  A separate all-ones 32-lane source candidate has launch-wide WellFormed,
  Complete and MmaConditions proofs, with actual source PCs and output 16.
  This is finite source/warp-arithmetic nonvacuity, not a full legal memory
  witness; its initial map is a placeholder and no memory/observer admission is
  claimed. Its Lean module built in 92 seconds in this round.
- Native evidence: `mma_probe.ptx` executes a full 32-thread warp with independently
  serialized small exact f16 matrix inputs. An independent rational 16x8x16 host
  matmul checks all 128 f32 results and four guard floats, totaling 528 bytes.
  The RTX 4060 Laptop sm_89 report was refreshed at 06:55:09 UTC: 20 exact-byte
  cases and one completion-only case, with 14 executed fixture hashes. Assembly
  evidence at 06:55:07 UTC covers 19 fixtures, using ptxas 12.8.93 and per-fixture
  sm_70/sm_80 targets. Both reports' source hashes were rechecked. These finite
  executions do not establish general IEEE, compiled-kernel or exact-logit
  equivalence. No performance optimization or speedup is claimed.
- Gate: `/tmp/ptx-mma-source-check.log` passed formatting, 32 Rust tests, Clippy
  with warnings denied, 19 generated AST comparisons, the full Lean build,
  2281 audited declarations, 95 evaluated false assertions rejected and assembly
  of 19 fixtures. The audit adds 72 explicit entries; only the existing allowed
  standard Lean axioms occur. Coverage metadata remains 12 capabilities/11 cases.
- Remaining frontier: independent full memory-admitted MMA source/rf/co/observer
  witnesses; parameterized tiled K-loop correctness and nonvacuity; shared-buffer
  reuse and complete async/ISA/storage correspondence. Hopper, broader atomic/
  shuffle support, in-flight Iris/runtime bridges and the exact unconfirmed
  paper 81-form inventory remain in the original active goal. The fragment probe
  does not replace the required Ampere tiled matmul case or weaken its target.
- Cost snapshot at 2026-11-05 07:13:17 UTC: the goal ledger reports 4,667,530 tokens,
  compared with the preceding published snapshot of 4,443,088, a difference of
  224,442. This is an interim ledger snapshot, not final billed usage. The goal
  remains active and the original acceptance requirements are unchanged.


## Round: complete MMA probe memory witness and actual tiled source (2026-11-05)

- Instance and previous limit: the preceding MMA probe proved source completion
  and full-warp arithmetic with a placeholder initial map, leaving actual memory
  agreement and observer admission open. Tiled shared reuse also needs repeated
  writes to the same byte, beyond the generic unique-writer witness constructor.
- Source-derived MMA inventory: `MmaWarpGraph` derives every actual read/write
  from the generated full-warp traces. It exposes six packed reads and four
  output writes per lane and proves there are no copy nodes. `MmaWarpMemory`
  supplies a separate represented all-ones input map, proves input/output
  separation, unique output-byte writers and race freedom for every rf. The
  original integer-sentinel placeholder fails memory constraints for every rf/co;
  completing source/warp arithmetic cannot admit that incorrect input map.
- Complete numerical probe witness: `MmaWarpControl` certifies actual program,
  base and MMA control edges with a rank. Source/barrier analysis proves that
  the probe has no barriers/copies; MMA entry/return positions are derived from
  actual trace tags. `MmaWarpWitness` independently constructs complete checked
  source/rf/InitialCo/observer witnesses for the represented 32-lane instance.
  Every f32 output byte is derived as encoding of 16 and the output guard is
  preserved. The observer covers the 1284-byte global arena. No kernel output
  theorem is assumed in constructing the witness. This is a finite numerical
  instance, not a parameterized MMA/tiled kernel contract.
- Repeated-write method: `MemoryGraph/RankedWitness` generalizes the existing
  ordinary event-graph rank/co construction to arbitrary nodes and source
  encodings, including independent async operation agents. Per-witness proof
  duties cover actual read values, rank-respecting po/base/rf/fr, race freedom
  and per-byte writer-rank injectivity. The theorem derives all seven current
  memory-condition fields, including SC and RMW atomicity. It adds no kernel
  precondition or restriction to allowed-execution definitions.
  `RankedObservation` selects a maximal actual writer from a finite inventory
  that must cover every emitted write. The rank is a sufficient construction
  certificate for one witness. This is engineering reuse of an existing method;
  no novelty claim is made.
- Reuse test: a model-level graph with two distinct operation agents writes 7,
  reads 7 and overwrites the same byte with 42. Memory/observer witnesses exist,
  the unique-writer premise is disproved, the observer returns 42 and a stale
  observer is rejected. This checks repeated-write construction, not PTX source
  or async-buffer-reuse correctness. The actual tiled loop still needs its own
  source-produced memory witness.
- Actual tiled source: `ampere_tiled_matmul.ptx` and its generated typed AST now
  contain 83 real instructions. A warp with block=(4,8,1) computes a 16x8 output
  tile, with row-major f16 A, column-major f16 B and row-major f32 C. Three
  8-byte copies per lane populate a declared 768-byte shared tile; wait/CTA
  publication precede six packed loads and MMA. A post-read CTA barrier precedes
  K+=16 and buffer reuse. Shared pointers explicitly reference the declared tile
  symbol; ptxas reports 768 bytes of shared memory. M/N/K must be multiples of
  16/8/16 and active buffers require bounds/alignment/separation.
- Local tiled source instance: an actual two-iteration, 106-step local run is
  proved successful and complete, with six recorded copies, two groups, 20
  queries, two MMAs, four dynamic barrier generations and 38 events. The second
  MMA captures C=16 and the final source store emits 32. Actual PCs 64/72
  alternate across publication/reuse generations; the loop is 57..77 and stores
  start at 78. The single-lane trace is not a full launch or checked memory
  witness. `uniqueBarrierSites` is false; dynamic source matching remains an
  obligation for the complete tiled proof. Proof reconstruction uses successful
  run extraction to avoid comparing two expanded full states. The final local
  module built in 16 seconds.
- Parameterized layout facts: `Ampere/TiledLayout` proves warp x/y coordinates,
  shared-copy bounds, unique copy-byte ownership, producer/consumer word offsets
  and A/B fragment-address equations for arbitrary valid x/y/register/half
  slots. It explicitly covers a word in the second half of an 8-byte copy.
  These are mathematical address facts that must still be connected to arbitrary
  actual source/register states and loop iterations. The module built in 1.1s.
- Native evidence: four tiled exact-byte cases check one tile, four CTAs with
  three K iterations, K=0 with unused A/B aliasing C, and extra inactive CTAs with
  two K iterations. All active input bytes remain unchanged and output guards
  survive. Independent rational matmul is used with exactly representable small
  input/product/sum values. The final sm_89 report at 07:46:53 UTC has 24 exact-
  byte cases plus one completion-only case and 15 executed fixture hashes. The
  assembly report at 07:47:15 UTC covers 20 fixtures with ptxas 12.8.93 and
  per-fixture sm_70/sm_80 targets. Final source hashes were rechecked. Earlier
  80-instruction development evidence was superseded after making shared base
  symbols explicit. No general IEEE/logit equivalence or speedup is claimed.
- Frontier: tiled independent specification, parameterized full-source/loop
  reconstruction, warp/CTA matching, memory values/races/shared reuse,
  universal output/frame correctness and independent complete legal execution
  witnesses under the same preconditions remain required. The generic repeated-
  write witness and fixed numerical probe do not close those obligations.
  Hopper, broader atomic/shuffle forms, Iris/runtime/ISA bridges and the exact
  unconfirmed 81-form paper inventory remain in the original active goal.

- Final gate: `/tmp/ptx-mma-memory-tiled-final.log` passes formatting, 33 Rust
  tests, Clippy with warnings denied, 20 generated AST comparisons, the full
  Lean build, 2360 audited declarations, 101 evaluated false assertions rejected
  and assembly of 20 fixtures. This round adds 79 explicit audit entries using
  only the existing allowed standard Lean axioms. Coverage metadata remains
  12 capabilities and 11 cases; the tiled case advances to partial, with its
  required parameterized proof/witness frontier stated explicitly.
- Cost snapshot at 2026-11-05 07:53:37 UTC: the goal ledger reports 4,817,420
  tokens versus the preceding published 4,667,530, a difference of 149,890.
  This is an interim ledger snapshot, not final billed usage. The full original
  goal remains active with no reduced acceptance requirements.

## Round: parameterized tiled source loop and phase visibility (2026-11-05)

- Instance and previous limit: the preceding tiled case had a complete fixed
  two-iteration local trace and mathematical fragment addresses, but no arbitrary
  K-loop induction or independent kernel specification. A unique-writer rule
  could not justify reads when successive copy groups reuse shared bytes.
- Reusable memory rule: `MemoryGraph/Rules.phase_writer_source` and
  `phase_writer_visible` derive the selected phase's rf source and value for
  every rf/co satisfying the current memory conditions. The proof requires an
  eligible actual read, the actual current write ordered before it, and an
  exhaustive classification of every other actual byte writer as the current
  writer, ordered before it, or ordered after the read. Earlier writes use
  coherence/no-stale; later writes use no-future. No desired value or selected
  rf is assumed. `Ampere/Memory.published_phase_copy_source/value` reuse actual
  copy-wait/CTA publication, allowing different issuer and consumer threads.
  The tiled source must still establish the order/race premises itself.
- Repeated-write reuse evidence: `Tests/MemoryGraphRanked` proves that its read
  selects the first write for every admitted rf/co, while the existing separate
  observer witness selects the later overwrite. Choosing the future write is
  rejected for every co. This remains a graph-level reuse example, not a tiled
  launch witness. These rules extend an existing method; no novelty is claimed.
- Independent specification: `Kernels/AmpereTiledSpec` describes row-major f16 A,
  column-major f16 B and row-major f32 C, bounded tiled dimensions, active-buffer
  bounds/alignment/separation, exact-real matrix products, every output byte and
  the global frame. A/B read-only aliasing is permitted; zero K and inactive
  outputs impose no unused-input representation/alignment/separation conditions.
  Canonical launch geometry is explicit. The native extra-CTA overlaunch case
  is not yet covered by this formal specification. Tests check zero-K/inactive
  specification inhabitants, B's column stride, C's row stride and sums spanning
  one and two K tiles. They are specification checks, not kernel correctness.
- Actual source fragments: `Ampere/Updates`, `ScalarSteps`, `CopyStage` and
  `MmaBlock` retain the fixed interpreter's register-bank invalidation, pending
  copy ledger and arbitrary prior query/group/MMA/barrier history. They prove
  relocatable three-copy/commit/wait/barrier and six-packed-load/MMA execution.
  `AmpereTiledStage` instantiates the generated slots 59..72 and composes all
  fourteen instructions, including the post-read reuse barrier. `Guard` and
  `Advance` use actual slots 57/58 and 73..77. `AmpereTiledIteration` composes a
  real 21-slot iteration with 17 events, ten queries, one group and one MMA.
  `AmpereTiledFinish` executes four actual f32 stores and ret. `AmpereTiledMma`
  connects the existing matched full-warp MMA rule to the independent tile-sum
  recurrence, conditional on actual participants' represented input fragments.
  Deriving those representations remains a full-kernel obligation.
- Arbitrary loop count: `AmpereTiledLoop` proves preservation of a PC-57
  invariant and local completion after any remaining t iterations, in 21*t+7
  source steps with 17*t+4 events. Queries advance by ten per iteration. Fixed
  shared/read/output pointers and K survive; global pointers advance modulo
  2^64, including unused final pointers. The unsigned K counter is unwrapped
  using the existing 32-bit bound. Reply premises constrain only copy lengths
  and packed-register tags. They assume no input values or MMA answers. A
  uniqueness theorem gives the same counts for every completed local run under
  these premises. This is a local construction from a reconstructed loop entry;
  neither that entry nor reply-shape premises are added to the kernel `Pre`.
- Tests and limits: parameterized rules are instantiated with nonzero prior
  history, nonzero old accumulators and unrelated registers. Wrapped pointers
  near 2^64 are retained. A separate arbitrary-count instance includes zero
  and three iterations; a purported completion one step early is refuted.
  Its copy bytes and packed words are deliberately not memory-coherent, making
  explicit that local successful completion is not a checked memory witness.
  Numerical specification assertions, local source proofs, generic memory rules
  and complete allowed executions are reported separately.
- Remaining frontier: derive PC-zero initialization/masking and reply tags from
  arbitrary complete source candidates; derive full-warp/CTA participation and
  dynamic barrier source matching; connect actual producer/consumer addresses
  to phase order/races and shared byte values; prove universal tiled output/frame
  correctness and construct an independent complete checked source/rf/co/observer
  witness under the same specification. Hopper, broader atomic/shuffle forms,
  in-flight Iris/runtime/ISA bridges and the unconfirmed exact 81-form inventory
  remain in the original active goal. There is no new performance optimization,
  benchmark/speedup claim or relaxation of exact logits/token requirements.
- Verification gate: `/tmp/ptx-tiled-loop-final.log` exits successfully after
  formatting, 33 Rust tests, Clippy with warnings denied, 20 generated AST
  comparisons, the complete Lean build, 2505 audited declarations, 110 evaluated
  false assertions rejected and assembly of 20 fixtures. This round adds 145
  explicit audit entries; only the existing allowed standard Lean axioms occur.
  Coverage metadata remains 12 capabilities/11 cases, with tiled status partial.
  Native PTX was unchanged this round. The existing 07:46:53 UTC GPU report's
  15 executed fixture hashes and 07:47:15 UTC assembly report's 20 fixture hashes
  were checked against current source. There was no new native execution run.
- Cost snapshot at 2026-11-05 09:14:58 UTC: the goal ledger reports 5,462,121
  tokens versus the preceding published 4,817,420, a difference of 644,701.
  This is an interim ledger snapshot, not final billed usage. The full original
  goal remains active; no required capability or proof/witness criterion was
  removed. No human proof-work time or performance benchmark was measured.

## Round: PC-zero tiled initialization and active copy extents (2026-11-05)

- Instance and previous limit: the preceding arbitrary-count K-loop theorem
  started from a PC-57 invariant. Its initialization, canonical CTA guards and
  source-produced addresses were not derived. Reply length/type assumptions and
  cross-thread memory obligations also remained. This round closes the first
  group while retaining the latter obligations explicitly.
- Actual initialization: `AmpereTiledInit` proves actual parameter loads,
  launch-coordinate reads, truncated tile-base multiplication and both CTA guard
  branches. `AmpereTiledAddresses` checks actual slots 16..51 against explicit
  wrapped address formulas. `AmpereTiledEntry` executes four real zero-literal
  accumulator moves plus counter initialization, composes all 57 active prefix
  slots and derives the existing loop invariant. The new generic float-step
  rule retains actual integer/float/packed bank invalidation. No caller invariant
  or desired read/MMA value is assumed.
- Geometry: `AmpereTiledGeometry` derives u32 tile-base bounds, active guard
  success and per-lane input/output row/column bounds from the existing Layout's
  divisibility/dimension fields and canonical valid thread identities. It
  includes the high A/C row and both output columns. Physical launch/resource
  limits remain outside this mathematical geometry model.
- Complete local source: `AmpereTiledSource` composes PC-zero initialization,
  arbitrary K-loop execution and four stores/ret. Active runs use 64+21*(K/16)
  source slots, 17*(K/16)+4 events and 10*(K/16) queries. Any other completed local
  run under the same reply size/tag certificate has those counts. The certificate
  constrains no desired values but still must be derived from arbitrary complete
  source candidates; it is not added to the independent kernel `Pre`.
- Empty cases without reply premises: for every oracle, active zero K executes
  all 64 source slots and emits exactly four f32 stores of zero, with four events
  and zero queries. Empty M exits in fifteen slots; positive M/empty N exits in
  seventeen, both with no events and zero queries. Unused A/B may be unaligned
  to eight bytes and alias C. The independent specification's vacuous unused-input
  conditions are retained. Full launch memory/observer witnesses remain separate.
- Source/layout connection: `AmpereTiledAddressRules` proves wrapped A/A-high/B/
  C/C-high formulas and exact shared offsets. Every actual copy operation's
  destination at any K step equals the independent cooperative-copy layout;
  the six actual packed read-event addresses equal its A/B fragment functions.
  These equations make the earlier ownership/producer facts applicable to source
  pointers; they establish no memory values or phase ordering by themselves.
- Full copy extents: `AmpereTiledBounds` proves a strided matrix-span inequality
  and derives all eight bytes of every active copy from the existing bounds.
  Pointer wrap is eliminated for actual input accesses using arena<=2^64. The
  unused final advanced pointer and unused zero-K inputs retain their original
  behavior; no padding precondition is introduced. A/B read-only aliasing remains
  permitted. Output/input separation remains the original Layout duty.
- Instances: a nonzero CTA/thread-coordinate three-iteration full source run
  completes in 127 slots with 55 events/30 queries. Exact A/A-high/B/C/C-high and
  shared/read pointers are checked. Its last A-high and B copy each end exactly
  at the corresponding input buffer end. Its reply values deliberately do not
  form a memory-admitted witness. A zero-K A/B/C alias instance accepts every
  oracle and rejects purported completion a slot early. Empty M with near-limit
  u32 dimensions/CTA index and max-u64 unused pointers, and empty N, accept every
  oracle; even an empty copy payload/integer word reply is unused.
- Proof cost: address-block replay required maxRecDepth=4096 for the finite
  thirteen/nine/fourteen-slot symbolic chunks and compiled in 8.6s. Entry, source,
  geometry, address-rule, copy-bound and instance modules each built in roughly
  1--2.2s after dependencies. This is proof-checking evidence, not a kernel
  performance benchmark or research novelty claim.
- Remaining frontier: extract reply size/tags from every complete source candidate
  and reconstruct the complete event/copy/barrier/MMA inventory; derive full-warp/
  CTA participation, dynamic barrier source matching, races and phase ordering;
  force shared values from memory agreement; prove universal matrix output/frame
  correctness and independently construct a complete checked source/rf/co/observer
  witness under the same specification. Native overlaunch is still outside the
  formal canonical-grid case. Hopper, broader atomic/shuffle support, in-flight
  Iris/runtime/ISA bridges and the unconfirmed exact 81-form inventory remain in
  the active original goal. No target, proof/witness criterion or exact logits/
  token requirement is weakened.
- Final gate: `/tmp/ptx-tiled-entry-final.log` exits successfully after formatting,
  33 Rust tests, Clippy with warnings denied, 20 generated AST comparisons, the
  complete Lean build, 2577 audited declarations, 118 evaluated false assertions
  rejected and assembly of 20 fixtures. This round adds 72 explicit audit entries;
  only the existing allowed standard Lean axioms occur. Coverage remains 12
  capabilities/11 cases with tiled status partial. `git diff --check` passes.
- Hardware evidence: PTX/Rust source was unchanged this round. Existing sm_89 GPU
  evidence at 07:46:53 UTC retains 24 exact-byte cases and one completion-only
  case; all 15 executed source hashes match. The 07:47:15 UTC assembly evidence's
  20 fixture hashes also match. These reports were revalidated, not rerun. New
  large masked/hostile-oracle instances are Lean local tests, not GPU runs.
- Cost snapshot at 2026-11-05 09:44:45 UTC: the goal ledger reports 5,583,146
  tokens versus the preceding published 5,462,121, a difference of 121,025.
  This is an interim ledger snapshot, not final billed usage. The original goal
  remains active. No human proof-work time or performance benchmark was measured.

## Round: derive tiled replies and reconstruct arbitrary completed sources (2026-11-05)

- Instance and previous limit: the complete tiled-source constructor still
  accepted a reply length/tag certificate. This could not justify a theorem for
  arbitrary complete source candidates without deriving that certificate from
  actual execution. Exact phase traces and final ledger/counter values also
  needed reconstruction for the subsequent global graph proof.
- Generic inversion: `Ampere/Inversion` derives copy length and actual MMA-input
  success from real successful source slots. It supplies successful-bind/prefix/
  completed-tail rules. `CopyInversion` advances three actual copies, deriving
  all three eight-byte lengths while preserving arbitrary previous history.
  Values remain untouched. No new precondition or allowed-execution restriction
  is introduced.
- Packed tags: `RawLoads` executes all six actual shared word-load slots with
  arbitrary reply variants. Its lookup equations retain integer invalidation of
  old packed data. Actual successful MMA-input extraction forces all four A/two
  B packed lookups to exist, hence each actual loaded reply must be packed.
  This rules out stale packed values surviving a newer integer overwrite.
  It does not reinterpret integer bits as real f16 pairs or infer memory values.
- Arbitrary loops: `AmpereTiledReplies` derives sizes/tags for one actual completed
  loop, replays the twenty-one source slots and recurses over the remaining
  iteration count. Preservation is factored to accept one step's values, with
  the old certificate API retained as a wrapper, avoiding any circular assumption
  about future reply tags. The finite query facts construct a certificate whose
  values come from the actual oracle. `AmpereTiledReconstruct` applies the result
  to arbitrary complete PC-zero runs after the existing initialization prefix.
  Counts, lengths and tags now require no caller certificate or desired value.
- Exact trace: `AmpereTiledTrace` constructs source states, accumulated events
  and final stores for arbitrary K. It proves each actual prefix and the complete
  trace, then uses completed-run uniqueness to equate every actual complete
  active source with one canonical state/event sequence. It also applies to each
  actual trace in a well-formed complete candidate. Copy count=3*t, groups=t,
  MMA count=t, barrier generation=2*t and queries=10*t are derived, where t=K/16.
  Old C is zero initially and the preceding actual matrix oracle answer later.
  No partial-product equality is assumed or yet proved for the whole kernel.
- Phase structure: `AmpereTiledEvents` exposes all seventeen phase events,
  source-derived copy ordinals/groups/source/destination/payloads, MMA PC/ordinal/
  query and C capture. Prefix/event-index rules select every phase slot and the
  final output slots from the complete trace. These provide actual source facts
  for the graph proof; source-PC matching of barrier events and global byte-level
  read/write inventories remain to be established.
- Counterexamples and positive boundary: tests reject all complete fuel counts
  for a seven-byte third-iteration copy, an integer second-iteration B word and
  an integer third-iteration A word. A separate old packed `%rb1` test verifies
  actual invalidation. A positive three-iteration source run accepts integer
  word replies at every matrix-query slot, which reads matrix rather than word
  answers. Canonical copy/group/MMA/barrier counters, the second MMA's old C/PC/
  ordinal/return position and the last reuse barrier return are checked.
  These local values deliberately are not a correct memory/MMA launch witness.
- Reuse and cost: the approach reuses actual-source prefix/uniqueness reasoning
  already used by the asynchronous-copy helper, extending it through arbitrary
  loops and mixed word variants. This is engineering reuse, not a novelty claim.
  New modules built in roughly 1.1--2.4s after dependencies. No performance
  optimization or speedup benchmark is claimed; exact logits/token requirements
  and the independent kernel specification remain unchanged.
- Remaining frontier: complete graph read/write/copy/barrier/MMA inventories,
  actual dynamic barrier source PCs, full-warp/CTA participation, race freedom
  and past/current/future phase ordering, shared-memory values, universal matrix
  output/frame correctness and an independent complete checked source/rf/co/
  observer witness under the same Pre. Native overlaunch remains outside the
  formal canonical grid. Hopper, broader atomic/shuffle forms, in-flight Iris/
  runtime/ISA bridges and the exact unconfirmed 81-form inventory remain in the
  original active goal; no requested criterion is removed.
- Final gate: `/tmp/ptx-tiled-reconstruction-final.log` exits successfully after
  formatting, 33 Rust tests, Clippy with warnings denied, 20 generated AST
  comparisons, the full Lean build, 2656 audited declarations, 123 evaluated
  false assertions rejected and assembly of 20 fixtures. This round adds 79
  explicit audit entries; only the existing allowed standard Lean axioms occur.
  All new public theorems have explicit entries. Coverage remains 12 capabilities/
  11 cases, with tiled status partial, and `git diff --check` passes.
- Native evidence: PTX and Rust frontend source were unchanged. The existing
  07:46:53 UTC GPU report retains 24 exact-byte cases and one completion-only
  case; all 15 executed fixture hashes match current source. The 07:47:15 UTC
  assembly report's 20 fixture hashes also match. These reports were revalidated,
  not rerun. New arbitrary-fuel rejection and matrix-query boundary tests are
  Lean source tests, not GPU executions or complete memory witnesses.
- Cost snapshot at 2026-11-05 10:13:25 UTC: the goal ledger reports 5,688,850
  tokens versus the preceding published 5,583,146, a difference of 105,704.
  This is an interim ledger snapshot, not final billed usage. The original goal
  remains active. No human proof-work time or performance benchmark was measured.

## Round: actual tiled graph inventory and shared phase visibility (2026-11-05)

- Instance and previous limit: arbitrary completed tiled source traces were
  reconstructed, but global read/write/copy inventories and actual phase order
  had not been derived. The generic repeated-write visibility rule therefore
  still lacked an instantiation on the actual tiled kernel.
- Exhaustive source events: `AmpereTiledInventory` covers all seventeen slots
  in every K phase and all four final output slots. It classifies issues, reads,
  writes, MMA returns and pre/post barrier arrivals/returns, and excludes RMWs.
  The argument is parameterized by arbitrary K through canonical reconstruction;
  it is not a finite two/three-iteration enumeration.
- Actual candidate graph: `AmpereTiledGraph` lifts these facts to every actual
  well-formed complete active candidate. All thread byte reads are shared packed
  words; thread writes are final global f32 stores. Independent copyRead and
  copyWrite nodes are included, with source-derived owners/phase ordinals and
  payload projections. Every recorded copy comes from a real source issue.
  `SourceInfo` only bundles existing Layout/launch/provenance/completion facts
  and is derivable from the original Pre; it assumes no access inventory, read
  value, race condition or selected memory witness. No RMW is possible.
- Publication and reuse: `AmpereTiledPhaseOrder` uses actual wait/pre-read barrier
  events to order any current copy write before a peer shared read. The actual
  post-read barrier orders a read before any later-phase copy write; composition
  orders earlier writes before later writes. Issuer and consumer may differ
  within a CTA. Copy accesses remain separate agents outside thread PO. No MMA
  rendezvous is promoted to a memory-publication edge.
- Writer identity: `AmpereTiledSharedWriters` derives every shared byte footprint
  and applies cooperative-copy ownership to prove overlapping writers equal only
  within one K phase. Repeated writes across K phases remain allowed. CTA identity
  and valid thread-z are retained. No global unique-writer precondition is added.
- Conditional value rule on actual PTX: `AmpereTiledPhaseVisibility` exhaustively
  classifies every competing shared writer as current, before current, or after
  the read. The existing generic coherence/no-stale/no-future reasoning derives
  the current rf source and byte value for all admitted rf/co, conditional on read
  eligibility and actual byte accesses. Eligibility still requires the complete
  global race proof. This is not yet the universal matrix correctness theorem.
- Source existence and tests: `AmpereTiledSourceCandidate` constructs full
  enumerated source candidates for arbitrary canonical geometries and supplied
  per-thread replies, proving provenance, distinct/complete thread coverage and
  completion. It does not establish memory/warp/observer legality. The four-CTA,
  three-iteration instance has 128 grid/block slots and tests different producer/
  consumer lanes, actual waits/returns, publication and read-before-reuse paths,
  old/current write order, separate copy agents and absence of RMWs. The selected
  read uses bytes 236..239 inside producer bytes 232..239. Actual read/write byte
  existence is derived with `AmpereTiledAccesses`; the conditional current-source
  test therefore needs no assumed access. Its value oracle deliberately is not
  a memory-admitted witness. New modules built in roughly 1.1--1.8s after deps.
- Reuse and boundary: the generic phase rule previously checked on a small
  repeated-write graph now applies to actual source-produced tiled copy agents.
  This is engineering reuse, with no research novelty or speedup claim. No PTX
  or Rust frontend source changed; exact logits/token requirements remain.
- Remaining frontier: derive global input/output region separation and output
  byte ownership, then prove complete race freedom/eligibility; establish actual
  dynamic barrier source PCs and full-warp/CTA/control admission; force input/
  shared values and prove universal matrix output/frame correctness; construct an
  independent complete checked source/rf/co/observer witness under the same Pre.
  Native overlaunch remains outside the formal canonical grid. Hopper, broader
  atomic/shuffle forms, in-flight Iris/runtime/ISA bridges and the exact unconfirmed
  81-form inventory remain in the original active goal; no criterion is removed.
- Final gate: `/tmp/ptx-tiled-phase-final.log` exits successfully after formatting,
  33 Rust tests, Clippy with warnings denied, 20 generated AST comparisons, the
  full Lean build, 2722 audited declarations, 127 evaluated false assertions
  rejected and assembly of 20 fixtures. This round adds 66 explicit audit entries;
  only the existing allowed standard Lean axioms occur. All new public theorem
  entries were checked. Coverage remains 12 capabilities/11 cases with tiled
  status partial; `git diff --check` passes.
- Native evidence: PTX and Rust frontend source were unchanged. Existing sm_89
  evidence at 07:46:53 UTC retains 24 exact-byte cases and one completion-only
  case; all 15 executed fixture hashes match. The 07:47:15 UTC assembly report's
  20 fixture hashes also match. Reports were revalidated, not rerun. New full-
  source candidate/order tests are Lean evidence, not GPU executions or complete
  memory/warp/observer witnesses.
- Cost snapshot at 2026-11-05 10:46:30 UTC: the goal ledger reports 5,799,382
  tokens versus the preceding published 5,688,850, a difference of 110,532.
  This is an interim ledger snapshot, not final billed usage. The original goal
  remains active. No human proof-work time or performance benchmark was measured.


## Round: tiled global ownership, complete race freedom and input visibility (2026-11-05)

- Instance and prior limit: the actual four-CTA, three-phase tiled source had
  publication/reuse order and a conditional shared visibility rule. That rule
  still required read eligibility; global access separation and the complete
  race argument had not been discharged. This round keeps the original Layout,
  Pre, canonical grid and exact-real matrix specification unchanged.
- Input bounds: `AmpereTiledBounds.copy_region` keeps all eight live-copy bytes
  inside their own A or B buffer. It does not require A and B to be disjoint.
  `AmpereTiledGlobalAccesses` derives all global input regions and all global
  output regions from actual byte accesses, proving that an input read has no
  writer anywhere in the candidate. Input/output separation is used only when
  an actual copy phase exists, so zero-K unused aliases remain admissible.
- Output ownership and coverage: `AmpereTiledOutputLayout` derives all four
  source store bases as independent C element addresses, removes wrapping using
  output bounds, and proves unique byte ownership across every valid CTA/lane/
  slot. Its inverse construction covers each matrix row/column. These are
  parameterized facts; coverage is not limited to the four-CTA test instance.
- Complete race argument: `AmpereTiledRace` classifies every overlapping pair
  involving a write. Global output writes have one owner and cannot overlap
  input reads. Shared writes are ordered across distinct K phases; same-phase
  overlapping writes are identical. Shared read/write pairs use publication
  in the current/earlier phase and post-read protection for later writes. The
  no-RMW inventory rules out treating a writer as a read at the overlap byte.
  Every complete active source candidate is race-free for arbitrary rf, without
  assuming memory admission, a desired value, or a selected witness. Separate
  async agents remain outside issuer PO. Read/observer eligibility follows.
- Input and shared values: `AmpereTiledMemory` forces every memory-admitted
  global read to select initialization, constrains every actual copy payload
  byte to its initial global source byte, and relates a copy write to that
  separate read node. Current-phase shared source/value rules now derive their
  eligibility, and the byte-offset bridge connects shared observations to
  initial input. Actual read/write accesses and the corresponding copy are
  still explicit premises; represented A/B fragment correspondence is next.
- Observed output and frame: `AmpereTiledObservation` proves the global non-C
  frame and observation of a unique actual store. `AmpereTiledOutputAccesses`
  derives every final store event and each output element's observed f32
  accumulator encoding. This is not yet equality with the independent product;
  that requires represented packed inputs and the full-warp MMA induction.
- Tests: the enumerated four-CTA/three-phase source now has race/eligibility
  tests with arbitrary rf, current/future-source tests without an eligibility
  premise, last-row/column/byte and padding checks, output coverage, actual
  global-writer uniqueness and zero-K unaligned unused-input alias checks.
  The deliberately inconsistent source oracle is proved memory-inadmissible
  for every rf/co using its actual first recorded copy byte. It is not used as
  a legal consistency witness. Four additional false arithmetic/store-bound
  claims exercise the upper-half slot, adjacent column and output padding.
- Reuse, cost and limits: this instantiates existing generic race, phase and
  observer rules on an actual tiled source, with no novelty or speedup claim.
  No synchronization was inserted into PTX, and no kernel plan or numerical
  target changed. These are Lean proofs/tests; no GPU performance experiment
  or human proof-work time was measured.
- Remaining frontier: actual dynamic barrier source PCs and full-CTA/warp/control
  admission; represented global A/B to packed-fragment correspondence; MMA
  accumulation equals the independent matrix product; independent complete
  source/rf/co/observer witnesses under the same Pre. Inactive output paths
  must be included in the final universal contract. Native overlaunch remains
  outside the canonical-grid formal case. Hopper, broader atomic/shuffle forms,
  Iris/runtime/ISA bridges and the exact unconfirmed 81-form inventory remain
  in the original active goal. No acceptance criterion is removed.
- Final validation: `/tmp/ptx-tiled-race-final.log` exits successfully after
  formatting, 33 Rust tests, Clippy with warnings denied, 20 generated AST
  comparisons, the full Lean build (3254 jobs), 2773 audited declarations,
  131 evaluated false assertions rejected, and assembly of 20 fixtures. This
  round adds 51 explicit public theorem audit entries; all new/touched public
  theorem entries were checked. Only the existing allowed standard Lean axioms
  occur. Coverage remains 12 capabilities/11 cases, with tiled status partial.
  `git diff --check` passes. The false padding check uses an executable numerical
  bound; rejection must be by refutation, not missing decidability or imports.
- Native evidence: PTX and Rust frontend source were unchanged in this round.
  Revalidation matches all 15 executed fixture SHA-256 hashes in the sm_89
  report (07:46:53 UTC), which contains 24 exact-byte checks and one completion-
  only check. All 20 fixture hashes in the 07:47:15 UTC assembly report match.
  These reports were revalidated, not rerun. New graph/race/value tests are
  formal evidence and do not establish GPU bit-equivalence or performance.
- Cost snapshot at 2026-11-05 11:08:54 UTC: the goal ledger reports 5,958,882
  tokens versus the preceding published 5,799,382, a difference of 159,500.
  This is an interim ledger snapshot, not final billed usage. The original goal
  remains active; no budget, acceptance case or precision requirement changed.


## Round: actual packed inputs and universal tiled matrix correctness (2026-11-05)

- Instance and previous limit: complete tiled source candidates already had
  race freedom, input/copy byte visibility, output ownership/coverage and the
  global frame. Their observed f32 values were actual accumulator encodings,
  not yet proved equal to the independent matrix product. The original Layout,
  Pre, canonical geometry, exact-real model and PTX source remain unchanged.
- Producer correspondence: `AmpereTiledProducer` derives the valid producer
  thread, copy part and four-byte word offset for each of the six packed reads.
  Actual recorded copy source/destination/length metadata is derived from source
  events. For every admitted memory witness, each actual shared byte equals
  its corresponding initial global byte. The caller no longer supplies a
  chosen producer/copy write, read source or value for this rule.
- Represented halves: `Ampere/PackedMemory` derives byte extraction of both
  symbolic f16 halves and extensional equality of pairs. `AmpereTiledInputRead`
  proves matrix-coordinate bounds and identifies each actual read half using
  the original A/B representation premise. A uses row-major indexing; B uses
  column-major indexing. No integer reinterpretation or IEEE encoding is added.
- Source fragment values: `AmpereTiledFragmentInputs` identifies each real half
  with the independent MMA layout, forces all four A/two B packed replies,
  derives actual call lane identities, and classifies actual MMA entries.
  Every actual entry's A/B fields equal the appropriate gathered/packed input
  tiles; old C is the actual previous source accumulator. These are conclusions
  from source, initial representation and memory admission, not new certificates.
- Accumulation: `AmpereTiledAccumulation` establishes the partial-product
  invariant by induction over arbitrary K phases simultaneously for every
  actual thread. The existing mandatory full-warp matched-arithmetic rule uses
  actual entry/return events, same CTA and matching ordinal. It identifies the
  returned matrix step without assuming a desired output oracle. The result
  then agrees with every output store slot's independent row/column.
- Universal contract: `AmpereTiledCorrect.correct` proves CheckedTriple against
  the original Pre and complete output/frame Post for all configurations. Active
  outputs use the phase induction, including zero K. Inactive outputs derive
  empty event lists from arbitrary completed source runs, exclude all recorded
  copies/writes/races and preserve the whole observed arena. No reply, read-source,
  eligibility, fragment-value or output-value premise is added to Pre.
- Tests: a four-CTA, three-K-phase nonuniform symbolic input uses A(r,k)=100r+k
  and B(k,c)=1000k+c. Its entire f16 representation and original Pre are proved,
  not merely assumed for a contract instantiation. The upper last A pair is
  3146/3147 and the last column-major B pair is 46015/47015, at source bases 3196
  and 9724. Tests check different producer lanes and upper-A/B copy parts, and
  instantiate the full universal contract plus zero-K and inactive contracts.
  Four additional executable false claims reject wrong upper-A/B addresses,
  self-copy ownership and use of the B part for an A fragment.
- Reuse and boundary: the existing phase visibility, packed MMA layout and
  matched arithmetic rules now compose into actual tiled matrix correctness.
  This is an engineering/model-relative correctness result, with no research
  novelty or optimization speedup claim. A universal theorem does not establish
  existence of an admitted execution. The nonuniform Pre instance is not an
  independent complete checked source/rf/co/observer witness, and the old
  inconsistent source oracle remains rejected rather than reused as one.
- Remaining frontier: construct independent complete legal source/rf/co/observer
  witnesses for every admissible launch under the same Pre and a concrete such
  instance; this includes actual dynamic barrier source PCs, full CTA/warp
  participation and acyclic control admission. Native overlaunch remains
  outside the canonical-grid formal case. Hopper, broader atomic/shuffle forms,
  Iris/runtime/ISA bridges and the exact unconfirmed 81-form inventory remain
  in the original active goal. No criterion or numerical requirement is removed.
- Final validation: `/tmp/ptx-tiled-product-final.log` exits successfully after
  formatting, 33 Rust tests, Clippy with warnings denied, 20 generated AST
  comparisons, the full Lean build (3261 jobs), 2823 audited declarations,
  135 evaluated false assertions rejected, and assembly of 20 fixtures. This
  round adds 50 public theorem audit entries, including both qualified PackedF16
  declarations. Every new/touched public theorem entry was checked; only the
  existing allowed standard Lean axioms occur. New modules built in roughly
  1.1--2.6 seconds after dependencies. Coverage remains 12 capabilities/11 cases,
  with tiled status partial. `git diff --check` passes.
- Native evidence: PTX/Rust source was unchanged in this round. The existing
  sm_89 report (07:46:53 UTC) retains 24 exact-byte checks and one completion-
  only check; all 15 executed source hashes match. All 20 source hashes in the
  07:47:15 UTC assembly report also match. Reports were revalidated, not rerun.
  The nonuniform represented input is a Lean specification instance, not a new
  GPU execution. No throughput/latency/memory benchmark or human proof-work
  time was measured, and exact logits/token requirements remain unchanged.
- Cost snapshot at 2026-11-05 11:25:45 UTC: the goal ledger reports 6,050,096
  tokens versus the preceding published 5,958,882, a difference of 91,214.
  This is an interim ledger snapshot, not final billed usage. The full original
  goal remains active, with no budget or acceptance criteria changed.


## Round: independent tiled source, control and full-warp MMA components (2026-11-05)

- Instance and prior limit: universal tiled output/frame correctness was proved,
  but an independent complete legal execution witness was still absent. This
  round constructs source/control/MMA components under the original active Pre,
  rather than deriving witness existence from the universal theorem. It does
  not complete memory/observer or dynamic barrier-source admission.
- Actual control: `AmpereTiledInventory.wait_cases` and `AmpereTiledControl`
  classify actual waits and barrier generations. Every complete active candidate
  has full-CTA arrivals at each returned generation; no peer can be excused by
  an exited-before-generation predicate. A rank strictly increases on every
  actual PO, barrier, issue, intra-copy, completion and MMA control edge. The
  resulting ControlAcyclic/BaseAcyclic proof includes separate copy nodes and
  MMA rendezvous. It assumes no memory values or rf/co, adds no execution
  premise, and adds no MMA memory-publication edge.
- Independent source oracle: `AmpereTiledWitnessOracle` takes all eight copy
  bytes from the fixed initial global input, chooses four-A/two-B packed replies
  from gathered matrix tiles, and chooses MMA answers from successive partial
  products. Actual query indices, reply sizes/tags, copy bytes and accumulator
  values are proved. The generic enumerated source constructor then provides
  complete actual traces for all canonical CTAs and K phases under active Pre,
  including zero K. This module does not import the universal correctness module.
- Source PC truthfulness: `Ampere/Origins.step_mma_source` generalizes the old
  return-only inversion to actual entry or return emissions. The existing
  return theorem remains a wrapper. `mma_source_pc` composes actual step
  inversion with source-location instrumentation, proving that a recorded MMA
  call's PC agrees with the actual pre-step PC. This is not a metadata premise.
- Full-warp component: `AmpereTiledWitnessMma` constructs all 32 actual entry/
  return participants in the appropriate CTA/phase, checks their actual source
  PCs and lane/warp/ordinal identities, and proves mandatory packed matrix-step
  arithmetic. Old C comes from the independently chosen previous partial
  product. The proof uses reversible packed layouts and the independent tile
  accumulation identity, not universal tiled correctness. Together with actual
  source completion, full-CTA participation and acyclic control, this closes
  those components of the witness for arbitrary active Pre and K counts.
- Concrete component tests: the represented nonuniform four-CTA/three-phase
  instance has complete actual source, full-CTA barriers, no exit shortcut,
  acyclic control and full-warp MMA predicates. All third-phase lanes are checked;
  actual entry/return serials 47/48 both come from PC 71. Copy part 1 byte 4 is
  the initial upper-A fragment 3146; actual query 26 has pair 3146/3147 and
  query 28 has B pair 46015/47015. The final exact-real scalar answer is proved
  equal to the 48-term product and to 3534768920. Zero-K component tests retain
  unaligned unused A/B/C aliases. Four additional false claims reject copy/wait
  rank reversal, a wrong participant lane, entry/return collapse and PC 72 as
  the MMA source. These are formal source/MMA components, not GPU executions.
- Boundary and reuse: this reuses the existing generic control, source-origin,
  source-enumeration and packed-MMA rules; it makes no novelty or performance
  claim. The old inconsistent source oracle remains rejected for every rf/co.
  A truthful copy oracle and correct full-warp arithmetic do not by themselves
  prove memory legality or final observation. The universal contract and its
  original Pre and exact logits/token requirements are unchanged.
- Remaining frontier: dynamic barrier-site matching at actual PC 64 versus 72;
  independent rf/co/observer admission for this input-determined source;
  completion of CheckedNonvacuous under the same full Pre, including inactive
  launches, and a complete concrete instance. Native overlaunch remains outside
  the canonical-grid formal case. Hopper, broader atomic/shuffle forms,
  Iris/runtime/ISA bridges and the exact unconfirmed 81-form inventory remain
  in the full original active goal. No acceptance criterion is removed.
- Final validation: `/tmp/ptx-tiled-witness-components-final.log` exits
  successfully after formatting, 33 Rust tests, Clippy with warnings denied,
  20 generated AST comparisons, the full Lean build (3265 jobs), 2877 audited
  declarations, 139 evaluated false assertions rejected, and assembly of 20
  fixtures. This round adds 54 public theorem audit entries, including both new
  generic MMA-source rules; the changed return wrapper retains its audit entry.
  Every new/touched public theorem entry was checked, and only the existing
  allowed standard Lean axioms occur. New control/oracle/MMA/component-test
  modules built in roughly 1.2--1.3 seconds after dependencies; the existing
  full-warp probe rebuilt in 91 seconds after the shared Origins change.
  Coverage remains 12 capabilities/11 cases, with tiled status partial.
  `git diff --check` passes.
- Native evidence: PTX/Rust source was unchanged. Revalidation matches all
  15 executed source hashes in the existing sm_89 report (07:46:53 UTC), with
  24 exact-byte checks and one completion-only check. All 20 source hashes in
  the 07:47:15 UTC assembly report match. Reports were revalidated, not rerun.
  The nonuniform component instance uses symbolic reals; it is not a new GPU
  IEEE bit-equivalence result. No optimization throughput/latency/memory
  benchmark or human proof-work time was measured.
- Cost snapshot at 2026-11-05 11:46:24 UTC: the goal ledger reports 6,218,505
  tokens versus the preceding published 6,050,096, a difference of 168,409.
  This is an interim ledger snapshot, not final billed usage. The full original
  goal remains active, with no budget, precision or acceptance criteria changed.


## Round: independent tiled rf/co and final observer admission (2026-11-05)

- Instance and prior limit: the input-determined complete active source family
  had full-CTA participation, acyclic actual control and mandatory full-warp MMA
  arithmetic. Memory rf/co and observer legality had not yet been constructed;
  source completion and truthful-looking replies alone were not sufficient.
  The original Pre, canonical grid, PTX source and exact-real model remain.
- All packed bytes: `AmpereTiledInputRead.initial_half_byte` extends the existing
  first-byte fact to both bytes of both symbolic f16 halves; the old theorem
  remains a wrapper. `AmpereTiledWitnessAccesses` inverts actual constructed
  reads/copies, derives every packed half from independent tile layouts, and
  relates the complete four-byte word to represented initial input. Each shared
  read byte has an actual same-phase producer write with exactly that byte.
  Global copy reads also agree with initialization. These proofs do not assume
  memory consistency and do not invoke universal tiled correctness.
- Explicit rf: `AmpereTiledWitnessMemory.rf` selects initialization for copy
  read nodes, and the actual current-phase producer copy for the six ordinary
  shared reads. All raw read agreement is proved from the constructed payloads
  and the unchanged input representation, with no caller-supplied source/value.
- Complete memory conditions: the existing actual control/base rank and proved
  read-from order give strict causal ranks. Overlapping writer rank injectivity
  follows from actual byte conflict order, without prohibiting repeated writes.
  The actual phase writer classification discharges from-read bounds: equal or
  earlier writes contradict forward coherence, and future writes follow the
  read. Global input reads have no overlapping writer. Together with the
  already-derived race freedom, these facts discharge every generic RankedCo
  memory condition. MemoryConstraints now holds independently for every active
  original Pre, including zero K, without changing eligibility or allowed runs.
- Independent observer: `AmpereTiledWitnessObservation` enumerates every actual
  copy write in every K phase and all final output stores. The coverage proof
  is against actual graph writes, not an expected postcondition. A rank-maximal
  actual-writer selector then gives ObserverConstraints on the full finite
  global arena, including completion, agreement and no-stale observation.
- Components theorem: `AmpereTiledWitnessComponents.components` combines actual
  source/provenance/completion, full-CTA barriers, control acyclicity, mandatory
  MMA, rf/co memory and final observer existence. Its construction does not
  import the universal correctness module. The remaining active checked field
  is SourceAligned for dynamic barrier-source matching; this theorem deliberately
  is not called CheckedNonvacuous. Inactive witness construction also remains.
- Concrete tests: the represented nonuniform four-CTA/three-phase family now
  has unconditional admitted memory and observer instances. Actual shared byte
  236 reads 2322 from current copy 3; old copy 0 is before current, which is before
  future copy 6. Reverse coherence and future read sources are rejected. After
  constructing admission, the independent output/frame theorem derives final
  observed f32 value 3534768920 and preserved output padding. Zero-K memory and
  observer instances retain unused A/B/C aliases and unaligned unused inputs.
  Four executable false claims reject initialization/future sources for a live
  shared read, a copy-writer source for a global input read, and reversed future
  write/read rank. These tests do not assert full checked barrier admission.
- Reuse and boundary: generic ranked coherence and rank-maximal observation
  rules now apply to the actual repeated-write tiled graph. This is engineering
  reuse with no novelty or speedup claim. No PTX synchronization was inserted,
  no desired matrix result was supplied as a precondition, and no numerical
  goal was weakened. Tests and formal model witnesses remain separate from GPU
  IEEE/runtime/compiler correspondence and performance measurements.
- Remaining frontier: actual dynamic matching of barrier source sites PC 64/72;
  inactive source/witness construction; then complete CheckedNonvacuous under
  the same full Pre and its concrete instance. Native overlaunch remains outside
  the formal canonical grid. Hopper, broader atomic/shuffle forms, Iris/runtime/
  ISA bridges and the exact unconfirmed 81-form inventory remain in the full
  original active goal. No acceptance criterion is removed.
- Final validation: `/tmp/ptx-tiled-rf-co-observer-final.log` exits successfully
  after formatting, 33 Rust tests, Clippy with warnings denied, 20 generated AST
  comparisons, the full Lean build (3270 jobs), 2915 audited declarations,
  143 evaluated false assertions rejected, and assembly of 20 fixtures. This
  round adds 38 public theorem audit entries, including the generalized
  packed-half byte rule; the first-byte wrapper retains its audit entry.
  Every new/touched public theorem entry was checked, and only the existing
  allowed standard Lean axioms occur. New modules/tests built in roughly
  1.1--1.5 seconds after dependencies. Coverage remains 12 capabilities/11 cases,
  with tiled status partial. `git diff --check` passes.
- Native evidence: PTX/Rust source was unchanged in this round. All 15 executed
  fixture hashes match the existing sm_89 report (07:46:53 UTC), containing
  24 exact-byte checks and one completion-only check. All 20 fixture hashes in
  the 07:47:15 UTC assembly report match. Reports were revalidated, not rerun.
  The new observer/output checks are symbolic-real Lean evidence, not new GPU
  executions or IEEE bit-equivalence claims. No throughput/latency/memory
  benchmark or human proof-work time was measured.
- Cost snapshot at 2026-11-05 12:07:13 UTC: the goal ledger reports 6,300,851
  tokens versus the preceding published 6,218,505, a difference of 82,346.
  This is an interim ledger snapshot, not final billed usage. The full original
  goal remains active; no budget, precision or acceptance criteria changed.


## Round: actual dynamic barrier PCs and full tiled checked nonvacuity (2026-11-05)

- Instance and prior limit: the actual tiled source had universal checked
  matrix/frame correctness and independent active source/control/MMA/memory/
  observer components. The two repeated barrier sites used the same barrier
  resource at actual PC 64 and 72, so a unique-static-site shortcut could not
  close SourceAligned. Inactive full checked witnesses were also missing.
  This was a proof-composition gap, not an optimization or a new method claim.
- Reusable source boundary: `SourceRun.run_add` composes instrumented execution;
  `SourceRun.at_boundary` derives an emitted event's annotation from an actual
  plain execution prefix and its next interpreter step. The PC is the actual
  emitting pre-state's PC. `Ampere.source_pc_of_prefix` lifts this rule into any
  well-formed candidate trace. Neither rule accepts a desired PC as a premise.
- Actual stage prefixes: the existing cooperative-copy and tiled-stage execution
  proofs now expose five-step pre-barrier and thirteen-step post-MMA prefixes.
  The original six-step and fourteen-step execution theorems remain wrappers
  with their original interfaces. This reuses their actual source execution
  proofs, rather than replaying the whole instrumented trace for each event.
- Dynamic matching: `AmpereTiledBarrierSources` reaches the actual pre-barrier
  state after 64+21*p+8*h slots, where h is 0 or 1. Its event serial is
  17*p+5+10*h, its PC is 64+8*h, and its generation is 2*p+h. Both arrival and
  return inherit this actual PC. Equal matched generations force the same h;
  SourceAligned therefore holds for arbitrary active complete source candidates,
  regardless of oracle values, without requiring a unique static barrier site.
- Inactive family: `AmpereTiledWitnessInactive` independently enumerates every
  canonical launched thread and follows the actual M=0 or N=0 guard/return path
  in 15 or 17 slots. Traces have no events/copies. InitialCo, empty rf and an
  initialization-selected full-domain observer satisfy every checked condition
  and complete observation. Unused inputs require no new alignment, value or
  separation premise. The module does not import universal tiled correctness.
- Full original Pre: `AmpereTiledNonvacuous.nonvacuous` combines the existing
  independent active input-determined source/rf/co/full-warp/observer witnesses
  with actual dynamic source matching and the inactive branch. CheckedNonvacuous
  now holds under exactly the same Pre as `AmpereTiledCorrect.correct`, including
  zero K and inactive output dimensions. The construction does not invoke the
  universal correctness theorem. No sync, oracle restriction or desired output
  value was added to the precondition or allowed-execution predicates.
- Complete concrete tests: the nonuniform four-CTA/three-phase source now has
  unconditional CheckedConditions, complete observer/domain admission and a Post
  obtained from the independent universal contract. Existing observed result
  3534768920 and padding preservation remain. All phase/half/arrival-return source
  PCs are checked; third-phase event serials 39/40 have PC 64, and 49/50 have
  PC 72. Actual cross-site and same-site/wrong-generation BarrierSync edges are
  proved impossible. Zero-K complete checked admission retains unused aliases.
  Both empty-M and empty-N launches have complete checked/observer/Post tests,
  with unaligned unused pointers/aliases, no events and actual 15/17-slot counts.
- Acceptance and boundary: universal correctness, independent complete legal
  execution existence under the same full Pre, and a concrete complete instance
  now meet the three formal tiled-case criteria relative to the current model.
  Inventory status remains partial for broader PTX/ISA/runtime/IEEE correspondence;
  no full PTX compliance or numerical/performance claim is made. Native extra-CTA
  overlaunch remains outside the canonical formal geometry. Hopper, broader
  atomic/shuffle forms, Iris/runtime/event bridges and exact verification of the
  unconfirmed 81-form inventory remain in the original active goal. The exact
  logits/token requirement is unchanged.
- Next implementation frontier: start Hopper with fixed source forms and actual
  event provenance for TMA descriptors, mbarrier phases and WGMMA groups before
  proving single-stage and then two-stage GEMM. Preserve independent operation
  identities and distinguish generic/async/tensormap proxies. In particular, do
  not reuse Ampere wait publication as a blanket TMA release: the implicit TMA
  complete-tx orders only its own transfer operations, not all earlier issuer
  instructions ([PTX ISA 9.4, asynchronous memory operations](https://docs.nvidia.com/cuda/archive/13.4.2/parallel-thread-execution/index.html)).
  A phase model must also retain a successful test/try-wait before the next
  phase's arrival, rather than treating phase parity alone as a complete
  protocol ([mbarrier phases](https://docs.nvidia.com/cuda/archive/13.4.2/parallel-thread-execution/index.html)).
  These are pending implementation/bridge duties, not newly claimed proofs.
- Final validation: `/tmp/ptx-tiled-full-checked-final.log` exits successfully
  after formatting, 33 Rust tests, Clippy with warnings denied, 20 generated AST
  comparisons, the full Lean build (3275 jobs), 2964 audited declarations,
  143 evaluated false assertions rejected, and assembly of 20 fixtures. This
  round adds 49 public theorem audit entries, including the generic source
  boundary rules and the two actual forbidden barrier-edge proofs. All public
  theorem entries in new/touched proof modules were checked. Only the existing
  allowed standard Lean axioms occur. The nonvacuity module's local import
  closure has 111 Ptx modules, with no universal tiled correctness or test import.
  Coverage remains 12 capabilities/11 cases; broader correspondence status is
  partial while the three model-relative tiled case criteria are now closed.
- Native evidence: all 15 executed fixture hashes match the existing sm_89
  report (07:46:53 UTC), with 24 exact-byte comparisons and one completion-only
  check. All 20 fixture hashes in the 07:47:15 UTC assembly report match. The
  reports were revalidated, not rerun; the final gate additionally assembled all
  20 current fixtures. No PTX/Rust source changed. Symbolic-real checked witnesses
  are not new GPU IEEE executions. No optimization throughput/latency/memory
  benchmark or human proof-work time was measured. `git diff --check` passes.
- Cost snapshot at 2026-11-05 12:33:33 UTC: the goal ledger reports 6,480,303
  tokens versus the preceding published 6,300,851, a difference of 179,452.
  This is an interim ledger snapshot, not final billed usage. The full original
  goal remains active, with no budget, precision or acceptance criteria changed.


## Round: typed Hopper mbarrier source and signed phase protocol (2026-11-05)

- Instance and prior limit: after closing the three model-relative Ampere tiled
  criteria, the frontend still accepted no Hopper target or mbarrier operations.
  Ampere's own-copy wait/publication rules do not describe TMA transaction counts,
  mixed proxies or asynchronous WGMMA registers. This round establishes the first
  source/protocol layer; it does not substitute a notification helper for GEMM.
- Primary reference: the fixed forms and layout-v0 protocol follow the archived
  [PTX ISA 9.4 mbarrier specification](https://docs.nvidia.com/cuda/archive/13.4.2/parallel-thread-execution/index.html),
  while the new source fixtures deliberately use PTX 8.0/sm_90a forms accepted by
  the installed ptxas. Layout-v1/report operands and newer phase-type qualifiers
  remain outside this subset. Transaction counts are signed, and transaction
  completion is distinct from pending thread arrivals.
- Typed frontend: five fixed CTA-local forms retain all selected qualifiers:
  init, inval, release arrive.expect_tx with a sink result, relaxed complete_tx,
  and acquiring try_wait.parity. Address/count/predicate types and u32 literal
  bounds are checked; unsupported destination tokens, cluster/relaxed variants,
  layout-v1, optional wait hints and predication fail closed. The lexer keeps
  `::` qualifiers intact while labels retain the correct instruction boundaries.
  PTX 8.0 and sm_90a are explicitly paired; both the accelerated target and
  numeric SM are retained in generated checked program data. Earlier PTX 7.0
  sm_70/sm_80 output formats remain subject to exact generated-file comparison.
- Source interpreter: `Hopper/Thread` embeds the prior Ampere backend at identical
  PC slots. It emits mbarrier operations with actual computed resource addresses
  and 32-bit operands. A wait records an unconstrained oracle bit and writes the
  actual predicate, consuming exactly one common query index. No thread-local
  heap or phase counter stands in for shared barrier state. Parameterized local
  rules cover all five forms. Instrumented source PCs erase exactly to this same
  execution; they are not oracle metadata.
- Independent protocol: `Hopper/Mbarrier` checks one ordered resource history.
  It retains expected/pending arrivals, signed tx count, phase and successful-wait
  observation. Phase completion requires pending=0 and tx=0; completion resets
  pending arrivals and disables subsequent arrival until a successful wait.
  Counter ranges are preserved by every admitted step/history. Successful waits
  check the preceding phase parity. Failed waits leave state unchanged and are
  deliberately allowed even after completion, a stated overapproximation rather
  than an added progress assumption. Count units remain opaque until TMA matching.
- Reusable rules: generic finish/step/run invariants and completed-wait inversion
  separate count safety, phase completion and reuse. `phase_cycle` and
  `two_phase_cycles` hold for arbitrary natural phases and positive transaction
  counts within the layout-v0 bound. Append rules compose histories and project
  resource events. These are engineering foundations, with no novelty or speedup
  claim; they do not establish memory visibility.
- Actual tests: a 12-instruction generated fixture completes two reused phases,
  with eight real mbarrier events at PCs 1/2/3/4/6/7/8/10 and two wait queries.
  A timeout followed by retry has an admitted 14-slot/three-query execution.
  Resource projection distinguishes equal addresses in different CTAs and
  different addresses within a CTA. The four-instruction missing-completion
  fixture returns locally under a lying successful oracle but fails the resource
  protocol. Explicit tests also preserve legal completion-before-expect with
  tx=-16; reject missing arrivals, reuse before successful wait, stale/wrong
  parity, duplicate/uninitialized objects, zero/overflowed arrival counts and
  positive/negative tx overflow. Invalidation/reinitialization is a protocol
  lifecycle test, not a proof that in-flight TMA memory may be reclaimed.
- Regression gate: four new Rust end-to-end tests cover fixture control/target,
  register typing, strict qualifier/operand rejection and version/target pairing.
  Eight additional evaluated false assertions exercise missing tx/arrival
  completion, premature/false-wait reuse, stale parity, unsigned saturation,
  duplicate initialization and count overflow. Assembly now reads each fixture's
  actual target, includes sm_90a and refreshes the source-hashed JSON report only
  after every assembly succeeds; no assembly result is called GPU execution.
- Boundary and next work: this is not a global Hopper allowed-execution predicate
  or a full legal kernel witness. Multi-thread resource matching against actual
  program order, resource allocation/opaque-object UB, implicit notifications tied
  to actual TMA operations, descriptor layouts and transferred bytes, directional
  proxy visibility, WGMMA full-warpgroup arithmetic plus async register/fence/group
  protocols, and single-stage then double-buffered GEMM remain required. Explicit
  relaxed complete_tx does not transfer data or release all earlier issuer writes.
  The capability moves from planned to partial; the required Hopper GEMM case
  remains planned. Exact 81-form parity is still unconfirmed, and all remaining
  original goal requirements and exact logits/token requirements are retained.
- Counter-range review: the signed layout-v0 limit constrains the resulting
  transaction state, while explicit expect/complete operands are u32. The protocol
  retains 32-bit updates larger than the positive state limit when a negative
  starting count makes the result legal. Two concrete tests cross from -limit
  to +limit and back without incorrectly imposing a per-update 20-bit cap.
  This avoids an unjustified restriction on candidate histories; it does not
  relax the invariant or change the exact numerical goal.
- Rejection-harness cost and integrity: negative assertions now share one import
  pass while remaining separate Lean commands. JSON diagnostics must identify
  exactly one evaluated-false `decide` result at each assertion's own source line;
  missing, unrelated, duplicate, parse/type/import errors and abnormal process
  results fail the gate. Six integration self-tests distinguish true assertions,
  mixed true/false batches, batches beyond the default 100-error limit, and
  syntax/elaboration failures from real refutations.
  This changes checker startup overhead, not Lean's proof kernel or the admitted
  model. The original sequential gate passed all 151 false claims before this
  batching change; the revised current source is checked again below.
- Final validation: `/tmp/ptx-hopper-mbarrier-batch-final.log` exits successfully
  after formatting, 37 Rust tests, Clippy with warnings denied, six negative-
  harness integration self-tests, 22 generated AST comparisons, the full Lean
  build (3281 jobs), 3029 audited declarations, 151 separately evaluated false
  assertions, and assembly of 22 fixtures. This round adds 65 public theorem
  audit entries; every new public theorem entry was checked, and only the
  existing allowed standard Lean axioms occur. The final gate includes the
  reviewed 32-bit counter deltas and both larger-delta positive cases. Coverage
  remains 12 capabilities/11 cases; Hopper infrastructure is partial and its
  required GEMM acceptance case is still planned. `git diff --check` passes.
- Native evidence: the current final gate refreshes the assembly report at
  13:00:19 UTC with all 22 source hashes and actual sm_70/sm_80/sm_90a targets,
  including both new Hopper notification helpers. It is assembly-only evidence.
  All 15 source hashes in the existing sm_89 execution report (07:46:53 UTC)
  still match; its 24 exact-byte comparisons and one completion-only check were
  revalidated, not rerun. No Hopper GPU execution, universal IEEE or optimization
  throughput/latency/memory claim is made; human proof-work time was not measured.
- Cost snapshot at 2026-11-05 13:00:45 UTC: the goal ledger reports 6,597,913
  tokens versus the preceding published 6,480,303, a difference of 117,610.
  This is an interim ledger snapshot, not final billed usage. The full original
  goal remains active; no budget, precision or acceptance criterion changed.


## Round: actual Hopper multi-thread resource matching and control cycles (2026-11-05)

- Instance and prior limit: the five mbarrier source forms and signed local
  phase protocol existed, but an unrelated list of protocol operations was not
  evidence about every thread of a real launch. Different resources could also
  pass local checks while mutually depending on future signals. This round is
  baseline proof infrastructure, not a measured optimization or novelty claim.
- Actual launch source: `Hopper/Source` requires valid geometry, unique launched
  thread identities, complete thread coverage and actual interpreter provenance.
  Completion is separate. Generic lookup and `source_event` rules recover the
  actual emitting step and pre-state PC through the existing instrumentation;
  neither PC nor event kind is supplied as trusted oracle metadata.
- Exhaustive finite inventory: `Hopper/Inventory` enumerates candidate event
  identities and actual mbarrier records. Its inventory-membership equivalence
  connects every proposed operation back to the actual candidate lookup. Resource
  locations retain CTA identity, so equal shared offsets in different CTAs do
  not collapse into one object. The inventory does not infer any read value.
- Source-matched histories: `Hopper.HistoryValid` requires unique event
  identities, an exact permutation of the full actual resource inventory,
  preserved issuer order and a successful protocol run. Generic rules establish
  soundness, completeness and common resource/operation identity for an event;
  missing, duplicate and fictitious entries cannot be hidden by balancing counts.
  Resource orders are local to the object, not a serialization of ordinary memory.
- Derived phases: protocol prefix/step decomposition and the existing invariant
  show that every successful actual wait has a real well-formed pre-state with
  a completed preceding parity. Every actual arrival has its real prefix phase,
  an observed previous completion and positive pending arrivals. These are
  derived from source-matched histories, without caller-supplied phase metadata.
- Control component: `ResourceControl` combines source program order, actual
  CTA arrival/return tags and resource-history order. A finite rank certificate
  proves absence of cycles in these control relations. Resource order itself
  does not publish data or serve as a proxy fence. `ResourceConditions` records
  actual source/completion, all resource histories and control only; it is not
  the full Hopper checked memory/construct/observer predicate.
- Complete positive source/component witness: the new 15-instruction generated
  `hopper_mbarrier_peers.ptx` has two threads per CTA in a two-CTA grid. Each CTA's
  leader initializes, arrives, notifies completion and eventually invalidates
  its object; its peer successfully waits before invalidation. All four actual
  source traces complete (leader 15 slots, peer 11), and every launched thread
  is covered. Exact histories, phase prefix facts and an acyclic control rank
  are checked. Wait PC 9 and both collective sites PC 5/11 are actual instrumented
  source facts. The two shared offset-zero resources remain distinct.
- Circular source counterexample: the new 18-instruction
  `hopper_mbarrier_cycle.ptx` initializes two different resources, synchronizes
  initialization, then each thread waits for the other resource before signaling
  its own. Successful oracle bits permit both local source traces to return;
  each resource separately admits a source-matched ordered protocol history.
  Exhaustive kernel-checked finite permutations prove the unique possible
  protocol order for each resource. Every matching family then has a four-edge
  source/resource control cycle, so no ResourceConditions witness exists for
  this actual candidate for any choice of histories. This is a model-relative
  construct rejection, not a GPU deadlock/termination theorem; it is never run
  on GPU. It does not rely on adding data-memory causality or changing rf/co.
- Other negative evidence: dropping a peer wait breaks exact coverage; duplicate
  event identities, reversed issuer order, cross-CTA notification reuse and
  invalidation before the peer wait are rejected. A fictitious complete_tx can
  make a standalone local protocol pass, but its event 99 is absent from the
  actual source and the inventory rejects it. Seven additional evaluated false
  assertions exercise these source/resource/control errors. A new Rust test
  checks both fixtures' true branch/loop PCs and target retention.
- Reuse and remaining boundary: this reuses source instrumentation, the existing
  strict path/rank rule and signed protocol invariants. No synchronization was
  inserted into an optimized kernel to obtain a performance claim, and no
  numerical or caller precondition was weakened. Implicit TMA completion must
  next obtain its own operation identity and actual byte-count correspondence;
  it cannot be invented as an explicit source complete_tx. TMA descriptors,
  transferred bytes and directional proxy visibility, complete CTA/async and
  opaque-object allocation/UB admission, WGMMA register/group arithmetic and
  single-stage then double-buffered GEMM remain open. Hopper capability stays
  partial and its required GEMM case stays planned. Broader atomics/shuffle,
  Iris/runtime/ISA bridges and unconfirmed exact 81-form parity remain in the
  full original active goal, with exact logits/token requirements unchanged.
- Final validation: `/tmp/ptx-hopper-source-resources-final.log` exits successfully
  after formatting, 38 Rust tests, Clippy with warnings denied, six rejection-
  harness integration self-tests, 24 generated AST comparisons, the full Lean
  build (3289 jobs), 3098 audited declarations, 158 independently evaluated
  false assertions, and assembly of all 24 fixtures. This round adds 69 public
  theorem audit entries; every new entry was checked, with only the existing
  allowed standard Lean axioms. All permutation and finite rank checks use Lean
  kernel reduction, without native-decide trust. Metadata still records
  12 capabilities/11 cases. `git diff --check` passes.
- Native evidence: the fresh assembly report (13:20:58 UTC) records all 24
  fixture hashes and actual targets, including four sm_90a mbarrier helpers.
  This is syntax/target evidence only. All 15 hashes in the existing sm_89 GPU
  report (07:46:53 UTC) still match; its 24 exact-byte comparisons and one
  completion-only check were revalidated, not rerun. No Hopper GPU execution,
  universal IEEE or optimization throughput/latency/memory result is claimed;
  human proof-work time was not measured.
- Cost snapshot at 2026-11-05 13:23:27 UTC: the goal ledger reports 6,682,496
  tokens versus the preceding published 6,597,913, a difference of 84,583.
  This is an interim ledger snapshot, not final billed usage. The full original
  goal remains active; no budget, precision or acceptance criterion changed.


## Round: actual 2-D TMA issue, byte graph and implicit completion (2026-11-05)

- Instance and prior limit: multi-thread mbarrier histories and control existed,
  but they could not manufacture a TMA notification as an ordinary source event.
  A real transfer needed its own identity, descriptor/coordinate interpretation,
  byte footprint and notification count. This round builds those engineering
  components and preserves all preceding source/resource regressions. It is not
  an optimization or new-method/performance claim.
- Fixed source forms: the strict frontend accepts the PTX 8.0/sm_90a 2-D
  cluster-destination/global-source tensor-copy form with mbarrier byte completion,
  and the CTA async proxy fence. All qualifiers/operands and actual branch PCs
  are retained; multicast, alternative dimensions/state spaces, im2col, optional
  cache operands and malformed vectors fail closed. `.s32` declarations retain
  their 32-bit representation throughout generated typing data. Ordinary accepted
  word instructions keep their opcode-defined unsigned/bit semantics; TMA
  coordinate operands have exact signed-32 interpretation. Negative literals,
  including -2^31, are serialized by their exact word pattern. There is no new
  signed-arithmetic or float-bit-reinterpretation implementation.
- Mathematical descriptor profile: `TmaDescriptor` models an unswizzled,
  non-interleaved, unit-stride 2-D tile with whole-byte elements and default byte-
  zero fill. It proves signed coordinate range, per-byte source footprint,
  zero-fill and global span properties. Dimension/row-stride/box/element-size
  fields are independent of source replies and copied payload values. A decoded
  mathematical view is not a verified opaque CUDA tensor-map encoder/decoder;
  its encoding, storage-space, runtime and full profile/UB correspondence remain
  an explicit bridge. Raw zero-fill rules do not prove f16/IEEE bit reinterpretation.
- Real source queries: the interpreter emits an issue record and no synchronous
  heap update. It consumes the actual descriptor query q and payload query q+1,
  checks complete payload length and advances to q+2. `TmaSource` inverts any
  successful actual issue to its opcode, descriptor, payload, query base and
  mandatory length. The existing actual-step/source-PC machinery applies to
  these new events. Issue-event identity itself identifies the transfer; no
  unrelated copy table or oracle-supplied logical identity is trusted.
- Independent graph: `TmaGraph` derives descriptor, per-byte read/write and
  notification nodes from actual source issues. All implicit nodes have a
  transfer agent distinct from the issuer. Descriptor access is tensormap-proxy,
  data accesses async-proxy and notification generic-proxy. Out-of-bounds source
  bytes have no read node; destination bytes remain in the tile footprint.
  Raw shared-cluster addresses use an explicit resolver; they are not silently
  assumed to be issuer-local. This is a TMA access fragment, not an adapter that
  silently omits ordinary/non-bulk accesses from a full memory proof.
- Derived notifications: `TmaResources` uses disjoint source-operation and
  implicit-notification origins. The notification target and count derive from
  the actual transfer. Actual source length relates the count to the complete
  payload length. Exact inventory permutation, unique origins and source order
  prevent invented, omitted or duplicate completion. The old signed-phase rules
  derive waits' real prefix states. `TmaControl` includes per-byte data dependencies,
  all writes before notification, source/CTA order and matched resource order.
  Its arbitrary-node rank rule proves acyclic control without claiming memory
  publication across proxies.
- Complete positive components: the generated 13-instruction
  `hopper_tma_copy.ptx` has an actual complete single-thread source with three
  queries, actual issue PC 8 and a 32-byte, two-row padded input view. Global
  source byte 0 is address 196 and byte 16 is address 260; the destination spans
  shared 16..47. Descriptor and all payload bytes agree with independent fixed
  inputs, the implicit notification is exactly 32 bytes, its resource history
  reaches the real completed phase, and combined source/data/resource control
  has an acyclic rank. These are checked components, not CheckedNonvacuous or
  an all-candidate functional copy/GEMM contract.
- Wrong-source evidence: a 31-byte reply faults in the source interpreter.
  Duplicate implicit notifications can pass the counter protocol alone but fail
  unique identity/inventory admission. Incorrect zero payload can complete
  locally and pass resource counts, yet fails independent byte agreement. A
  source expecting 32 bytes with a descriptor/transfer notifying 16 still returns
  under a lying oracle; exhaustive kernel reduction of all resource permutations
  proves no matching history can admit it. Negative coordinate/OOB tests retain
  exact word interpretation and raw byte-zero fill.
- Regression and boundaries: three new Rust tests exercise target/operand/type
  retention, negative-coordinate boundaries and strict rejection. Eight additional
  false assertions cover striding, proxies, operation agents, signed coordinates,
  byte counts, duplicate notifications, short replies and missing implicit
  completion. The next required bridge is descriptor storage/initialization and
  combined weak-memory/proxy/rf/co/race/observer admission that derives descriptor
  and payload agreement for arbitrary admitted candidates. Complete CTA/async/
  allocation/UB checks, WGMMA register/fence/group arithmetic, single-stage and
  double-buffered GEMM remain open. No agreement was added as a caller premise
  to the existing kernel correctness theorems. The original exact logits/token
  requirement, Iris/runtime bridges, broader atomics/shuffle and unconfirmed
  exact 81-form inventory remain in the full active goal.
- Final validation: `/tmp/ptx-tma-source-graph-resources-final.log` exits
  successfully after formatting, 41 Rust tests, Clippy with warnings denied,
  six rejection-harness integration self-tests, 25 generated AST comparisons,
  the full Lean build (3296 jobs), 3173 audited declarations, 166 independently
  evaluated false assertions and assembly of all 25 fixtures. This round adds
  75 public theorem audit entries. All 111 public theorem entries in new/touched
  proof modules were checked, including the existing register-bit/type rules
  generalized to s32. Only the existing allowed standard Lean axioms occur.
  No native-decide trust is used for the 120 resource-order checks. Coverage
  still records 12 capabilities/11 cases; Hopper remains partial and the GEMM
  case remains planned. `git diff --check` passes.
- Native evidence: the assembly report refreshed at 14:07:37 UTC contains all
  25 source hashes and actual sm_70/sm_80/sm_90a targets, including the new TMA
  fixture. This establishes syntax/target acceptance only. All 15 source hashes
  in the existing sm_89 GPU report (07:46:53 UTC) still match; its 24 exact-byte
  comparisons and one completion-only check were revalidated, not rerun. No new
  Hopper GPU execution, universal IEEE or optimization throughput/latency/memory
  claim is made; human proof-work time was not measured.
- Cost snapshot at 2026-11-05 14:11:37 UTC: the goal ledger reports 6,815,654
  tokens versus the preceding published 6,682,496, a difference of 133,158.
  This is an interim ledger snapshot, not final billed usage. The full original
  goal remains active; no budget, precision or acceptance criterion changed.


## Round: combined Hopper access inventory and immutable input values (2026-11-05)

- Instance and prior limit: TMA source/resource/control components existed, but
  the constructed descriptor/payload agreement propositions did not follow
  from any shared memory-read component. Checking only TMA writers would also
  silently omit overlapping ordinary, RMW or non-bulk writes. This round adds
  reusable engineering rules and adversarial regressions; it makes no new
  optimization, novelty, speedup or hardware-execution claim.
- Shared representation: the pure tensor-map view moves to `ISA/TensorMapView`;
  `Hopper.Tma.Descriptor2D` preserves its existing name through an alias.
  `Symbolic.Byte.tensorMapPart` and `ISA/TensorMapStorage` represent an opaque
  object by 128 typed indexed parts. Stored-object uniqueness and access width
  are checked. These are abstract storage tags, not a bit-level CUDA encoding,
  numeric reinterpretation or host encoder/decoder correspondence.
- Combined inventory: `Hopper/AccessGraph` preserves actual ordinary/RMW source
  kinds and source-issued non-bulk copies alongside TMA descriptor, byte read,
  byte write and notification nodes. Non-bulk identities are actual source issue
  events. Every legal TMA payload offset has a destination kind, using the
  source-derived mandatory length. OOB inputs have no read kind. Generic
  descriptor-address resolution and cluster shared-address resolution are
  explicit. The inventory introduces no full memory consistency predicate,
  cross-proxy ordering, moral-strength rule or assumed physical address map.
- Reusable value rules: `InputValues` indexes initial memory by proxy. Its read
  agreement is an explicitly gated value fragment and accepts an explicit
  eligibility predicate. The generic immutable-read rule quantifies over all
  source/RMW/non-bulk/TMA writers. `descriptor_agreement_from_memory` recovers
  each oracle descriptor from independently stored expected objects, eligible
  descriptor reads and 128-byte all-writer immutability.
  `payload_agreement_from_memory` uses actual source provenance/length, eligible
  in-bounds async reads and all-writer immutability to derive every input byte.
  OOB writes require the explicit primitive `ZeroFill` legality condition:
  reads-from agreement alone cannot constrain a byte with no read.
- Concrete independent fragment: `Tests/TmaInputValues` constructs separate
  initial proxy views, an initial reads-from witness, stored descriptor, actual
  input-site classification, read agreement and global immutability. Both rules
  then recover the existing padded tile's descriptor/input agreement. Its input
  sites are a fragment witness, not a derived full PTX race/eligibility theorem.
  Malformed candidates used only for inventory checks are labeled as such.
- Counterexamples: ordinary store, both sides of an RMW and a non-bulk shared
  copy remain visible in the combined graph and refute immutability where they
  write. Equal-sized descriptor substitution and wrong payloads return in the
  actual source interpreter but fail the read fragment. An actual negative-x
  TMA source step has an OOB destination write and no corresponding source read;
  correct zero fill satisfies the primitive rule, while an equally long nonzero
  fill returns locally and is rejected. Separate generic and tensormap views
  prevent an implicit kernel-start publication assumption.
- Primary specification: [NVIDIA PTX ISA 8.5](https://docs.nvidia.com/cuda/archive/12.6.3/parallel-thread-execution/index.html#data-movement-and-conversion-instructions-cp-async-bulk-tensor)
  identifies tensormap-proxy descriptor access, generic descriptor pointers and
  signed coordinates. The same specification's tensor-map copy/fence operation
  uses a 128-byte object. These references motivate the mathematical components;
  no new binary/runtime correspondence is claimed.
- Remaining: combine proxy-aware ordering, rf/co, races and observers, derive
  eligibility and async-to-generic visibility, connect proxy initial views and
  typed descriptor storage to actual CUDA encoding/runtime, finish construct,
  allocation/UB checks, then WGMMA and single/double-buffer GEMM universal
  correctness plus independent full-Pre completed witnesses and concrete cases.
  Current input-fragment evidence does not close any required kernel case or
  lower any original goal or exact-output acceptance criterion.

- Validation: complete `scripts/check.sh` passes: 41 Rust tests, Clippy with
  warnings denied, six rejection-harness integration tests, 25 generated AST
  comparisons, the full 3301-job Lean build, 3223 audited declarations, 174
  individually evaluated false assertions and 25 PTX assembly fixtures. The
  50 new public theorems are included in the audit. Opaque 128-byte evaluation
  exceeded the default recursion depth in the first rejection run; the harness
  rejected that run instead of counting it as a refutation. The final run uses
  an explicit 50000 recursion limit and retains exact per-assertion false-proof
  diagnostic checks. Assembly evidence refreshed at 14:37:15 UTC.
- GPU evidence is unchanged from 07:46:53 UTC: all 15 fixture hashes still match,
  with 24 exact-byte cases and one completion-only case. No new GPU execution or
  Hopper hardware result is claimed. Coverage remains 12 capabilities/11 cases,
  with Hopper partial and the required Hopper GEMM case planned.
- Goal ledger snapshot at 14:37:26 UTC: 6,940,872 tokens versus the preceding
  published 6,815,654, a difference of 125,218. This is an interim usage snapshot,
  not final billed usage. The original unbounded full goal remains active.


## Round: phase-scoped TMA publication and shared-buffer protection (2026-11-05)

- Instance and prior limit: immutable input rules covered source/descriptor/data
  agreement, but resource serialization alone could not publish TMA results to
  generic consumers. A useful rule also needed to distinguish phases and object
  lifetimes and constrain reads before shared-buffer reuse. This is engineering
  progress toward the required Hopper case, not a new-method or speedup claim.
- Prefix-derived observations: `TmaObservation` evaluates actual mbarrier
  prefixes and records the active phase plus the number of prior initializations.
  It recognizes a source-matched implicit transfer notification followed by a
  true wait in the immediately completed phase of the same lifetime. The rule is
  sufficient; it does not claim to characterize every legal parity-wait usage.
  Soundness recovers actual source/notification locations and operations,
  completed prefix states, lifetime equality and exact phase relationship.
  History-origin uniqueness connects actual indices to resource order.
- Directional publication: `ProxyPublication` uses that observation to publish
  only the same transfer's byte writes to subsequent generic accesses. It keeps
  cluster membership, wait CTA and shared byte location explicit. Source program
  order and CTA propagation are separate from implicit operations. A proof maps
  each publication to an existing actual write/notify/wait/consumer control path;
  arbitrary resource/control edges are not promoted to memory publication, and
  a transfer notification does not release arbitrary prior issuer writes.
- Reuse protection: a separate generic-to-async rule requires an actual shared
  proxy-fence event ordered after the generic access and before the new TMA
  issue, with matching thread/CTA/shared location. Actual source prefixes with
  and without this fence respectively supply and fail this protection edge.
  Cooperative readers still need checked CTA participation/propagation rules.
  Missing protection is not advertised as a full PTX execution refutation.
- Visibility fragment: gated read agreement, initial-before-write coherence,
  no-stale publication and no-future protection are explicit memory-model
  component conditions. Reusable unique-writer and repeated-phase rules select
  the source and value for arbitrary rf/co. Earlier writers must be ordered in
  coherence and later writers protected against the current read; no desired
  reply or selected rf is a client premise. Full proxy-aware race/eligibility,
  coherence, observer and complete ISA/async admission remain separate work.
- Actual new source: strict PTX 8.0/sm_90a `hopper_tma_publish.ptx` contains 16
  instructions, including a successful wait loop, shared u32 load and global u32
  store. The frontend preserves the branch target and both memory operations.
  Actual source production and completion are checked for every local read
  reply. Source PCs are 12 for the consumer load and 13 for the output store.
  The four-byte visibility argument forces the reply/store word to 3351692740,
  derived from initial bytes 196,197,198,199. A zero reply returns locally yet
  fails the visibility fragment for every rf/co when the consumer is eligible.
- Independent fragment witness: fixed input bytes determine the good source
  oracle; actual copy writers determine rf and initial-before-write coherence.
  Agreement, no-stale and no-future conditions are independently checked for all
  four consumer bytes, then instantiate the universal rule. This witness is
  intentionally a read fragment, not the full allowed-execution/observer witness
  required for closing a kernel case. Descriptor/input agreement from the prior
  round and full race eligibility are not silently folded into this claim.
- Protocol tests distinguish true/false waits, the currently completed versus
  older phases after parity repeats, and old/new initialization lifetimes at
  identical addresses/phase numbers. Explicit source `complete_tx` can satisfy
  counter arithmetic but cannot stand in for the transfer's notification.
  Synthetic protocol histories are labeled separately from actual source runs.
- Specification basis: [NVIDIA PTX ISA 8.5 async proxy](https://docs.nvidia.com/cuda/archive/12.6.3/parallel-thread-execution/index.html#asynchronous-data-movement-and-conversion-instructions-async-proxy)
  provides the implicit async/generic fence at observed bulk completion; the
  same specification restricts an implicit notification's ordering to its own
  transfer. Runtime correspondence to this definition is not newly proved.
- Remaining: full proxy/rf/co/race/observer admission with derived eligibility,
  launch/cluster/CTA participation, async in-flight lifetime and allocation/UB
  checks, descriptor encoding and initial proxy publication, WGMMA register/
  warpgroup/group semantics, and required single/double-buffer GEMM universal
  correctness plus independent full-Pre completed witnesses and concrete cases.
  The original goal, exact logits/token requirement and case acceptance criteria
  remain unchanged; Hopper stays partial and the required GEMM case planned.

- Validation: final full `scripts/check.sh` exits zero: 42 Rust tests, Clippy
  with warnings denied, six rejection-harness integration tests, 26 generated
  AST comparisons, full Lean build (3306 jobs), 3293 audited declarations,
  186 individually evaluated false assertions, and 26 assembled PTX fixtures.
  All 70 new public theorems are audited. The first rejection run correctly
  refused an unknown-name error in one new assertion; fixing its `Ptx.wrap`
  reference yielded the fully evaluated final refutation set. No elaboration
  error was counted as a false proof.
- Source-hashed assembly evidence refreshed at 14:59:51 UTC, including the new
  sm_90a fixture; all 26 hashes match. Existing GPU evidence is unchanged at
  07:46:53 UTC, with all 15 source hashes matching, 24 exact-byte cases and one
  completion-only case. There is no new Hopper GPU execution evidence.
- Goal ledger snapshot at 15:00:50 UTC: 7,035,058 tokens versus the preceding
  published 6,940,872, a difference of 94,186. This is an interim usage snapshot,
  not final billed usage. The original unbounded full goal remains active.


## Round: byte-preserved order, actual races and derived read eligibility (2026-11-05)

- Instance and prior limit: the publication helper required an explicit
  eligibility predicate. Promoting resource control or an unqualified transitive
  cross-proxy path to memory order could additionally let a shared fence publish
  unrelated global bytes. This round derives race/eligibility facts from the
  actual combined inventory. It is engineering progress, not a new-method,
  performance or full Hopper kernel-correctness claim.
- Byte-specific order: `Hopper/ByteOrder` keeps a fixed byte location throughout
  each path. It includes generic source order/CTA edges, source-issued non-bulk
  internal/completion edges, same-transfer TMA data edges, observed own-transfer
  publication and explicit shared-fence protection. Implicit operations remain
  outside issuer program order. Generic-source order at a global byte stays
  among generic source nodes; it cannot reach a TMA write through the supported
  shared fence. Absence of a source fence gives a separate source-closure rule.
- Proxy-aware races: morally strong accesses require equal proxies, matching
  complete footprints and the appropriate logical-agent or mutual-scope
  relationship. The `MemoryGraph` facade is used for actual kind/footprint facts,
  not its generic-only moral-strength/causality predicates. Observation chains
  pass through actual RMWs; causality is not arbitrarily closed across reads,
  writes or byte locations. A mixed-size race disables every read's eligibility,
  while uniform-size taint is tracked at the byte read.
- Generic reasoning rules: actual ordered conflicts imply race freedom and
  eligibility. `ByteVisibility.CausalConstraints` uses that computed predicate,
  guarded read agreement, initialization and no-stale/no-future causality.
  Its checked projection supplies the existing directional visibility rules.
  This is a causal component, not complete coherence/atomicity/observer or
  ISA admission. `ByteWitness` supplies an independent rank-based construction
  rule; ranks build individual witnesses and do not constrain all executions
  to sequential schedules. `AccessInversion` recovers actual byte kinds/locations.
- Publication family: `Tests/TmaEligibility` determines actual source memory
  event identities, every writer, shared overlap and global-input/descriptor/
  output separation. Descriptor storage occupies 4096..4223, TMA input is below
  672, output starts at 8192, and TMA destinations occupy shared 16..47.
  Every reply in the actual one-thread source family is race-free for arbitrary
  rf. The consumer word and emitted store are constrained by causal admission
  without a separate caller eligibility premise; a zero reply is impossible
  for every initial view/rf/co under those component conditions.
- Independent positive component: `Tests/TmaInputCausal` covers every real read
  of the original completed padded-copy helper, including the whole descriptor
  and every in-bounds TMA source byte. Its independent initial rf and coherence
  construct checked causal evidence together with actual source production and
  completion. There is no generic shared consumer in this helper, so it does
  not close the outstanding full consumer/coherence/observer witness or the
  required Hopper GEMM acceptance criteria.
- Negative memory probe: `Tests/TmaRaces` uses the already source-produced
  no-fence local prefix. Its u32 read and one-byte TMA write share a physical
  issuer but have different proxies/private agents and footprints 4 versus 1.
  Neither causal direction exists under initial rf, regardless of proposed
  resource histories/cluster relation, giving a checked mixed-size race and
  globally disabled eligibility. The corresponding fenced source prefix orders
  that conflict for arbitrary rf. These prefixes do not establish full resource,
  initialization, allocation, completion or launch/ISA validity; refusing a
  memory-component proof is distinguished from rejecting an entire kernel.
- Specification basis: [NVIDIA PTX ISA 8.5 moral strength and races](https://docs.nvidia.com/cuda/archive/12.6.3/parallel-thread-execution/index.html#morally-strong-operations)
  requires same-proxy moral strength and disables memory axioms in the presence
  of mixed-size races. The new definitions implement these component boundaries;
  full PTX/physical/runtime correspondence remains unproved.
- Remaining: full consumer causal/coherence/observer nonvacuity, complete
  proxy-aware memory/ISA/CTA/cluster admission and source-family classification,
  in-flight resource/allocation/UB checks, descriptor encoding/initial proxy
  publication, then WGMMA and the required single/double-buffer GEMM universal
  proofs plus independent full-Pre completed executions and concrete cases.
  The original unbounded goal, exact logits/token target and case acceptance
  criteria are unchanged; Hopper remains partial and GEMM planned.

- Validation: full `scripts/check.sh` exits zero with 42 Rust tests, Clippy
  warnings denied, six rejection-harness integration tests, 26 generated AST
  comparisons, the full 3313-job Lean build, 3340 audited declarations, 193
  individually evaluated false assertions and 26 assembled PTX fixtures. All
  47 new public theorems are audited. A source-event projection proof initially
  expanded a dependent match excessively; a bounded diagnostic isolated it,
  and the replacement pure projection checks in the normal short build. No
  timeout or elaboration failure is counted as a checked proof/refutation.
- Assembly evidence refreshed at 15:28:14 UTC and all 26 fixture hashes match.
  GPU evidence remains unchanged at 07:46:53 UTC, with 15 matching source hashes,
  24 exact-byte cases and one completion-only case. No new Hopper hardware or
  runtime-performance evidence is claimed. Coverage remains 12 capabilities and
  11 cases; the required Hopper GEMM case remains planned.
- Goal ledger snapshot at 15:30:50 UTC: 7,127,697 tokens versus the preceding
  published 7,035,058, a difference of 92,639. This is an interim usage snapshot,
  not final billed usage. The full original unbounded goal remains active.


## Round: independent consumer memory/observer closure (2026-11-05)

- Instance and prior limit: the actual TMA publication source family had
  universal conditional consumer/store constraints and derived eligibility, but
  no independent witness for every real read, full current memory components
  and final observation. This round supplies that evidence without using the
  correctness conclusion as a witness premise. It remains engineering work,
  with no optimization, novelty, performance or Hopper-hardware claim.
- Actual read witness: `Tests/TmaConsumerWitness` transfers the input helper's
  independently checked descriptor/data view, covers the entire 128-byte
  descriptor and every input data byte, and supplies the actual consumer bytes.
  RF selects initialization for immutable global inputs/descriptors and the
  matching TMA writer for consumer shared bytes. Actual fence/wait serials and
  absence of CTA barriers establish a source-region closure rule; consumer
  accesses cannot return to a prior transfer write. Same-proxy moral strength
  rules exclude spurious observation chains from the cross-proxy consumer.
  No-stale/no-future and complete read agreement then hold independently.
- Memory components: `Hopper/Memory` defines proxy-aware strict partial
  coherence, single-copy and RMW atomicity, communication/SC-per-location and
  acyclic byte base order alongside causal constraints. It includes a reusable
  unique-writer initial-coherence rule. `Tests/TmaConsumerMemory` proves every
  actual byte-edge increases a rank, writer uniqueness and absence of spurious
  strong read/write conflicts or RMWs in this particular helper. Its chosen
  coherence, atomicity and SC witnesses satisfy all these conditions. Ranking
  constructs this execution witness; universal correctness still quantifies
  over arbitrary admitted memory witnesses and does not impose that schedule.
- Global observer: `Hopper/Observation` uses the explicit generic initial view,
  the actual combined writer inventory, proxy-aware observer eligibility,
  completion and no-stale checks. Its domain must cover every actual global
  write. The selector takes values from actual writes rather than a required
  output map. `Tests/TmaConsumerObserver` constructs a 16-byte arena at
  8188..8203, covering output 8192..8195 and guard/padding bytes. For arbitrary
  admitted source-family reply/rf/co/observer, it derives every output byte and
  initial-value preservation outside the output within the observed domain.
  The selected concrete output word is 3351692740, decoded from initial bytes
  196,197,198,199. No universal frame claim is made outside an observer's domain.
- Joined evidence: `Tests/TmaConsumerChecked` checks every source-matched
  resource history and acyclic source/data/resource control for the actual
  parameterized source family, and joins these with the independently built
  full current memory and observer components for the good reply. Generic and
  async initial views are explicitly proved equal to this helper's launch
  memory. Tensormap initialization remains a distinct typed view, not an
  assumed generic-to-tensormap publication or verified CUDA binary encoder.
- Negative evidence: an observer omitting actual global writes fails mandatory
  coverage; an observer selecting stale initialization fails no-stale admission.
  A zero reply passes the actual source/resource/control components but fails
  memory admission for every initial view/rf/co. Metadata refutations check
  output-writer identity, global-only domain and guard/output byte coverage.
- Boundary: this closes this helper's current abstract memory/observer witness
  gap, not all PTX/ISA/physical-runtime admission. Complete arbitrary-source
  extraction (including other wait-oracle paths), launch/CTA/cluster and in-flight
  lifetime/allocation/UB checks, full descriptor encoding/profile/proxy-runtime
  correspondence, WGMMA and required single/double-buffer GEMM universal proofs
  plus independent full-Pre completed executions remain. Hopper stays partial
  and GEMM planned; the full original goal and exact logits/token target stay
  unchanged. Other kernel/model/runtime boundaries remain as previously stated.
- Specification basis: [NVIDIA PTX ISA 8.5 coherence and API synchronization](https://docs.nvidia.com/cuda/archive/12.6.3/parallel-thread-execution/index.html#memory-consistency-model)
  motivates strict partial coherence and synchronized final observation. The
  definitions and proofs here do not establish CUDA API or device conformance.

- Validation: final full `scripts/check.sh` exits zero with 42 Rust tests,
  Clippy warnings denied, six rejection-harness integration tests, 26 generated
  AST comparisons, full Lean build (3319 jobs), 3400 audited declarations, 201
  individually evaluated false assertions and 26 assembled PTX fixtures. All
  60 added public theorems (57 in new files and three source-region/observation
  rules in `ByteOrder`) are audited. Exact audit-line membership and metadata
  validation pass after the documentation update.
- Source-hashed assembly evidence refreshed at 15:53:29 UTC and all 26 hashes
  match. Existing GPU evidence is unchanged at 07:46:53 UTC, with 15 matching
  fixture hashes, 24 exact-byte cases and one completion-only case. There is no
  new Hopper GPU execution evidence. Coverage remains 12 capabilities/11 cases,
  with Hopper partial and the required Hopper GEMM case planned.
- Goal ledger snapshot at 15:56:18 UTC: 7,208,731 tokens versus the preceding
  published 7,127,697, a difference of 81,034. This is an interim usage snapshot,
  not final billed usage. The full original unbounded goal remains active.


## Round: WGMMA source and local async register protocol (2026-11-05)

- Instance and prior limit: the TMA/mbarrier publication helper had independently
  checked current memory/observer components, but the AST and execution entry
  could not represent WGMMA. An MMA modeled as an immediate ordinary register
  assignment would allow premature consumers and lose group completion. This
  round adds the source/local-protocol component for the required future Hopper
  GEMM. It is engineering baseline work, not a new proof-method, optimization,
  performance or hardware result.
- Fixed profile: typed PTX 8.0/sm_90a accepts WGMMA fence, commit, wait 0..7 and
  shared/shared m64n8k16 f32/f16/f16 with four distinct f32 accumulators, two
  64-bit descriptor registers, predicate or literal 0/1 scale-D, scales +1/+1
  and transposes 0/0. Unsupported shapes, types, register-A, qualifiers, scaling,
  transpose modes, operand counts and target/version combinations fail closed.
  Rust acceptance/rejection tests and Lean typing tests cover both scale-D
  forms; a generated checked AST preserves all operands and source PCs.
- Reusable execution: `Hopper/WgmmaThread` wraps the existing Hopper state with
  a ledger and consumes the same AST. Ordinary/TMA steps delegate at the same
  PC and query counter; the old entry explicitly rejects WGMMA. Explicit access
  inventories cover every accepted ordinary instruction. Pending accumulator
  reads/writes fault, while independent integer arithmetic and TMA can overlap.
  A register fence is required before first MMA and after generic accesses to
  reused accumulator names. It does not complete groups or publish shared data.
- Completion: MMA replies remain pending, and consecutive same-shape MMA takes
  its accumulator from the latest pending result. Commit creates a fresh group
  even when empty. Wait never commits; its monotone bounded cut covers mandatory
  older groups and may acknowledge extra recent committed groups. Writeback
  selects only newly completed calls and applies them in issue order. Completed
  calls cannot reopen, and repeated wait cannot replay an old write over a later
  generic register update. Well-formedness, cut bounds, ordinary-step delegation,
  generic hazard faults, missing-fence faults and invalid waits have reusable
  rules. Protocol tests exercise chained MMA and overlap with independent TMA,
  without treating this local reuse as a research-method contribution.
- Actual source: `wgmma_probe.ptx` assembles for sm_90a and mechanically produces
  `Generated/WgmmaProbe`. `Tests/WgmmaSource` checks all 128 local source runs,
  completion with no pending MMA, exact event PCs 10/11/12/13/14, lane identity,
  query numbering and identical source-derived collective schedules. The
  schedule keeps actual pre-step PCs, dynamic sequence, warpgroup, descriptors,
  accumulator names and fixed-profile arguments. It is a projection component,
  not full collective/SIMT admission. The matrix reply 16 is arbitrary test data;
  this probe's shared arrays are uninitialized and it is not a legal memory or
  tensor-arithmetic witness. There is no new Hopper GPU execution result.
- Boundary: descriptor decoding/layout and shared operand byte reads, collective
  arithmetic and control, combined proxy/memory admission, allocation/lifetime
  and runtime correspondence still need to connect to this executor. Full
  single-stage/double-buffer GEMM universal correctness, independent full-Pre
  completed witnesses and concrete admitted cases remain. Hopper stays partial,
  required Hopper GEMM planned, and the exact logits/token target unchanged.
- Specification basis: [NVIDIA PTX ISA 8.5 WGMMA](https://docs.nvidia.com/cuda/archive/12.6.3/parallel-thread-execution/index.html#asynchronous-warpgroup-level-matrix-multiply-accumulate-instructions)
  describes register fencing, group commit/wait and collective participation.
  The local rules here do not establish complete PTX or physical-device
  conformance. The paper's exact 81-form inventory remains unconfirmed.

- Validation: final full `scripts/check.sh` exits zero with 45 Rust tests,
  Clippy warnings denied, six rejection-harness integration tests, 27 generated
  AST comparisons, full Lean build (3327 jobs), 3674 audited declarations, 218
  individually checked false assertions and 27 assembled PTX fixtures. All 65
  new public theorems are audited. The source proof checks an arbitrary lane
  directly; its final leaf build takes 146 seconds in this environment. Bounded
  diagnostics isolated costly implicit matching/projections of complete states;
  explicit parameters and reusable result/completion rules avoid those paths.
  Cancelled diagnostics/timeouts are not counted as proofs or refutations.
- Audit completeness: checking names against the actual Lean environment found
  previously omitted public helpers. Another 209 environment-resolved helpers
  and proof projections now have explicit axiom audits. The gate inventories
  actual imported Ptx theorem names and requires every name matching an authored
  public theorem to occur in the audited result set. It covers 3667 such names;
  the 3674 total also includes previously selected other declarations. This
  avoids assuming a file's first namespace identifies every later declaration.
  The approved axiom boundary remains propext/Quot.sound/Classical.choice.
- Source-hashed assembly evidence refreshed at 16:45:53 UTC; all 27 hashes match.
  GPU evidence stays unchanged at 07:46:53 UTC, with all 15 source hashes matching,
  24 exact-byte comparisons and one completion-only case. No new GPU or
  performance result is claimed. Coverage remains 12 capabilities/11 cases,
  Hopper partial and required Hopper GEMM planned.
- Goal ledger snapshot at 16:46:15 UTC: 7,430,556 tokens versus the preceding
  published 7,208,731, a difference of 221,825. This is an interim usage snapshot,
  not final billed usage. The full original unbounded goal remains active.


## Round: WGMMA operand layouts, tensor admission and single-stage target (2026-11-05)

- Instance and prior limit: WGMMA had typed forms and local group/register
  protocols but no captured shared operand bytes, descriptor address mapping or
  matrix instruction constraints. A numeric oracle reply could pass the protocol
  without corresponding to any shared input. This round connects the tensor
  component to the actual source MMA. This remains engineering baseline work,
  with no optimization, novelty, performance or Hopper hardware claim.
- Accumulators: `Hopper/WgmmaLayout` gives reversible ownership of all 512
  f32 entries in a 64x8 output across 128 lanes/four registers. Arbitrary-element
  gather/scatter round trips, unique ownership/coverage and exact-real matrix
  multiply-accumulate rules are checked. Four distinct warps contribute their
  own 16-row bands; lower accumulator pairs map to the lower eight rows.
- Descriptors: `WgmmaDescriptor` retains exact 14-bit start/leading/stride
  fields in 16-byte units and rejects nonzero reserved/base/swizzle fields by
  canonical re-encoding. This is a supported profile, not a complete ISA legality
  test. The packed no-swizzle profile has leading=128/stride=256 bytes. General
  core-address functions and reversible packed byte maps prove complete,
  nonoverlapping, bounded coverage of 2048 A and 256 B bytes. This is distinct
  from the opaque CUDA TMA tensor-map encoding. The earlier source/protocol
  probe had unvalidated 16/128 strides which alias elements; those values are
  outside this packed profile, and the probe now uses corrected descriptors.
  The old descriptors are not declared universally illegal PTX descriptors.
- Captured reads: source issue captures logical A/B byte replies at the actual
  query alongside the matrix reply. `WgmmaInputs` defines all 2304 logical byte
  identities, injectivity/coverage, descriptor-derived CTA-shared locations and
  read kinds. One operation has an async warpgroup identity; it is not modeled
  as 128 unrelated memory agents. Shared read agreement and typed f16 fragments
  must hold. Integer bytes cannot be silently reinterpreted as symbolic floats.
  The byte inventory still needs integration with the full combined graph/RF.
- Tensor component: `WgmmaStorage` constructs a packed symbolic shared view for
  arbitrary real A/B, independently of any required result. `WgmmaTensor` checks
  lane/cohort metadata, descriptor profiles, all input bytes and exact-real MMA
  arithmetic. Under this component and a matrix storage view, the output follows
  the matrix specification; an arbitrary compatible accumulator is supported.
  Independent witnesses exist for arbitrary represented A/B/C. A wrong reply
  preserves cohort and read agreement but fails tensor admission. The nonuniform
  concrete component checks result 64479; it is not a GPU floating-point result.
- Source connection: `WgmmaIssueRules` proves a fetched MMA emits its actual
  source/query/operand payload and preserves call history. The generated probe's
  actual prefix and MMA step are proved for arbitrary A/B, including its emitted
  call and real PC 11. The same calls satisfy the independently built tensor
  component and yield the expected matrix result. Shared arrays in this probe
  are still uninitialized: the constructed abstract view is not a legal full
  launch, an admitted RF/observer witness or a completed GEMM verification.
- Concrete next target: `hopper_gemm_stage.ptx` now puts initialization and
  consumption in one 47-instruction source. A (4,8,4) CTA uses one leader to
  initialize/publish the barrier and issue two TMA transfers (2048+256 bytes),
  waits for completion, executes shared/shared WGMMA and four stores per lane,
  then synchronizes before barrier invalidation. A/B use explicit packed global
  tensor views. Source branch targets, transfer count and four store offsets are
  retained by translation tests. The generated AST has checked typing and the
  source assembles for sm_90a. Mathematical geometry rules cover all 512 intended
  output offsets uniquely and within bounds; they are not execution proofs of
  this new kernel's address arithmetic or launch/resource/memory legality.
- Reuse and boundary: the tensor rules work both with arbitrary independent
  A/B/C calls and the actual source-prefix call family. This is useful modular
  reuse, not evidence of a new research method. The next required step joins
  actual TMA producer bytes, prefix resource/control, WGMMA collective reads,
  proxy publication/protection, lifetime/allocation and global observation in
  one admitted execution. Single-stage and two-stage K-loop universal proofs,
  full-Pre completed execution witnesses and concrete admitted cases remain.
  Hopper stays partial, the required Hopper GEMM case stays planned and the
  exact logits/token target is unchanged. Other case/ISA/runtime/Iris boundaries
  remain as previously recorded; exact paper 81-form parity remains unconfirmed.
- Execution interface still to join: current `Hopper.Source.Produced` uses the
  original Hopper interpreter, which explicitly rejects WGMMA; the WGMMA
  executor wraps it for ordinary/TMA steps but has its own state/events. Thus
  projecting out WGMMA events cannot establish the old source predicate for
  this new kernel. The next step must connect a unified, source-checked event
  path and completed ledger to the existing resource/control/memory inventory,
  preserve actual event serials/PCs, and add the collective reads with their
  async agent identity. Independent component witnesses are not a substitute
  for that full kernel admission. Existing regression contracts must retain
  their checked source correspondence through the interface change.
- Basis: [NVIDIA PTX ISA 8.5 WGMMA layouts and descriptors](https://docs.nvidia.com/cuda/archive/12.6.3/parallel-thread-execution/index.html#asynchronous-warpgroup-level-matrix-multiply-accumulate-instructions)
  and [NVIDIA CUTLASS Major-K INTERLEAVE descriptor layout](https://github.com/NVIDIA/cutlass/blob/main/include/cute/atom/mma_traits_sm90_gmma.hpp)
  were checked, including the actual layout diagrams. No NVIDIA implementation
  is copied into the verifier or treated as a proof of hardware conformance.


- Validation: final full `scripts/check.sh` exits zero with 46 Rust tests,
  Clippy warnings denied, six rejection-harness integration tests, 28 generated
  AST comparisons, full Lean build (3337 jobs), 3758 audited declarations and
  234 individually checked false assertions. The environment-resolved public
  inventory covers 3751 names. All 83 new authored public theorems plus the
  new tensor `agreement` proof projection are audited. The completeness gate
  caught that omitted projection before the final passing run.
- Check cost: the parameterized source/tensor leaf checks in 313 seconds;
  the existing full 128-lane protocol-source leaf rechecks in 149 seconds after
  the descriptor/read-capture changes. Other new component/geometry leaves
  check in the normal short builds. Bounded diagnostic timeouts and interrupted
  exploratory runs are not counted as proofs or rejection evidence.
- Assembly evidence refreshed at 17:23:48 UTC and all 28 source hashes match,
  including the corrected WGMMA probe and new single-stage target. GPU evidence
  is unchanged at 07:46:53 UTC, with 15 matching source hashes, 24 exact-byte
  comparisons and one completion-only case. There is no new Hopper GPU result
  or runtime-performance measurement. Inventory remains 12 capabilities and 11
  cases, Hopper partial and required Hopper GEMM planned.
- Goal ledger snapshot at 17:24:22 UTC: 7,585,052 tokens versus the preceding
  published 7,430,556, a difference of 154,496. This is an interim usage snapshot,
  not final billed usage. The full original unbounded goal remains active.


## Round: unified source admission and complete single-stage source/tensor witness (2026-11-05)

- Instance and prior limit: the real single-stage target mixes ordinary/TMA and
  WGMMA instructions. The legacy Hopper interpreter explicitly rejects native
  WGMMA, so its source predicate could not admit this target; deleting native
  events would also renumber TMA/resource/store identities. This round adds a
  rich source interface and joins actual producer/consumer/source components.
  It is engineering baseline work, with no optimization, novelty or performance
  claim and no new Hopper hardware evidence.
- Source interface: `UnifiedView` maps each native event to exactly one opaque
  legacy event slot and retains every ordinary/TMA event, thread ID, serial and
  actual PC. Presence, lookup, event count and located erasure are preserved.
  Tags grant no ordinary access, barrier operation or CTA rendezvous. The rich
  candidate remains authoritative for WGMMA calls. A projected fake MMA tag
  cannot create an implicit operand read. No legacy `Produced` assertion is
  made for a mixed program; the old interpreter's rejection remains tested.
- Checked execution: `UnifiedSource` uses the real WGMMA interpreter and
  requires physical thread coverage, unique IDs and source-produced traces.
  Unified completion additionally requires an empty pending ledger. A returned
  source thread with outstanding WGMMA is rejected even though its legacy base
  status is done. `UnifiedStep` derives actual ordinary/TMA step origin and
  query/payload length from source delegation. Existing source-length-dependent
  access/input rules are factored through reusable length lemmas and retain
  their original legacy APIs and proofs.
- Resource component interface: `UnifiedComponents` combines this source and
  completion predicate with the existing descriptor, payload, history and
  control checks on the number-preserving view. The TMA byte-presence and
  immutable-input-memory rules now accept shape facts proved from actual rich
  source execution. A component record alone does not construct the histories
  or establish combined WGMMA memory/ISA admission.
- Combined inventory: `UnifiedAccess` retains ordinary/RMW/non-bulk/TMA access
  nodes and adds all 2304 logical operand reads of an actual lane-zero MMA
  representative. The reads have their descriptor-derived CTA-shared location,
  captured byte, async proxy and a distinct operation identity (separate from
  TMA and issuer threads). They do not enter issuer program order. This is an
  inventory graph, without full launch/completion/proxy, RF/coherence, moral
  strength, race or causality admission; generic-only memory rules do not apply
  to it. `UnifiedCollective` matches 128 distinct actual MMA source events,
  physical lanes, CTA, mark, descriptors, destination names, ordinal and group.
  Full fence/commit/wait collective schedules remain separate obligations.
- Actual stage source: normalized checkpoints compose with `run_add` and the
  same generated 47-instruction AST and fixed interpreter. They prove complete
  execution for every physical lane and arbitrary represented real A/B, with
  leader-derived branching, not an assumed leader flag. The leader executes
  47 steps and peers 41; their native MMA events are at serials 9/4, source PC
  29 and actual queries 5/1. All 128 actual calls form one source-matched cohort.
  The leader's actual TMA events at serials 5/6 carry the two checked payloads.
- Tensor connection: actual packed descriptors have shared bases 16/2064.
  `HopperStageTensor` constructs one abstract post-transfer byte view and proves
  that both complete TMA payloads and every WGMMA operand agree with that view.
  Its source-matched calls satisfy tensor conditions and compute the exact-real
  64x8x16 matrix product with zero C for arbitrary A/B. This does not identify
  the chosen source oracle with arbitrary launch.initial or prove the transfer
  has a valid resource/RF/publication history.
- Actual outputs: `HopperStageAddressValues` removes machine-word wraps from
  the source address checkpoint using physical launch bounds. Every actual
  store address follows the reversible accumulator layout and its four bytes
  lie in global [8192,10240). `HopperStageOutput` identifies all 512 emitted
  candidate store events and their matrix-valued symbolic bytes. The concrete
  nonuniform last source store writes 1472 at 10236. These are actual source
  events; selecting them in a legal global observer remains unproved.
- Reuse and remaining boundary: the old TMA access/input predicates retain their
  checked source correspondence and APIs, while the rich source uses the same
  shape lemmas and tensor rules. This is modular reuse, not research novelty.
  Still open: collective schedule checks; concrete resource/control histories;
  global initial input/descriptor agreement; full combined RF/coherence/proxy,
  race, allocation/lifetime and observer admission; universal correctness for
  arbitrary admitted candidates; and an independent completed witness under the
  full identical kernel Pre. The required double-buffered K-loop GEMM remains
  planned, Hopper remains partial, paper 81-form parity remains unconfirmed and
  all other ISA/runtime/Iris/numerical boundaries remain as previously recorded.
- Proof cost: full unnormalized 128-lane execution expansion exhausted an
  exploratory heartbeat budget and was not counted as a proof. Checked source
  checkpoints avoid repeated complete-state expansion without adding premises:
  prefix 62 seconds, transfer 4.1 seconds, native 1.2 seconds, address 6.2
  seconds, stores 2.7 seconds, finish 1.1 seconds and composition 4.8 seconds in
  individual builds. No diagnostic failure/timeout counts as a refuted assertion.

- Validation: final full `scripts/check.sh` exits zero with 46 Rust tests,
  Clippy warnings denied, six rejection-harness integration tests, 28 generated
  AST comparisons, full Lean build (3357 jobs), 3906 audited declarations and
  255 individually evaluated false assertions. The environment-resolved public
  inventory covers 3899 names. All 143 new authored public theorems, two new
  shared helper theorems and three matching proof projections are audited.
  The 21 added false assertions cover dropped/renumbered native slots, tags
  incorrectly granting accesses/barriers, fake readers, pending return, legacy
  entry rejection, async agent/proxy identity and leader/peer query/serial
  mistakes. Every refutation uses closed decidable metadata, not Real equality.
- Regression: adding the opaque event tag required one explicit no-access case
  in an old TMA test; it is now checked. The existing full 128-lane source and
  arbitrary-A/B tensor-source leaves recheck successfully in 148/318 seconds.
  The first gate run's missing-case error is recorded as a failure, never as
  rejection evidence; the final complete gate passes.
- Assembly evidence refreshed at 18:37:45 UTC; all 28 current source hashes
  match. GPU evidence remains at 07:46:53 UTC with all 15 source hashes matching,
  24 exact-byte comparisons and one completion-only case. There is no new
  Hopper GPU result or performance measurement. Inventory remains 12
  capabilities and 11 cases; Hopper partial and required Hopper GEMM planned.
- Goal ledger snapshot at 18:38:01 UTC: 7,868,515 tokens versus the preceding
  published 7,585,052, a difference of 283,463. This is an interim usage snapshot,
  not final billed usage. The full original unbounded goal remains active.


## Round: aligned schedules, real input bytes and full TMA resource/control components (2026-11-05)

- Instance and prior limit: the 47-instruction single-stage target had complete
  128-thread source/tensor witnesses and actual matrix-valued output stores,
  but its source oracle was not connected to global input storage. MMA membership
  alone did not check the fence/commit/wait sequence. No exhaustive resource
  history or combined source/CTA/TMA/resource control witness existed for this
  target. This round closes those component gaps for arbitrary real A/B; it
  does not complete memory admission or the required Hopper GEMM case. This is
  baseline engineering, with no optimization, novelty or performance claim.
- Aligned schedules: `WgmmaSignatureRules` derives the mark's PC, dynamic
  sequence and physical warpgroup from actual native steps. Raw event schedules
  agree with checked located replay. `UnifiedSchedules` checks every physical
  lane in each participating warpgroup against the full fence/MMA/commit/wait
  sequence, retaining PCs, operation metadata and descriptor uniformity. Raw
  signatures retain the evaluated per-thread D predicate; the aligned key does
  not add an unrequired uniform local-predicate condition. Source/tensor value
  semantics retain that predicate. Ordinary-only threads need not form a native
  warpgroup. The actual stage's four native operations at PCs 28..31 pass for
  arbitrary A/B despite the leader/peer query and event-serial differences.
- Stronger counterexample: a small handwritten source AST runs all 128 physical
  threads to completion with no pending matrix operation, but only tid.x=0
  threads commit an empty group. Source coverage, unique IDs and completion are
  proved; aligned admission rejects it. This exercises empty collectives even
  when there is no MMA membership to check. The AST is a semantic litmus, not
  a newly generated/assembled PTX or GPU fixture. Metadata fixtures separately
  check that raw local D scale is retained without requiring it to be uniform;
  no source/tensor admission is claimed for those synthetic fixtures.
- Independent initial storage: `HopperStageInputs` constructs the two opaque
  128-byte tensor-map objects at global 4096/4224, packed f16 A/B inputs at
  65536/69632 and an arbitrary unchanged frame elsewhere. `TmaPackedRows`
  proves the real TMA byte-address function returns base+offset for arbitrary
  contiguous 128-element f16 row count, base and in-bounds offset. The same
  rule handles both transfers. Every actual source TMA copy is classified,
  its descriptor matches the stored map and its complete payload agrees with
  the initial global bytes. This covers all source copies, not two unconnected
  example accesses. These are symbolic tensor-map/f16 storage representations;
  native CUDA tensor-map encoding and IEEE behavior remain external boundaries.
  An otherwise source-complete candidate with incompatible integer initial
  input bytes is explicitly rejected by payload agreement.
- Resource history: `HopperStageResources` independently supplies 133 entries:
  initialization; arrive-expect-tx 2304; distinct actual notifications for A's
  2048 and B's 256 bytes; every physical thread's successful wait; and final
  invalidation. Origin uniqueness, exhaustive permutation of the actual source
  inventory, per-thread order and the full mbarrier protocol are proved. All
  resource locations other than the one actual shared barrier have empty
  histories. Notification identities/counts follow actual source events; no
  matching oracle invents them. The final retired barrier is `none`.
- Checkable metadata erasure: `TmaResourceErasure` discards memory payloads,
  oracles and final states only for resource/control checking. It preserves
  all event slots, IDs, presence, mbarrier operations, CTA tags, TMA descriptor/
  address metadata, notifications, inventories and internal/control edges.
  History validity and control acyclicity are equivalent before/after erasure.
  These are generic proved projection rules, including invalid source data;
  the erased candidate is never asserted to be source-produced or complete.
  No memory agreement, RF map, visibility, allocation or ownership is granted
  by erasure. The actual rich source witness remains checked independently.
- Control witness: a strict rank handles source program order, both actual CTA
  rendezvous, TMA issue/descriptor/read/write/notification nodes and the full
  resource serialization. `TmaResourceRank` proves the reusable link from a
  pairwise-ranked finite history to resource-edge order. The actual stage's
  control graph is acyclic for arbitrary A/B. This is an independent witness
  aid, not a restriction requiring all allowed executions to share this rank;
  resource/control ranks are not reused wholesale as memory causality.
- Actual completion observation: every one of the 128 source waits observes
  both distinct TMA notifications at the correct object lifetime and completed
  phase. `HopperStageCompletion` checks `CompletionObserved` with explicit
  same-CTA cluster scope for this one-CTA launch. No claim for arbitrary
  clusters is made. This resource observation still needs a valid memory rule
  before it can justify a native async operand read.
- Component composition and reuse: `stage_tma_components` checks rich source
  production/completion, initial descriptor/payload agreement, all histories
  and control under the same represented input. `stage_checked_components`
  joins these facts with full aligned schedules and the source-matched tensor
  component for arbitrary A/B and arbitrary initial frame. Existing tensor,
  TMA shape and byte/input contracts are reused; the contiguous-row and erasure/
  rank rules are reused across A/B and the whole original resource interface.
  No correctness theorem or desired output is assumed to construct the witness.
  Output store correctness remains at the symbolic source-event boundary.
- Tests distinguish failure causes: dropping either implicit notification
  prevents completion. Invalidating after the first wait preserves the entire
  actual entry inventory and per-thread source order, but the protocol rejects
  later peer waits on the retired object. Initial descriptor offsets, f16 byte
  positions, unmodified guard bytes, transfer-specific observations, lifetime/
  phase and CTA/source ranks are checked. Finite metadata refutations use no
  Real/Event/State equality decider. Positive symbolic input tests use checked
  algebra/proofs; their nonuniform final A/B bytes contain 64/23 respectively.
- Remaining work: native collective-control and operand completion edges in the
  combined graph; WGMMA RF/coherence/proxy/race, allocation/lifetime and global
  observer admission; universal correctness for arbitrary admitted source
  candidates (including finite unsuccessful-wait loops); an independent complete
  execution under the identical full kernel Pre; and the required double-buffer
  K-loop GEMM. The next step must connect TMA byte writes to native async reads
  in the combined memory model, rather than treat these components as a finished
  GEMM proof. Hopper remains partial, required Hopper GEMM planned, exact paper
  81-form parity unconfirmed, and all other runtime/Iris/ISA/numerical boundaries
  remain. No numerical/logits/token requirement is weakened.
- Basis: the aligned collective/register and shared-descriptor requirements
  were checked against [NVIDIA PTX ISA 8.5](https://docs.nvidia.com/cuda/archive/12.6.3/parallel-thread-execution/index.html#asynchronous-warpgroup-level-matrix-multiply-accumulate-instructions).
  The implementation does not turn equality of these schedules into a memory
  fence or claim full SIMT/hardware conformance.
- Validation: the final full `scripts/check.sh` exits zero with 46 Rust tests,
  Clippy warnings denied, six rejection-harness integration tests, 28 generated
  AST comparisons, full Lean build (3374 jobs), 4005 audited declarations and
  275 individually evaluated false assertions. All 99 new authored public
  theorems have exact dependency audits; the environment-resolved public-name
  inventory covers 3998 names. Twenty new closed false assertions extend the
  existing gate; errors/timeouts are not counted as refutations. Coverage
  inventory remains 12 capabilities and 11 cases, with metadata validation only.
- Check cost: checked native signature origin/replay 2.6 seconds, schedule
  checker/rules 1.1 seconds, actual stage schedule 1.2 seconds, input connection
  4.2 seconds, exhaustive resource history 26 seconds, resource metadata 32
  seconds, control metadata 24 seconds, resource/control composition leaves
  1.1..1.5 seconds, all-lane completion observations 5.9 seconds, source-divergent
  collective litmus 5.1 seconds and input/resource tests 13 seconds in individual
  builds. Closed metadata leaves are separated from reusable symbolic proof
  leaves so proof edits do not repeatedly rebuild the finite inventories.
- Assembly evidence refreshed at 19:11:42 UTC; all 28 current source hashes
  match. GPU evidence remains at 07:46:53 UTC with all 15 source hashes matching,
  24 exact-byte comparisons and one completion-only case. There is no new
  Hopper GPU result, runtime performance or proof-to-hardware claim.
- Goal ledger snapshot at 19:14:18 UTC: 8,034,109 tokens versus the preceding
  published 7,868,515, a difference of 165,594. This is an interim usage snapshot,
  not final billed usage. The full original unbounded goal remains active.


## Round: native proxy/byte memory order and forced TMA operand reads (2026-11-05)

- Instance and prior limit: the single-stage source/input/resource/control/
  tensor witness observed both TMA completions, but native reads were only an
  access inventory. It had no shared byte-memory edge from an actual TMA write
  to WGMMA, no whole-inventory native race eligibility and no rule forcing
  native RF. This round supplies the native memory fragment and connects all
  2304 actual operand reads to their producers. It is engineering baseline
  work, not a new GPU optimization or research novelty claim.
- Native primitives: `UnifiedNativeOrder.TmaReady` names the actual transfer
  byte and matching descriptor-derived native location. It requires an actual
  source-matched 128-lane collective and transfer-specific completion observation
  followed by source order to every participant (possibly through CTA edges).
  Generic shared accesses instead require an actual async proxy fence before
  each participant's issue. Mere source launch or resource/control order is not
  a byte publication rule. No desired reply, chosen RF or arithmetic answer is
  a publication premise.
- Completion and reuse: `WgmmaCompletedAt` matches a later actual source wait
  to a participating thread, warpgroup and dynamic sequence. Its observed cut
  must exceed the call's group and remain within committed groups, with valid
  before/after and keep bounds. Native read completion can order subsequent
  generic accesses; reuse additionally orders the observed wait before the
  new actual TMA issue at the same byte. An uncommitted group cannot be finished
  by a zero-group wait. No actual native wait means no completion or justified
  native reuse. These are byte-specific rules; all conflicting in-flight users
  still need checking before a whole buffer can be reclaimed.
- Proxy-aware memory: `UnifiedBytes/Order/Causal/Memory` define read/write
  bytes, explicit proxy views, moral strength, byte-preserved order, observation,
  races, taint and derived eligibility over ordinary/RMW/non-bulk/TMA/native
  nodes. Causal constraints and coherence/atomicity/SC-per-location components
  cover this full inventory. Native reads retain their distinct async agent
  and remain outside issuer program order; the generic-only MemoryGraph strength
  predicate is not applied to them. Original base-node access/strength/ordering
  interfaces remain intact. Generic rank-based causal witness and initial-co
  helpers are available, but are not a constructed native kernel witness.
- Conservative global order: incoming native read edges necessarily concern
  the operation's shared CTA location. The checked `global_base_order_iff`
  proves that global-byte paths between base nodes are exactly the original
  Hopper ByteOrder. Native completion/publication cannot leak ordering onto an
  unrelated global byte. No proxy fence is synthesized from a WGMMA register
  fence, collective schedule match or arbitrary control path.
- Actual source connection: `HopperStageNativePublication` proves each actual
  source mbarrier wait precedes that lane's actual MMA event, and matches both
  actual TMA write locations to the packed descriptor operand locations.
  Every A/B byte has an actual `NativePublished` edge. Complete native source
  waits are separately matched to group completion at the real PC/serial/
  query, and every native read has its checked completion edge. These proofs
  use the existing all-thread source/resource histories, not invented events.
- Exhaustive writers and regions: `HopperStageMemoryInventory` proves all
  ordinary source writes are global, non-bulk accesses are absent, and every
  shared writer is one of the two actual source TMA transfers. Distinct A/B
  arenas and byte offsets identify a unique producer for each native operand.
  Source footprint projection retains all four actual output words per lane.
  The full inventory separates one-byte shared accesses, aligned four-byte
  global outputs [8192,10240), low 128-byte descriptor reads and high packed
  input reads. These regions and actual widths derive no mixed-size race for
  every RF; this is not an assumed allocation separation or eligibility flag.
- Derived native values: actual byte publication and unique shared writers
  exclude native taint. Together with the whole-candidate mixed-size proof,
  `native_eligibility_derived` has no additional caller no-race/eligibility
  premise. `native_rf_forced` holds for every RF/co satisfying the new causal
  memory constraints on this arbitrary-real-A/B source family: every operand
  selects its exact actual TMA byte. `native_input_agreement_derived` obtains
  the represented matrix input view through memory. An initial-only RF is
  rejected even if its initial bytes could equal the copied values. This is
  universal conditional visibility on the constructed source family, not an
  independent existence proof of those memory constraints or a universal
  correctness theorem over all admitted PTX source candidates.
- Actual in-flight counterexample: `HopperStageNativePrefix` checks generated
  source prefixes for arbitrary A/B in all 128 physical lanes. The leader/
  peers execute 31/26 steps and stop at PC 31 after commit, before native wait.
  All actual MMA events form a full matched collective, every lane retains one
  pending operation and no native wait exists. These source prefixes cannot
  justify reuse. They are not complete launches. The counterexample does not
  rely on a missing participant or a synthetic mismatch of final state/events.
- Reusable rules: unique-writer and phase-writer visibility quantify over
  arbitrary compatible RF/co; phase rules permit multiple writes when other
  writes are proved earlier than the selected phase or later than the read.
  Existing TMA input/resource components and graph footprint facts are reused.
  The whole-candidate region proof derives the global eligibility condition;
  it is not replaced by eligible=True. This is verification engineering reuse,
  not evidence of a novel optimization/proof method.
- Test scope: symbolic tests check actual first/last-byte publication, derived
  eligibility, forced RF rejection, native wait acknowledgment and full-cohort
  source-prefix no-reuse. Generic no-fence and zero-group completion rules are
  checked. Closed metadata assertions exercise wrong producer IDs/offsets,
  shared/global aliasing, proxy/write/footprint errors and premature source/
  group completion. No Real/Event/State equality decider is introduced. The
  existing source/register/TMA regressions and exact numerical target remain.
- Remaining boundary: independent causal/full memory RF/co witnesses for this
  source family; full native collective-control and base-order acyclicity;
  global output observer/frame admission; allocation/lifetime and runtime/Iris
  correspondence; arbitrary-candidate source reconstruction including finite
  unsuccessful waits; full identical-Pre correctness/nonvacuity; and the
  required double-buffered K-loop GEMM. Defining the memory component and
  deriving values conditionally does not discharge existence or full kernel
  admission. Hopper remains partial, the required Hopper GEMM case planned,
  exact paper 81-form parity unconfirmed and the full original goal active.
- Basis: [NVIDIA PTX ISA 8.5 async completion and proxy rules](https://docs.nvidia.com/cuda/archive/12.6.3/parallel-thread-execution/index.html#asynchronous-warpgroup-level-matrix-multiply-accumulate-instructions)
  were checked for observed async completion, register fencing and native group
  waits. The new constraints are a model-relative memory fragment; a formal
  equivalence with every hardware-allowed PTX execution is not claimed.
- Validation: the final full `scripts/check.sh` exits zero with 46 Rust tests,
  Clippy warnings denied, six rejection-harness integration tests, 28 generated
  AST comparisons, full Lean build (3391 jobs), 4126 audited declarations and
  295 individually evaluated false assertions. All 98 new authored public
  theorems plus 23 new memory/race proof projections have exact audits; the
  environment-resolved public-name inventory covers 4098 names. Twenty new
  closed false assertions extend the existing gate. Failed exploratory tactic
  attempts are not counted as proofs or refutations. Coverage metadata remains
  12 capabilities/11 cases; its validation is not proof coverage.
- Check cost: new generic memory/race/visibility/safety leaves check in about
  1.1..1.3 seconds; actual publication 1.2 seconds; source writer/footprint/
  region leaves in short symbolic builds; whole-inventory native eligibility
  1.6 seconds; actual source-prefix/collective proof 5.1 seconds; memory tests
  1.1 seconds in individual builds. State/event equality is not enumerated.
  Existing large source proofs did not change; full dependency audit still ran.
- Assembly evidence refreshed at 19:57:52 UTC; all 28 current source hashes
  match. GPU evidence remains at 07:46:53 UTC with all 15 hashes matching,
  24 exact-byte comparisons and one completion-only case. There is no new
  Hopper GPU result or runtime performance measurement.
- Goal ledger snapshot at 20:00:23 UTC: 8,190,356 tokens versus the preceding
  published 8,034,109, a difference of 156,247. This is an interim usage snapshot,
  not final billed usage. The full original unbounded goal remains active.


## 2026-11-05 — Independent native memory and completed observer witnesses

- Optimization instance and classification: continue the actual 128-thread
  one-phase Hopper TMA/WGMMA stage toward the required double-buffered GEMM.
  This round is substantive progress: it closes independent memory/observer
  existence for that source family. It is verification engineering, not a new
  ownership method or a completed optimization experiment.
- Previous limitation: native byte visibility was conditional on a caller's
  compatible causal RF/co. Defining a consistency predicate and showing that
  it forces the desired reads did not establish that an actual completed
  source execution could satisfy it. Unindexed store footprints also could
  not distinguish the identities of all actual output writers.
- New construction: `HopperStageNativeRankData` computes only unambiguous
  source MMA/wait metadata ranks. Erased ordinary-event fence placeholders
  are deliberately excluded. `HopperStageMemoryRank` ranks every actual byte
  edge: source generic/CTA order, tensor data, observed TMA publication,
  explicit proxy-fenced generic publication and native completion. Reuse
  would need a completed native wait before a later actual transfer; this
  one-phase source has no such transfer. Strictly increasing byte paths
  establish base-order acyclicity. Control paths bound justified memory edges;
  they do not create new memory edges or publication permissions.
- Independent RF and input agreement: `InitialReadAgreement` is a reusable
  descriptor/data read constructor that preserves the tensormap and async
  proxy indices. The actual source has no ordinary reads and no non-bulk
  copies. `HopperStageReadWitness` selects initial storage for descriptor and
  TMA input reads, and each exact actual TMA producer for native operand reads.
  All read values agree for arbitrary represented real A/B and frame, without
  assuming any causal execution. Exhaustive read/write conflict inversion
  proves initial input/descriptor reads immutable; overlapping read/write
  pairs are exactly native reads and their shared TMA producers.
- Full memory component: native/TMA agents are distinct and neither access is
  a scoped RMW, so these pairs are not morally strong. No observation-order
  edge is invented from their RF link. Source-indexed output footprints keep
  the actual event serial. Packed byte inverses and reversible C coordinates
  derive unique writers for every shared/global byte, including every one of
  the 512 output words. The explicit initial-before-writer coherence witness
  satisfies causal initialization/no-stale/no-future, coherence, single-copy
  atomicity, RMW atomicity and per-location SC. `stage_memory_exists` constructs
  RF/co satisfying the complete defined unified memory component and derived
  no-mixed-size-race for arbitrary A/B/frame; it has no assumed admission premise.
- Completed observer: `UnifiedObservation` carries the existing combined
  observer obligations to the rich native inventory, including completion with
  no pending WGMMA calls. `HopperStageObserverWitness` derives the writer for
  every output byte from its actual C-layout owner. Its finite global domain
  [8188,10244) covers every actual global write and four frame bytes on each
  side. A compatible observer cannot hide an emitted write or select stale
  initial storage. `stage_independent_components` combines actual generated
  source, input/resources, TMA control, aligned native schedules, tensor,
  memory and completed-observer witnesses on the same source family.
- Contracts and reuse evidence: `observed_matrix_byte` proves all 2048 output
  bytes are the f32 symbolic fragments of the matrix specification, for every
  compatible RF/co/observer on this actual source family. `observed_frame`
  preserves unwritten domain locations; the independently constructed observer
  preserves both four-byte guards. Existing generic visibility, TMA control,
  tensor layouts and source production proofs are reused. This does not prove
  correctness over arbitrary source candidates or a new reusable async
  ownership protocol.
- Tests: arbitrary-input memory existence, a concrete nonuniform source's
  memory/observer components, first output 1 and last output 1472, both frame
  guards and parameterized stale/omitted-observer rejection. Twelve additional
  closed metadata refutations cover RF producer selection, reversed ranks,
  wrong C owners and missing/aliased observation coverage. No Real/Event/State
  equality decider is introduced. An initial rejection run failed on a missing
  import; it was corrected and is not counted as a logical refutation.
- Remaining boundary: full native collective-control admission, allocation and
  in-flight lifetime/runtime/Iris correspondence; arbitrary-source correctness
  including finite unsuccessful waits; identical full-Pre correctness and
  completed execution witnesses; and the required double-buffered K-loop GEMM.
  Memory-component and observer existence does not close these obligations.
  Exact-real tagged fragments are not IEEE bytes; this round supplies no
  Hopper hardware result, logits/token equivalence or performance measurement.
  Hopper remains partial, the required double-buffered case remains planned,
  exact paper 81-form parity remains unconfirmed and the original goal active.
- Validation: final full `scripts/check.sh` exits zero: 46 Rust tests, Clippy
  warnings denied, six rejection-harness integration tests, 28 generated AST
  comparisons, full Lean build (3404 jobs), 4208 audited declarations and 307
  individually evaluated false assertions. All 77 new authored public theorems
  and five new observer proof projections have exact dependency audits;
  the environment-resolved inventory covers 4177 names. Thirteen new modules
  are registered. Coverage metadata remains 12 capabilities/11 cases.
- Check cost: individual symbolic leaves checked in about 1.1..2.6 seconds:
  byte rank 1.4, read witness 2.6, read-conflict inversion 1.4, indexed stores
  1.5, writer uniqueness 1.6, complete memory witness 1.1, observer witness
  1.3, observed output 1.2 and new tests 1.4. Existing large source proofs are
  reused and the whole dependency audit ran; no proof-obligation assumptions
  or target relaxation were added to obtain these measurements.
- Assembly evidence refreshed at 20:33:03 UTC with all 28 current source hashes
  matching. GPU evidence remains at 07:46:53 UTC with all 15 source hashes
  matching and 25 recorded cases; this round did not rerun GPU execution.
- Goal ledger snapshot at 20:35:01 UTC: 8,371,184 tokens versus the preceding
  published 8,190,356, a difference of 180,828. This is an interim usage snapshot,
  not final billed usage. The original unbounded goal remains active.


## 2026-11-05 — Native construct control and an actual circular-wait source

- Optimization instance and classification: continue the Hopper stage needed
  for double-buffered TMA/WGMMA GEMM. This round is substantive progress:
  source-matched native synchronization and issue/completion now join the
  existing source/CTA/TMA/resource control graph. This is verification
  engineering; no novel ownership protocol or optimized speedup is claimed.
- Concrete old limitation: complete source traces and identical full aligned
  native schedules do not exclude a native/CTA circular wait. Checking source
  PCs and matching all 128 participants alone did not supply rendezvous edges
  to the global construct-control graph. Independent memory/observer existence
  from the preceding round did not discharge this control obligation.
- Normative boundary: [PTX ISA 8.5 WGMMA proxy operations](https://docs.nvidia.com/cuda/archive/12.6.3/parallel-thread-execution/index.html#asynchronous-wgmma-proxy-operations)
  defines warp-local `.sync` waiting and warpgroup-wide `.aligned`
  participation. The new rules preserve that distinction. The paper's
  [construct matching component](https://sf-tensor.com/papers/formalizing-ptx.pdf)
  is the alignment target, not a claim that this subset is complete PTX.
- New generic model: `UnifiedControl` gives each native instruction a separate
  arrival endpoint and source return endpoint. Prior source events lead to
  that lane's arrival; matching actual signatures create arrival-to-return
  edges only within the same physical 32-thread warp. Signatures retain PC,
  dynamic sequence, warpgroup, operation and fixed-profile operands; only the
  evaluated local scale-D predicate is normalized, as in the aligned checker.
  Source returns issue the implicit native operand nodes, and actual matched
  group waits finish them. Source/CTA/TMA/resource control is lifted intact.
  `ControlAdmitted` combines aligned schedules with global construct acyclicity.
  These are completed-candidate construct components, not a replacement for
  partial-prefix participation, ISA/UB or hardware conformance semantics.
- Source correspondence: `UnifiedControlParticipants` turns schedule matching
  into actual event IDs for every one of the 128 physical participants. It
  then obtains all 32 same-warp rendezvous participants and their checked PCs
  from produced source traces. `UnifiedControlCheck` compares only coordinates
  and source-signature metadata; it adds no Real/Event/State equality decider.
  A source return cannot become its own earlier arrival. Different warps and
  different PCs/sequences/instructions do not synchronize under this relation.
- Independent positive witness: `HopperStageNativeInventory` retains actual
  native event serials, including the real fence. Erased ordinary-event fence
  placeholders cannot be used for this purpose. `HopperStageNativeControl`
  constructs a strict rank for every base, arrival, rendezvous, issue and
  finish edge on the actual arbitrary-real-A/B stage family. The new control
  component is checked alongside the preceding independent full memory and
  observer witnesses on the same candidate. Peer returns of one native
  instruction are not incorrectly ordered against one another; rendezvous
  runs from arrivals to returns instead.
- Actual failure/reuse evidence: `hopper_collective_cycle.ptx` is a generated
  eight-instruction sm_90a fixture. In a (4,8,4) CTA, tid.x=0 lanes execute a
  native fence before CTA barrier 0; other lanes execute the barrier before
  that same fence. All 128 source-local runs finish with no pending operations
  and have the same aligned fence schedule. There are no TMA copies/resources;
  an explicit rank proves the original source/CTA/TMA control graph acyclic.
  The new same-warp rendezvous closes a cycle through the actual CTA events,
  excluding every candidate native-control family. The proof uses the same
  generic cycle-exclusion rule as the positive graph composition. This is a
  construct-admission counterexample, not a GPU termination theorem. The
  circular-wait fixture is assembled only and never GPU-launched.
- Test scope: arbitrary-A/B positive control and memory/observer composition,
  all physical warp participants' actual source PCs, within-warp acceptance,
  cross-warp/different-instruction rejection, actual fence serials, arrival vs
  return ranks, unordered peer returns and the generated complete/aligned/
  legacy-control-pass/native-control-fail case. Twelve closed false metadata
  assertions supplement the parameterized proofs. A quadratic full-check
  refutation hit Lean's heartbeat limit and was rejected by the harness; it
  was replaced by a local schedule metadata refutation while retaining the
  all-participant symbolic proof. Neither that timeout nor failed exploratory
  tactics count as logical refutations. The checker was not weakened.
- Remaining boundary: full allocation/in-flight lifetime/runtime/Iris
  correspondence; arbitrary-source correctness including finite unsuccessful
  waits; identical full-Pre correctness and completed execution witnesses;
  and the required double-buffered K-loop GEMM. A valid native construct graph
  does not synthesize byte/proxy visibility, establish allocation safety or
  prove arbitrary-source output correctness. Hopper remains partial and the
  required double-buffered case planned. Exact paper 81-form parity remains
  unconfirmed. Exact logits/token targets and symbolic-real/IEEE distinctions
  are unchanged; no new Hopper hardware or performance result is claimed.
- Validation: final full `scripts/check.sh` exits zero with 46 Rust tests,
  Clippy warnings denied, six rejection-harness integration tests, 29 generated
  AST comparisons, full Lean build (3413 jobs), 4281 audited declarations and
  319 individually evaluated false assertions. All 73 new authored public
  theorems have exact dependency audits, and the environment-resolved public
  inventory covers 4250 names. Nine new Lean modules, including the generated
  circular-wait target, are registered. Inventory remains 12 capabilities and
  11 cases; this count is metadata, not proof coverage.
- Check cost: the new participant linkage and construct-rank leaves check in
  about 1.1..1.3 seconds; the symbolic native inventory about 2.4 seconds;
  generated cycle source metadata/participation about 7.5 seconds; its legacy
  control witness about 8.9 seconds; the combined tests about 1.1 seconds.
  An early quadratic schedule enumeration was interrupted after inspecting its
  live process and memory use, then replaced with a per-trace metadata proof
  and symbolic all-participant construction. It is not counted as a test pass.
- Assembly evidence refreshed at 20:58:31 UTC with all 29 current source hashes
  matching. GPU evidence remains at 07:46:53 UTC with all 15 recorded source
  hashes matching; this round did not rerun GPU execution. The new cyclic
  fixture is excluded from GPU launches.
- Goal ledger snapshot at 21:00:00 UTC: 8,476,551 tokens versus the preceding
  published 8,371,184, a difference of 105,367. This is an interim usage snapshot,
  not final billed usage. The original unbounded goal remains active.


## 2026-11-05 — Actual double-buffered K-loop target and reusable phase rules

- Optimization instance and classification: the required Hopper GEMM now has
  its own actual two-stage K-loop PTX target, rather than relying on the prior
  one-phase target. This is substantive implementation/proof progress and
  changes the acceptance-case inventory from planned to partial. It is not a
  completed kernel verification, measured speedup or new ownership method.
- Previous limitation: the one-phase source had only one TMA fill and one MMA;
  unique shared writers could not model repeated buffer writes. It provided no
  actual next-tile prefetch, alternating barriers or parity reuse. A static
  descriptor start address also depended on assumed shared symbol placement.
- Actual source: `hopper_double_buffer_gemm.ptx` has 101 typed instructions,
  one (4,8,4) CTA, a 64x8 output tile and K=16*TILES. Each TMA stage contains
  2048 A bytes and 256 B bytes, with separate 8-byte mbarriers. Next-tile TMA
  issues precede the producer's current MMA. Each current committed group is
  waited on, followed by CTA barrier 2 before later reuse. The next transfer
  can remain in flight during current computation; no throughput or physical
  overlap measurement has been made. The per-iteration rendezvous cost must
  be measured before claiming optimization benefit. T=0 also takes a no-TMA/
  no-MMA zero-output path; the required nonempty K-loop remains the main target.
- Runtime descriptors and frontend extension: the PTX derives all four packed
  descriptors from the actual shared symbol addresses. `shr.u32`/`shr.u64`
  now have explicit AST, typing and unsigned word semantics. The second operand
  is u32 for both value widths, and counts at/beyond the value width yield zero,
  as specified by [PTX ISA 8.5 shr](https://docs.nvidia.com/cuda/archive/12.6.3/parallel-thread-execution/index.html#logic-and-shift-instructions-shr).
  `ISA/Shift` proves clamp equivalence and the common operational local-step
  rule; Rust and Lean independently reject width mismatches and unsupported
  signed forms. `WgmmaDescriptorEncoding` proves correct packed-profile
  encoding/decoded bases for arbitrary supported aligned shared addresses.
  Existing opcode meanings and exact-real floating semantics are retained.
- Generated typing: the larger Hopper program exceeded the default recursion
  depth while checking types. Hopper emission now scopes an explicit depth
  allowance to its `decide` proof, and all nine prior Hopper generated files
  have the corresponding mechanically regenerated proof formatting. The
  kernel still checks every typing proof; no typing axiom, bypass or weakened
  predicate was introduced. Frontend emitted-proof assertions were updated
  for the Hopper format while preserving the existing Ampere expectations.
- Independent specification: `HopperDoubleBufferSpec` defines accumulation for
  arbitrary real tile families. `HopperDoubleBufferMatmul` proves it equals an
  ordinary matrix product summed over K=16*T, using logical full-matrix A/B
  indexing independent of the source. Concrete nonuniform mathematical
  three-tile examples give first element 20 and last element 29440. These
  are specification examples, not nonuniform PTX execution tests.
- Address/layout rules: `TmaPackedTiles.packed_tile_source_byte` proves a
  general packed-row tile-offset formula and is reused for A's eight-row and
  B's one-row tiles. Operand addresses come from independently decoded packed
  descriptors and reversible byte layouts. Both shared arenas are bounded,
  aligned and disjoint in the translated layout; A/B tensor reads are inside
  their corresponding logical allocations. Coordinate lemmas keep signed
  32-bit TMA indices in range under an explicit tile-count bound. This is not
  a full physical allocation/lifetime/runtime correspondence theorem.
- Phase rules: each buffer has its own use counter. `HopperDoubleBufferPhases`
  proves the selected stage, independent counter updates, expected parity and
  parity flip on reuse for arbitrary tile numbers, including parity wrap.
  `HopperDoubleBufferProtocol` proves arbitrary-length resource-local runs:
  initialize once; for each phase arrive with 2304 transaction bytes, complete
  2048 and 256 separately, allow all 128 acquiring waits, then invalidate.
  Missing either completion, using current/stale parity or restarting an
  unobserved phase is rejected. These reusable local rules do not yet match
  operations to every actual source/notification identity or construct a full
  admitted repeated-pipeline execution.
- Actual source probes: twelve checked runs cover T=0..5 in the producer and
  last-consumer lanes. The actual generated interpreter reaches exit with
  zero pending calls and the expected group/call counts. Metadata projections
  retain actual TMA destinations, tensor-map addresses, tile coordinates,
  mbarrier addresses/parities and native group completion. They check both
  first buffer reuses, parity wrap and producer prefetch/MMA/wait/refill order.
  Probes choose successful waits and represented zero tile inputs/replies.
  They do not assert full 128-thread launch consistency, arbitrary-T source
  correctness, actual shared-memory visibility or functional correctness.
- Remaining boundary: arbitrary-T all-thread source reconstruction, including
  finite unsuccessful waits; exhaustive source-matched resource histories;
  collective/control/tensor and RF/co/causal/coherence/observer admission for
  repeated writes; full-Pre universal correctness plus independent complete
  execution witnesses; allocation/in-flight lifetime/runtime/Iris connections;
  and review/extension of general output geometry against the paper. Existing
  one-phase proofs remain separate. No new unproved premise is used to label
  the repeated pipeline verified. Exact paper 81-form parity stays unconfirmed,
  and no IEEE, Hopper hardware, logits/token-equivalence or performance claim
  is added. The full original goal remains active.
- Validation: final full `scripts/check.sh` exits zero with 47 Rust tests,
  Clippy warnings denied, six rejection-harness integration tests, 30 generated
  AST comparisons, full Lean build (3425 jobs), 4370 audited declarations and
  339 individually evaluated false assertions. All 89 new authored public
  theorems have exact dependency audits; the resolved public inventory covers
  4339 names. Twelve new Lean modules are registered. The twenty new rejection
  assertions cover shift type/value/count boundaries, runtime descriptor bases,
  arena/stage/parity errors, missing notifications, premature phase restart and
  actual source group/pending metadata. No error/timeout is counted as a
  logical refutation. Inventory remains 12 capabilities/11 cases, with the
  required double-buffered case accurately marked partial.
- Check cost: new symbolic specification/address/phase/protocol/encoding leaves
  checked in about 1..2 seconds in individual builds; finite source and metadata
  probes took tens of seconds. A repeated-wait proof initially caused excessive
  definitional expansion; explicit rewrite/induction preserved all 128 waits and
  reduced the complete parameterized protocol leaf to about 1.8 seconds. The
  semantic extension required rebuilding earlier contracts; the existing
  WGMMA source and tensor-source leaves took 222 and 402 seconds in the full
  run. Both were confirmed live and allowed to finish, rather than restarted
  on an observation timeout. These are checker costs, not kernel speedups.
- Assembly evidence refreshed at 21:47:41 UTC; all 30 current source hashes
  match. GPU evidence remains at 07:46:53 UTC with all 15 source hashes matching.
  No new Hopper execution, physical byte comparison or runtime benchmark was
  performed; compilation/encoding/API correspondence remains an explicit boundary.
- Goal ledger snapshot at 21:48:37 UTC: 9,033,938 tokens versus the preceding
  published 8,476,551, a difference of 557,387. This is an interim usage snapshot,
  not final billed usage. The original unbounded goal remains active.

### 2026-11-05 — Parameterized execution of the double-buffer loop header

- Optimization instance: the actual 101-instruction two-stage TMA/WGMMA
  target. This step connects buffer selection, failed-wait retries and phase
  updates to the translated program; it does not change the kernel or add
  synchronization. Potential overlap and its performance cost remain unmeasured.
- Previous limitation: arbitrary-T phase equations and resource-local protocols
  were separate from source execution. The existing twelve finite probes chose
  successful waits and zero matrix replies. They could not establish that the
  actual control flow preserved accumulators and selected the correct buffer
  after an arbitrary finite unsuccessful-wait prefix.
- Reusable source rules: `Hopper/WgmmaInteger` lifts integer execution through
  the Scalar, Ampere, Hopper and WGMMA interpreters, retaining register-bank
  filtering, touched/dirty names and the explicit no-pending-call condition.
  Assignment, branch, comparison and one-bit subtraction rules use the fixed
  operational semantics. They do not assert memory visibility or arithmetic
  correctness from unconstrained replies.
- Source selection: `HopperDoubleBufferSelection.selection_execute` executes
  actual PCs 45..54 for every tile number and context, including both paths.
  Its postconditions identify the selected barrier, packed A/B descriptors,
  expected parity, and preserved registers/floats. Prologue register values are
  explicit entry assumptions, not a proved initial-state invariant yet.
- Waits: `HopperDoubleBufferWait.wait_test_execute` executes actual PCs 55/56
  for both Boolean answers. `arbitrary_failed_wait_prefix` proves any finite
  number of unsuccessful iterations, retaining each failure event and advancing
  the query counter from its actual prior value. Failure returns to PC 55;
  success reaches PC 57. This does not promise eventual progress or claim that
  prescribed oracle replies satisfy resource/graph admission.
- Phases: `HopperDoubleBufferPhaseStep.phase_update_execute` executes the
  actual branches and subtraction at PCs 57..60. Only the selected phase
  changes. The resulting counters equal `phaseZero (tile+1)` and
  `phaseOne (tile+1)`. The other phase and unrelated accumulators are preserved.
- Composition: `HopperDoubleBufferHeader.header_execute` executes PC 45 to
  PC 61 for arbitrary tile numbers, thread contexts and finite retry counts.
  It assumes the explicit loop-entry bindings, running PC, no pending call,
  the unsuccessful replies and one successful reply. Its exact source result
  includes those events; accompanying postconditions prove phase, query and
  frame properties. Arbitrary retained real accumulator values are preserved.
  This is a local loop-header rule, not a full iteration, complete launch,
  full-Pre correctness theorem or independent completed-launch witness.
- Validation: six new Lean modules and 75 authored public theorems, each with
  an exact dependency audit. Actual-source metadata tests cover both stage
  selections, first reuses, parity wrap, nonzero initial query count and finite
  failed-wait prefixes. Twelve additional individually checked false assertions
  catch wrong stage/parity, incorrect independent phase updates, missing failure
  events, wrong branch targets and dropped/reset query counts. Metadata checks
  use decidable Nat/Option/list/Bool projections; they do not decide equality of
  real-valued states or count type/import errors as logical rejection.
- Full gate `/tmp/ptx-double-buffer-header-gate.log` exited zero: 47 Rust tests,
  Clippy warnings denied, six rejection-harness integration tests, 30 generated
  AST comparisons, 3431 Lean build jobs, 4445 audited declarations, 4414 resolved
  public names covered and 351 rejected assertions. All 30 PTX examples assemble.
  Updated coverage metadata also validates as 12 capabilities and 11 cases;
  Hopper and the required double-buffer GEMM case remain partial. No new
  unproved assumption or weakened arithmetic/output contract was introduced.
- Evidence: assembly report refreshed at 22:10:25 UTC, with 30 current source
  hashes. GPU evidence remains at 07:46:53 UTC, 15/15 current source hashes and
  25 cases. No new Hopper GPU result, byte comparison, speedup, IEEE guarantee
  or logits/token-equivalence claim is added.
- Remaining: initial-state reconstruction and complete per-tile iteration
  (prefetch, MMA, committed completion, CTA rendezvous and loop advance), then
  arbitrary-T all-thread composition; source-matched repeated resource histories;
  coupled native control/tensor and byte RF/co/causal/coherence/observer admission;
  full-Pre correctness and independent compatible completion; allocation,
  in-flight lifetime, runtime and Iris correspondence; general output geometry
  review and exact paper 81-form inventory. This is source-proof engineering
  progress, not evidence of a new reusable concurrency proof method across
  distinct optimization mechanisms. The full original goal remains active.
- Goal ledger snapshot at 22:11:05 UTC: 9,170,886 tokens versus the preceding
  published 9,033,938, a difference of 136,948. This is an interim usage snapshot,
  not final billed usage or a completion report.

### 2026-11-05 — Native compute and bounded loop advancement

- Optimization instance: the same two-stage TMA/WGMMA K-loop. The PTX target
  is unchanged; no extra wait or CTA rendezvous is introduced in this step.
  Throughput, latency, memory use and actual prefetch overlap remain unmeasured.
- Previous limitation: the PC 45-to-61 header was connected to actual source,
  but next-tile/producer branching, native group completion and reuse-barrier
  advancement were still separate execution obligations. Finite whole-source
  probes did not establish arbitrary-state/history rules for these segments.
- `Hopper/WgmmaControl` adds source-derived bounded increment/comparison rules
  and lifts the existing CTA barrier through the WGMMA interpreter. It emits
  the actual arrival/return generation and explicitly preserves groups,
  completed count, call history and pending calls. A CTA barrier is not a
  native completion witness; participant matching remains graph admission.
- `HopperDoubleBufferPrefetchGuard.prefetch_guard_execute` proves actual
  PCs 61..64 for arbitrary contexts, bounded tile counters and an explicit
  producer-election register. Last-tile execution skips prefetch; otherwise
  only the producer reaches PC 65 and consumers reach PC 76. It constructs
  `%next`, retains the source query count and preserves unrelated registers
  and arbitrary real accumulators. Producer uniqueness is not assumed from an
  arbitrary context; it still needs the initial-state/loop invariant.
- `HopperDoubleBufferAdvance.advance_execute` proves actual PCs 80..84: the
  existing CTA rendezvous, stage toggle, tile increment, unsigned comparison
  and branch to PC 45 or 85. Tile/slot postconditions, barrier generation,
  query count and accumulator/register frames are checked. Bounds prevent
  interpreting a wrapping `.u32` increment as unbounded natural addition.
- `HopperDoubleBufferCompute.compute_execute` proves actual PCs 76..79 with
  arbitrary retained history, descriptors, available accumulator inputs and
  unconstrained arithmetic/completion replies. `compute_only_finishing` shows
  only this iteration's new call writes back when prior calls are not pending.
  `computeState_accumulators` identifies all four writes with the captured
  oracle results and removes their integer-bank entries. Wait-zero completes
  the committed group and leaves no pending call under the explicit ledger
  bounds; history is retained, rather than silently discarded or re-executed.
- `compute_and_advance_execute` composes the actual nine-instruction native
  block and loop tail for arbitrary contexts/history and bounded tile counts.
  This connects native completion to the existing reuse rendezvous and counter
  updates. It does not identify arithmetic replies with matrix multiplication
  or establish collective, proxy, resource or byte-level memory legality.
- Validation: five new Lean modules and 56 public theorems, each dependency
  audited. Actual-source checks exercise producer/consumer and final/nonfinal
  paths, stage toggles, barrier generations, preserved pending calls and a
  32-bit overflow boundary outside the theorem's precondition. A nonzero
  accumulator seed with three historical calls checks commit versus wait,
  retained history and the native-to-tail composition. Only closed decidable
  metadata is evaluated; structured native metadata has a derived decidable
  equality with Nat fields, without a real-valued state equality decider.
  Seventeen additional individually refuted assertions catch wrong producer
  paths, skipped synchronization/generations, premature completion, dropped
  history, incorrect query/group counts and out-of-bound successor reasoning.
- Full gate `/tmp/ptx-double-buffer-loop-body-gate.log` exited zero: 47 Rust
  tests, Clippy warnings denied, six rejection-harness integration tests,
  30 AST comparisons, 3436 Lean build jobs, 4501 audited declarations,
  4470 environment-resolved public names and 368 refuted assertions. All 30
  PTX examples assemble. Individual compute and execution-test leaves checked
  in 1.6 and 2.3 seconds in the observed builds; these are proof-check costs,
  not GPU speedups. Inventory remains 12 capabilities and 11 cases, with the
  required double-buffer case partial and exact paper 81-form parity unconfirmed.
- Assembly evidence refreshed at 22:28:27 UTC: 30/30 source hashes match.
  GPU evidence remains at 07:46:53 UTC: 15/15 hashes match, 25 cases, with no
  new Hopper GPU, IEEE or logits/token-equivalence claim. No new unproved
  assumption or weakened output contract is used to declare the case complete.
- Remaining: actual producer prefetch setup/transfers at PCs 65..75, initial
  prologue/output and arbitrary-T full-loop reconstruction; exhaustive
  source-matched resource histories; repeated native collective/control/tensor
  and RF/co/causal/coherence/observer admission; full-Pre correctness and an
  independent compatible completed-launch witness; allocation, in-flight
  lifetime, runtime/Iris correspondence and general output-geometry review.
  Reusing existing source rules in these segments is engineering progress,
  not evidence of a new concurrency method reused across distinct optimizations.
  The full original goal remains active.
- Goal ledger snapshot at 22:28:54 UTC: 9,239,991 tokens versus the preceding
  published 9,170,886, a difference of 69,105. This is interim usage, not final
  billed usage or a completion report.

### 2026-11-05 — Producer prefetch and a complete source iteration

- Optimization instance: the same double-buffer TMA/WGMMA loop. This step
  completes its producer source path and composes one real iteration. PTX and
  synchronization are unchanged; no throughput, latency or overlap result is added.
- Previous limitation: the source header and native-to-tail segments were
  proved separately. Producer address selection and TMA issues at PCs 65..75
  were missing, and a complete iteration could not yet restore the register,
  accumulator and pending/group invariants needed by the next iteration.
- Reusable source lifting: `Hopper/WgmmaTmaSteps` derives bounded constant
  multiplication, expectation and TMA issue from the fixed interpreters. It
  preserves real PC/query indices and records actual descriptor/payload replies.
  Issue consumes two queries, retains WGMMA accounting and does not prove bytes
  completed, proxy publication, memory contents or resource legality.
- Producer path: `HopperDoubleBufferPrefetchAddresses` proves actual PCs 65..72
  select the stage opposite the current MMA and compute A's next-tile coordinate.
  `PrefetchTransfer` proves actual PCs 73..75, including the 2304-byte expectation
  and separate A/B issues at q/q+2 with payload queries q+1/q+3. Descriptor
  addresses, views, coordinates, destinations, barrier and payload are retained
  for later admission. `Prefetch` composes the producer run through PC 76.
- All branches: `HopperDoubleBufferPrelude.prelude_execute` composes the
  next-tile/producer guard with the real producer path, or skips it for a
  consumer or final tile. All paths reach PC 76. Payload-length premises apply
  only when the source actually prefetches, so unused consumer/final-tile
  replies are not spuriously constrained. Current MMA operands and arbitrary
  real accumulators are preserved while preparing the other shared buffer.
- Accumulator availability: `HopperDoubleBufferAccumulators` describes typed
  floating values and absence of integer shadows. It proves the header/prelude
  preserve these values, and derives the real MMA register read from them plus
  no pending calls. Interpreter success is not an input hypothesis. Explicit
  accounting projections retain group/completion/call history through ordinary
  source steps; they do not assume earlier history came from a legal launch.
- Complete iteration: `HopperDoubleBufferIteration.iteration_execute` composes
  actual PC 45 through header, optional prefetch, native issue/commit/wait and
  reuse rendezvous/advance, ending at PC 45 or output entry PC 85. It supports
  arbitrary contexts, retained history, available real accumulators, bounded
  tile counters and any prescribed finite failed-wait prefix before success.
  Postconditions restore next-tile loop registers and accumulator availability,
  advance groups/completion, retain history and leave no pending native call.
  Query counts include failures, optional four-query prefetch and MMA/wait.
- Proof boundary: source register/bound/ledger/reply-shape conditions are
  explicit loop-entry assumptions. Arithmetic writes are the captured oracle
  results, not yet the independent GEMM specification. This is neither initial
  state reconstruction nor a legal whole-launch witness. Cross-lane collective,
  resource, descriptor/input-byte agreement, proxy and repeated-memory admission
  must independently constrain these replies before functional correctness.
- Validation: eight new Lean modules and 99 public theorems, with exact
  dependency audits. Actual-source metadata tests cover even/odd producers,
  consumers, first reuse, final/only tiles, finite failed waits, nonzero initial
  queries/accumulators and retained historical calls. They check opposite-buffer
  copies, A/B coordinate scaling, actual TMA queries, unchanged current MMA
  operands and group completion. Short A and oversized B payloads are rejected;
  malformed unused replies do not reject consumer/final-tile paths. Twenty new
  individually refuted assertions catch stage/coordinate/map/query errors,
  erased failures/history, premature loop reentry and invalid payload acceptance.
  Decidable checks use metadata/fault values, without real-state equality.
- Check cost: an initial accounting proof expanded nested states and exhausted
  its two-million-heartbeat limit. Explicit projection/frame rewrites replaced
  that definitional expansion without dropping fields or weakening the claim.
  The completed iteration leaf checked in 1.6 seconds and the finite source-test
  leaf in 12 seconds in the observed builds. These are proof-check costs only.
- Full gate `/tmp/ptx-double-buffer-iteration-gate.log` exited zero: 47 Rust
  tests, Clippy warnings denied, six rejection-harness integration tests,
  30 AST comparisons, 3444 Lean build jobs, 4600 audited declarations,
  4569 resolved public names and 388 refuted assertions. All 30 PTX examples
  assemble. Inventory remains 12 capabilities/11 cases; Hopper and the required
  double-buffer case remain partial, and exact paper 81-form parity unconfirmed.
- Evidence: assembly report refreshed at 22:51:17 UTC, 30/30 current source
  hashes. GPU evidence remains at 07:46:53 UTC, 15/15 hashes and 25 cases, with
  no new Hopper execution, IEEE, logits/token-equivalence or performance claim.
  No unproved axiom, assumed execute result or weakened output target was added.
- Remaining: kernel prologue/output and arbitrary-T all-thread full-loop source
  reconstruction; source-matched repeated resource histories; collective/control/
  tensor and RF/co/causal/coherence/observer admission; full-Pre functional
  correctness and independent compatible completed-launch witnesses; allocation,
  in-flight lifetime, runtime/Iris connections and general output geometry.
  These source rules reuse existing semantics and are engineering progress,
  not evidence of a new concurrency method across distinct optimizations.
  The full original goal remains active.
- Goal ledger snapshot at 22:51:34 UTC: 9,315,582 tokens versus the preceding
  published 9,239,991, a difference of 75,591. This is an interim usage snapshot,
  not final billed usage or a completion report.

### 2026-11-05 — Arbitrary loops and reconstructed kernel entry

- Optimization instance: the same two-buffer TMA/WGMMA loop, unchanged PTX
  and synchronization. This step extends a single checked iteration to arbitrary
  bounded source loops and connects a represented-zero-input instance to the
  real kernel entry. No performance or physical GPU result is introduced.
- Previous limitation: a complete iteration restored its invariants, but no
  arbitrary-length source composition or initial-state reconstruction established
  a kernel run beyond the finite probes. Iteration success alone was not an
  initial-kernel or completed-launch witness.
- `HopperDoubleBufferLoop.loop_execute` composes arbitrary finite iteration
  counts from an explicit loop invariant. Each tile may prescribe a different
  finite retry count. Reply conditions use an independently defined query
  schedule, not an assumed interpreter result. The proof tracks exact source
  fuel/events, running PC, available accumulators, restored loop registers,
  pending calls, completion, retained call count and unchanged control registers.
- `LoopSchedule` proves strictly increasing query starts, disjoint wait-query
  intervals, total retry accounting and prefetch counts. For a complete loop,
  the producer prefetches all but the last tile; consumers do not prefetch.
  This origin separation does not itself prove transfer visibility or resource
  admissibility. It is available for later source/notification matching.
- `HopperDoubleBufferContext` now owns the unchanged launch context and
  represented-zero-input replies, shared by generic proofs and finite probes.
  `oracle_payload_shape` proves the descriptor/payload length condition at every
  query. `LoopWitness` applies it to a constructed arbitrary-length source run
  with successful waits. This is source nonvacuity from a loop checkpoint,
  not a resource/memory-admitted completed launch or arbitrary-input correctness.
- `Entry` proves the actual first 28 instructions, including all parameter
  reads, runtime shared-address descriptor construction and accumulator zeroing.
  The producer flag is derived from three-dimensional launch coordinates and
  is true only for lane zero. `Initialization` reconstructs both barrier
  initializations, proxy fence, CTA rendezvous, zero-tile guard, initial A/B
  copies and loop register initialization. No intermediate run is assumed.
- `KernelLoop.kernel_loop_source` connects entry and the arbitrary loop for
  every lane and 0<T<=2^28, from empty state to output entry PC 85. It derives
  typed initial loop registers and zero accumulators; the source output state
  has T committed/completed groups, T retained calls, no pending native work,
  preserved output/coordinate/control registers and represented zero accumulators.
  The zero-tile source branch reaches PC 85 separately without TMA or MMA.
  PC 85 is still running: output stores, invalidation and return are not proved
  by this theorem. Explicit chosen replies are not identified with arbitrary
  launch memory, and collective/resource/memory admission remains separate.
- Validation: nine new Lean modules and 74 public theorems, each dependency
  audited. Six- and seven-tile actual loop examples exercise both stage reuses,
  parity wrap and retained prefetch queries. From-empty-state six-tile examples
  cover producer, last lane and an interior lane, plus both zero-tile branches.
  Independent schedule checks cover varying retries. Twenty new individually
  refuted assertions catch dropped initial transfers, wrong producer election,
  stale counters/coordinates/parity, discarded history, wrong query totals,
  extra final-tile prefetch and confusion between output entry and return.
  All evaluated checks compare closed decidable metadata/fuel/query values.
- Check cost: a monolithic first-28-instruction `rfl` proof exhausted its
  four-million-heartbeat limit. Splitting parameter reads, four descriptor
  constructions and zeroing into checked source segments reduced the successful
  entry leaf to 2.4 seconds, without weakening its statement or trust boundary.
  Initialization checked in 14 seconds; the final kernel-loop proof leaf in
  1.8 seconds; from-empty-state finite examples in 17 seconds in observed builds.
  These are checker costs, not kernel speedups.
- Full gate `/tmp/ptx-double-buffer-kernel-loop-gate.log` exited zero: 47 Rust
  tests, Clippy warnings denied, six rejection-harness integration tests,
  30 AST comparisons, 3453 Lean build jobs, 4674 audited declarations,
  4643 environment-resolved public names and 408 refuted assertions. All 30
  PTX examples assemble. Coverage metadata remains 12 capabilities/11 cases;
  Hopper and the required double-buffer case remain partial, with exact paper
  81-form parity unconfirmed. No assumed execute result or unproved axiom is added.
- Evidence: assembly refreshed at 23:13:36 UTC, 30/30 source hashes current.
  GPU evidence remains at 07:46:53 UTC, 15/15 hashes current and 25 cases, with
  no new Hopper execution, IEEE, logits/token-equivalence or speedup claim.
- Remaining: actual output address calculation, stores, barrier invalidation
  and return; general nonzero-input kernel witnesses and functional refinement;
  repeated source-matched resource histories; native collective/control/tensor
  and RF/co/causal/coherence/observer admission; independent compatible completed
  launch witnesses; allocation, in-flight lifetime, runtime/Iris correspondence
  and general output geometry review. Existing semantic rules are reused here;
  this is engineering progress, not a new concurrency method demonstrated across
  different optimizations. The full original goal remains active.
- Goal ledger snapshot at 23:14:08 UTC: 9,389,207 tokens versus the preceding
  published 9,315,582, a difference of 73,625. This is interim usage, not final
  billed usage or a completion report.

### 2026-11-05 — Complete returned source and output-byte inventory

- Optimization instance: the same double-buffer TMA/WGMMA target. This step
  connects output and return to the constructed source candidate; PTX and
  synchronization are unchanged. No new performance or physical GPU result.
- Previous limitation: the reconstructed kernel reached PC 85 with no pending
  native call, but was still running. Address calculation, four stores, final
  barrier/invalidation and return were unconnected to this parametric witness.
- Source lifting: `Hopper/WgmmaOutputSteps` derives typed floating stores,
  invalidation and return through the fixed Scalar/Ampere/Hopper/WGMMA layers.
  Stores emit the actual typed byte list at the resolved address. Invalidation
  emits a resource event; it does not assume resource legality. Return marks
  the local source state done, retaining the explicit no-pending obligation.
- Output suffix: `HopperDoubleBufferOutputAddresses` proves actual PCs 85..91
  for arbitrary completed-loop states with the physical-lane coordinate registers.
  `OutputStores` proves actual PCs 92..95 for arbitrary available typed real
  accumulators. Existing checked C-layout lemmas identify row/column addresses
  and byte bounds. `Return` proves actual PCs 96..100: final CTA arrival/return,
  producer-only invalidation of both barriers, and ret. `Output` composes all
  suffix segments and preserves queries/group/completion/call accounting.
- Complete candidate: `KernelSource.complete_source_run` connects empty-state
  entry, arbitrary-length represented-zero-input loop (or T=0 branch) and output
  suffix for every lane and T<=2^28. `complete_source_status` proves local done
  and no pending WGMMA; every source event has a located-run correspondence.
  `complete_source_well_formed` proves launch geometry, unique source thread IDs,
  full thread coverage and actual source production for the 128-thread candidate.
  These source predicates do not admit resource/tensor/memory graphs or identify
  chosen replies with arbitrary launch memory. In particular they are not the
  goal's independently proved compatible completed-launch witness yet.
- Global writes: `WriteInventory` proves that initialization, TMA issue, the
  loop and return contain no ordinary global-write events. The complete source
  therefore has exactly four f32 ordinary writes per lane, with actual byte
  values from the chosen represented-zero-input suffix. The address formula
  bounds all words in [8192,10240); output-byte ownership is injective across
  lanes/slots/indices and covers all 2048 C bytes. This is an exact source-write
  inventory, not coherence, observer/final-heap correctness or IEEE bit encoding.
  Native/TMA memory effects still require their separate graph expansion/admission.
- Validation: eight new Lean modules and 84 public theorems, dependency audited.
  Complete actual-source runs cover producer, last lane, interior lane and both
  zero-tile paths. Checks retain done/PC, native groups/completion/history, both
  producer invalidations, four addresses/word widths, typed f32 byte indices,
  first/last C bytes and exact instruction fuel. Twenty additional individually
  refuted assertions catch incomplete return, missing invalidation, wrong row
  stride/addresses/widths, output aliasing, discarded history, extra query use
  and confusion between symbolic real fragments and physical bit bytes. No
  equality decider over real-valued states is used; no error or timeout is
  counted as logical refutation.
- Full gate `/tmp/ptx-double-buffer-complete-source-gate.log` exited zero:
  47 Rust tests, Clippy warnings denied, six rejection-harness integration tests,
  30 AST comparisons, 3461 Lean build jobs, 4758 audited declarations,
  4727 resolved public names and 428 refuted assertions. All 30 PTX examples
  assemble. The output composition checked in 2.8 seconds, complete candidate
  leaf in 5 seconds, byte inventory in 1.3 seconds and finite full-source tests
  in 26..28 seconds in observed builds. These are checker costs, not speedups.
  The rejection process was confirmed live and polled to exit zero.
- Coverage metadata remains 12 capabilities/11 cases, with Hopper and the
  required double-buffer case partial. Exact paper 81-form parity is unconfirmed.
  Assembly refreshed at 23:32:29 UTC, 30/30 source hashes current. GPU evidence
  remains at 07:46:53 UTC, 15/15 hashes and 25 cases, with no new Hopper execution,
  IEEE, logits/token-equivalence or performance claim. No unproved axiom or
  assumed execute result is introduced.
- Remaining: general nonzero-input kernel witnesses and functional refinement;
  repeated source-matched TMA/mbarrier histories; native collective/control/tensor
  and byte RF/co/causal/coherence/observer admission; independent compatible
  completed-launch witnesses and full-Pre correctness; allocation, in-flight
  lifetime, runtime/Iris correspondence and general output geometry. Reusing
  source/byte-layout rules here is engineering progress, not a new concurrency
  method reused across distinct optimizations. The full original goal stays active.
- Goal ledger snapshot at 23:33:06 UTC: 9,457,941 tokens versus the preceding
  published 9,389,207, a difference of 68,734. This is interim usage, not final
  billed usage or a completion report.

### 2026-11-05 — Arbitrary-real data source and captured-call tensor component

- Optimization instance: the same double-buffer TMA/WGMMA target, unchanged
  PTX and synchronization. The prior complete witness used only zero inputs;
  it could not exercise accumulation, data-tile origin or a general nonzero
  input-memory layout. No performance or physical GPU claim is added here.
- Query origin: `ReplyQueries` derives native-query indices from the actual
  successful-wait source schedule and proves their inversion/uniqueness. The
  producer's final MMA has a different query offset because it no longer
  prefetches; consumers have their own stride. Initial and next-tile A/B TMA
  payload indices are derived separately, including both buffer-reuse paths.
- Constructed replies: `DataOracle` accepts arbitrary real A/B tile families.
  Its matrix replies compute the fixed `Wgmma.results` operation from the prior
  independent accumulation, and source input consistency is proved later; no
  desired execution result is a premise. TMA payloads and native operand bytes
  carry the selected input tile. Every source payload shape and supported
  positive descriptor profile is proved, with explicit query/tile origin lemmas.
- Input layout: fixed A=65536/B=131072 modeled bases overlap beyond 32 A tiles.
  The old zero-input source family is preserved. The new arbitrary-data family
  uses modeled B base 65536+2048*T, with disjoint A/B regions, alignment and
  64-bit address-bound proofs under the existing tile bound. This supports a
  later coherent arbitrary-input heap construction without shrinking T's range;
  it is not a GPU allocation or CUDA tensor-map encoding correspondence theorem.
- Source construction: `DataEntry` proves oracle-independent pre-query entry
  segments and arbitrary tile-zero initial copies. `DataLoop` applies the
  existing actual-iteration/loop rules and derives typed accumulator contents
  at every checkpoint. `DataSource` connects empty state through return for
  all lanes and supported T, including T=0, retaining source coverage and local
  completion. Its ordinary symbolic output writes match the independent tiled
  specification and ordinary K=16*T matmul. These are the constructed source
  witness's writes, not universal correctness over admitted executions or an
  observer/final-heap theorem.
- Captured calls: `DataCalls` proves the actual emitted MMA call is present in
  the complete source trace, has the correct lane/group/ordinal/descriptors,
  reads the prior checkpoint accumulation and captures the current tile's
  operand bytes and arithmetic result. Cohort and `Wgmma.Arithmetic` properties
  are proved from these fields. Thus instruction arithmetic of chosen replies
  is checked against source-captured inputs, rather than silently assumed.
- Tensor boundary: `DataTensor` constructs `Wgmma.TensorConditions` for those
  calls over an explicit logical per-tile shared view and proves the matrix
  step. It does not identify that view with completed/published TMA bytes or
  a source-matched repeated RF/co history. Actual collective source IDs/control,
  resource completion, visibility, memory/observer and runtime admission remain
  required before full functional correctness or legal nonvacuity is established.
- Validation: eight new Lean modules and 93 dependency-audited public theorems.
  Nonuniform three-tile complete-source metadata tests retain source completion,
  histories and dynamic TMA origins. Formal symbolic-write tests connect actual
  source execution to first/last values 20 and 29440; a captured final call has
  input 8 and output 20. Separate proved arithmetic negations reject a zero
  final reply and resetting the prior accumulator. They use checked real
  arithmetic proofs, not a real-state equality decider. Twenty new strict
  decidable refutations cover wrong final/consumer queries, stale payload tiles,
  old overlapping B placement, wrong descriptor origins, pending/history and
  captured group/query errors. No error/timeout counts as a logical rejection.
- Full gate `/tmp/ptx-double-buffer-real-data-gate.log` exited zero: 47 Rust
  tests, Clippy warnings denied, six rejection-harness integration tests,
  30 AST comparisons, 3469 Lean build jobs, 4851 audited declarations,
  4820 resolved public names and 448 individually refuted assertions. All 30
  PTX examples assemble. Observed leaves checked in 2.3 seconds for replies,
  15 seconds for data entry, 1.2 seconds for the loop, 5.2 seconds for complete
  source, 1 second for calls, 1.2 seconds for the tensor component and 10 seconds
  for examples. These are proof-check costs, not kernel speedups.
- Coverage remains 12 capabilities/11 cases. Hopper and the double-buffer
  acceptance case remain partial; exact paper 81-form parity is unconfirmed.
  Assembly refreshed at 23:57:46 UTC, 30/30 current source hashes. GPU evidence
  remains at 07:46:53 UTC, 15/15 current hashes and 25 cases, with no new Hopper,
  IEEE, logits/token-equivalence or speedup evidence. No unproved axiom,
  assumed successful execute result or weakened output target is added.
- Remaining: identify logical tile views with the launch's packed inputs and
  actual TMA writes; repeated source-matched mbarrier/TMA histories; collective
  source-ID/control matching; native byte RF/co/causal/coherence/observer admission;
  full-Pre functional refinement for admitted executions and independently
  compatible completed-launch witnesses; allocation/in-flight lifetime,
  runtime/Iris correspondence and general output geometry. This is source/tensor
  engineering using existing rules, not a new concurrency method demonstrated
  across distinct optimization mechanisms. The original goal remains active.
- Goal ledger snapshot at 23:58:10 UTC: 9,537,860 tokens versus the preceding
  published 9,457,941, a difference of 79,919. This is interim usage, not final
  billed usage or a completion report.


### 2026-11-06 — Per-tile source identities, collectives and TMA input bytes

- Instance: the actual 101-instruction double-buffer GEMM, with arbitrary real
  tile inputs, `0<T<=2^28`, all 128 lanes and the constructed source family with
  first-attempt successful waits. Existing loop proofs still support finite
  failed-wait prefixes; the closed event indices here describe this chosen
  completion witness, not every admitted execution.
- Concrete gap: call membership and a shifted logical shared view did not
  identify each repeated MMA/TMA/wait by its actual source event. A reused slot
  alone cannot identify which transfer supplied its current tile. The previous
  one-stage components did not provide these repeated source identities.
- `HopperDoubleBufferEventIndices` proves prefix lengths, precise MMA and
  acquiring-wait lookups, and retention through the complete trace. Before tile
  `n<T`, producer/peer starts are `8+10*n` / `2+7*n`; producer MMA indices are
  `13+10*n` before the final tile and `10+10*n` at the final tile, while peer
  MMA indices are `4+7*n`. Omitting the final prefetch changes the event index.
- `DataCollective` constructs `Unified.Collective` for every actual tile using
  the captured calls and exact source IDs. All 128 lanes match PC 77, native
  synchronization sequence `4*n+1`, descriptors, ordinal and group. Lane IDs are
  distinct, and equal per-lane MMA IDs imply equal tile numbers. The generic
  ledger synchronization-count lemma also allows arbitrary finite retries.
  This record does not establish the complete fence/commit/wait native-control
  admission for the repeated launch.
- `TmaSources` identifies initial A/B issues at indices 6/7 and later issues
  at the previous tile's start plus 2/3. Expectations are at 5 or previous
  start plus 1. Actual descriptors, coordinates, queries, alternating slots,
  2304-byte expectations and implicit 2048/256-byte notifications are retained.
  Implicit write locations/bytes match the logical shared view, and every actual
  captured native operand byte matches its tile's implicit TMA write at the
  same shared location. This proves matching operation nodes and values; it
  does not prove execution order, completion, visibility or safe overwrite.
- `TmaInputs` independently represents the packed global tile arrays and both
  stored tensor maps, with B starting after A. A reusable packed-slice address
  lemma derives actual source byte addresses. The identified copies read A at
  `65536+2048*n+offset` and B at `dataBBase(T)+256*n+offset`; their payloads
  agree with this initial memory. These are per-identified-copy facts, not yet
  an exhaustive launch-wide descriptor/payload inventory or memory admission.
- Reuse evidence: the same source-index and packed-slice rules handle both
  buffer slots, arbitrarily many rounds and both 2048-byte A / 256-byte B
  transfers. This is engineering composition of the existing semantics, not
  evidence of a new general concurrency proof method across distinct optimization
  mechanisms. No performance experiment or new synchronization rule is claimed.
- Validation: five new Lean modules, 73 audited public theorems (including 23
  concrete metadata tests), and 18 new strict decidable false assertions.
  Three- and five-tile tests inspect actual rich source-event projections,
  covering both slots, first/second reuse, producer/peer indices, final prefetch
  omission, retained mark/group history, copy coordinates, parity and zero tiles.
  Strict refutations reject wrong indices, stale group/sequence, slot/stride/
  byte-count mistakes, old parity and conflating repeated copy identities.
  They compare Nat/Int/Bool/ID metadata, without a real-state equality decider.
  Import/type/proof-timeout failures never count as semantic refutations.
- Full gate `/tmp/ptx-double-buffer-source-indices-gate.log` exited zero:
  47 Rust tests, Clippy warnings denied, six rejection-harness integration tests,
  30 generated AST comparisons, 3474 Lean jobs, 4924 audited declarations,
  4893 environment-resolved public names and 466 individually refuted assertions.
  All 30 PTX examples assemble. New input-address checking took 1.6 seconds and
  concrete metadata checking 2.0 seconds in the recorded build; these are proof
  costs, not GPU timings. Coverage metadata validation also passed after updates.
- Assembly evidence refreshed at 2026-11-06 00:18:09 UTC, 30/30 current hashes.
  Existing GPU evidence remains at 2026-11-05 07:46:53 UTC, 15/15 current hashes,
  25 cases (24 exact-byte results and one completion-only result) on sm_89.
  No Hopper GPU, IEEE-level, logits/token-equivalence or speedup result is added.
- Remaining: exhaustive source resource inventories and repeated mbarrier/TMA
  histories; native-control and coupled RF/co/causality/coherence/observer
  admission; full-Pre functional refinement for arbitrary admitted executions
  and a compatible completed-launch witness; allocation/in-flight lifetime,
  runtime/Iris correspondence and general output geometry. The original goal
  remains active at its original scope. Hopper and the double-buffer case are
  partial, and exact paper 81-form parity remains unconfirmed. No unproved axiom,
  assumed successful source execution or weakened output target was introduced.
- Goal ledger snapshot at 2026-11-06 00:18:40 UTC: 9,658,868 tokens versus the
  preceding published 9,537,860, a difference of 121,008. This is interim
  tool-reported usage, not final billed usage or a goal-completion report.


### 2026-11-06 — Repeated source-sound resource histories and phase observations

- Instance: the same actual double-buffer GEMM with arbitrary real tile inputs,
  both shared stage slots, `T<=2^28`, and all 128 lanes of the constructed
  first-attempt-successful-wait source family. The zero-tile path is included.
  Generic loop support for finite unsuccessful waits remains separate from this
  particular history construction.
- Concrete gap: actual source IDs and matching operand/TMA bytes did not yet
  give repeated resource histories or show which transfer phase a successful
  wait observed. Stage-slot equality and equal parity bits cannot identify a
  current completion after repeated reuse and parity wrap.
- `HopperDoubleBufferResourceEndpoints` identifies both initializations and
  final invalidations in the complete source trace, including zero tiles, and
  supplies source-backed wait/resource lookups. `stageTile(slot,phase)` is proved
  to select that slot, use the expected parity and be in range exactly when the
  phase is below that slot's use count.
- `ResourceHistory` constructs each slot's init, repeated expectation/A-notice/
  B-notice/128-wait phases, and invalidation with actual source and implicit TMA
  notification identities. Every entry is proved to be in the actual resource
  inventory for bounded supported T. Its projected operations equal the earlier
  arbitrary-length protocol and run to `some none` (valid invalidation), including
  unused stages at T=0. Each phase has 131 entries; a history has
  `2+131*uses(T,slot)` entries. Inventory inclusion is one-way and is not an
  exhaustive inventory proof.
- `ResourcePrefixes` proves exact phase cuts and notification/wait positions in
  the constructed histories. Before phase p the protocol is `readyState p`;
  before the first wait it has completed phase p, and subsequent waits preserve
  that completed phase. Positions here index resource histories, distinct from
  source-event serials. Prefix arithmetic is proved structurally for arbitrary
  use counts; no successful protocol result is assumed as a precondition.
- `ResourceObservations` derives lifetime/absolute-phase stamps: both notices
  are stamped `(1,p)` and every corresponding lane wait `(1,p+1)`. Checked
  `Tma.observation` links every current A/B notice to each actual source wait.
  Notices from any different phase are rejected, for both A and B, even if the
  parity bit has wrapped back to the same value. Slot reuse does not initialize
  a new lifetime. These are computed observations in the source-sound constructed
  history, not a universal theorem about arbitrary admitted GPU executions.
- Method/reuse: the existing resource protocol and observation rules now compose
  with actual repeated source identities for both slots, all phases and both
  transfer sizes. No new unproved concurrency rule was added. This is engineering
  progress toward the required pipeline witness, not a demonstrated new general
  ownership/synchronization method across distinct optimizations. No performance
  gain or proof of safe shared-memory overwrite is claimed.
- Validation: five new Lean modules, 481 source lines and 70 audited public
  theorems, including 25 concrete tests. Zero-/three-/five-tile tests check source
  endpoint IDs, protocol completion, both stage histories, current A/B notices,
  all-lane boundary positions, first/second reuse, lifetime and absolute phases.
  Twenty new strict decidable refutations reject stale/future notices, parity-wrap
  revival, confusing arrivals with completion notices or waits, wrong source IDs,
  dropped phases and lifetime/phase resets. These compare only metadata/protocol
  values; no equality decider on real-valued states is installed. Import, type,
  syntax and timeout errors are not accepted as refutations.
- Full gate `/tmp/ptx-double-buffer-resource-history-gate.log` exited zero:
  47 Rust tests, Clippy warnings denied, six rejection-harness integration tests,
  30 generated AST comparisons, 3479 Lean jobs, 4994 audited declarations,
  4963 environment-resolved public names and 486 individually refuted assertions.
  All 30 PTX examples assemble. The observation module checked in 1.5 seconds
  and the concrete resource tests in 2.8 seconds in that build; these are proof
  checking times, not GPU measurements. Updated coverage metadata also validates.
- Assembly refreshed at 2026-11-06 00:35:28 UTC with 30/30 current source hashes.
  Existing GPU evidence remains at 2026-11-05 07:46:53 UTC, 15/15 current hashes
  and 25 cases (24 exact-byte results and one completion-only result) on sm_89.
  No new Hopper execution, IEEE/logits/token-equivalence or speedup evidence.
- Remaining: the constructed histories need origin uniqueness, exhaustive actual
  inventory coverage and source-order proofs before satisfying `Tma.HistoryValid`.
  Protocol success and one-way entry soundness do not imply these fields.
  Native-control, coupled RF/co/causality/coherence/observer admission, full-Pre
  correctness for arbitrary admitted executions and a compatible completed-launch
  witness, allocation/in-flight lifetime, runtime/Iris correspondence and general
  output geometry remain. The original goal stays active with its full scope;
  Hopper/double-buffer are partial and exact paper 81-form parity is unconfirmed.
  No unproved axiom or weakened exact-output target is introduced.
- Goal ledger snapshot at 2026-11-06 00:35:40 UTC: 9,730,205 tokens versus the
  preceding published 9,658,868, a difference of 71,337. Interim tool-reported
  usage, not final billed usage or a goal-completion report.


### 2026-11-06 — Resource origin uniqueness and thread-local source order

- Instance: the actual double-buffer GEMM's constructed source-matched histories
  for arbitrary real tile inputs, both stage slots and arbitrary use counts.
  Source execution still has the existing `T<=2^28` bound; these history-index
  identities hold for the constructed lists even without that bound. No new
  universal claim about all admitted executions is made.
- Concrete gap: protocol execution, one-way inventory inclusion and phase
  observation did not rule out duplicate source/notification identities or
  histories that invert thread-local source order. These are required fields
  of `Tma.HistoryValid`, independent of local protocol success.
- `HopperDoubleBufferResourceSerials` proves closed source serials equal the
  source-derived indices. Producer/peer wait serials are `8+10*tile` and
  `2+7*tile`; later expectation/A/B serials are `10*tile-1`, `10*tile` and
  `10*tile+1`, with separately checked initial values 5/6/7. Final invalidation
  serials are `10*T+11+slot`. The complete-loop and producer-prefix event lengths
  are proved, rather than assumed for the final source indices. Thread-coordinate
  linearization recovers lane identity.
- `ResourceRanks` recovers a local history position from each actual source or
  notification origin, including reused slots and the producer/peer stride
  difference. It is proved on the valid constructed origins, not offered as an
  admission checker for arbitrary fabricated origins. `ResourceUnique` proves
  that the mapped positions are exactly the consecutive range of history
  indices. Thus every history's origin list is duplicate-free, and `idxOf` and
  recovered positions agree with actual lookups.
- `ResourceSourceOrder` classifies source members as initialization, a bounded
  phase expectation/wait, or invalidation. Same-thread increasing source serials
  imply increasing local history positions. This proves `Tma.SourceOrder` for
  every constructed history, including unused stages at T=0. Existing checked
  phase observations and origin uniqueness also give each current A/B
  notification's local `Tma.Before` relation to every corresponding lane wait.
  This relation is not a GPU happens-before or memory-visibility theorem.
- Reusable rule: `Tma.observation_before_of_unique` factors the existing checked
  index argument through precisely origin uniqueness. The original
  `observation_before(HistoryValid, observation)` interface remains intact and
  delegates to it. No caller-facing admission target is weakened, and no new
  axiom or assumed successful execution is introduced. The same local argument
  covers all phases, slots and lanes; this is engineering reuse of existing
  semantics, not a new concurrency method demonstrated on distinct optimizations.
- Boundary counterexample: removing the actual final invalidation at T=0 leaves
  uniqueness, source order and an admitted local protocol prefix intact. A formal
  negation theorem still rejects `HistoryValid`: its exhaustive inventory field
  would have to include the actual omitted invalidation. Thus the completed
  fields do not imply inventory exhaustion or full admission.
- Validation: five new Lean modules and one refactored core rule, with 64 newly
  audited public theorems, including 19 test theorems. Metadata examples cover
  zero-/three-/five-tile histories, both slots, producer/peer strides, initial and
  final serials, reused notification ranks and last-peer positions. Corrupted
  histories reject duplicated initialization/source identity and inverted source
  order. Eighteen new strict decidable refutations reject stale ranks, conflated
  copy IDs, wrong stride/endpoint serials, reversed source order and the claim
  that omitting invalidation is exhaustive. The separate omitted-invalidation
  `HistoryValid` negation is a checked proof, not counted as a `by decide`
  assertion over that record. No real-state equality decision procedure is used.
- Full gate `/tmp/ptx-double-buffer-resource-order-gate.log` exited zero: 47 Rust
  tests, Clippy warnings denied, six rejection-harness integration tests, 30 AST
  comparisons, 3484 Lean build jobs, 5058 audited declarations, 5027 resolved
  public names and 504 individually refuted assertions. All 30 PTX examples
  assemble. Targeted source-order checking took approximately 10 seconds and
  the new test module 1.8 seconds; these are proof costs, not GPU timings. The
  core-rule refactor also triggered rechecking the existing Hopper dependents.
  Updated coverage metadata validates and touched tracked files pass whitespace
  checks.
- Assembly evidence refreshed at 2026-11-06 02:18:09 UTC, 30/30 current hashes.
  Existing GPU evidence remains at 2026-11-05 07:46:53 UTC, 15/15 current hashes,
  25 sm_89 cases (24 exact-byte and one completion-only). No new Hopper GPU,
  IEEE/logits/token-equivalence or performance result. A transient automatic
  approval quota failure prevented an earlier read; the ordinary approval path
  succeeded again at 01:51:09 UTC without bypassing the check.
- Remaining: exhaustive coverage of the actual resource inventory is the last
  unproved `HistoryValid` field for these lists. Next derive reverse inventory
  inclusion from indexed source barrier/TMA cases through initialization, loop
  and return, account for actual inventory uniqueness and outside-gate emptiness,
  and construct the full history records. Combined control acyclicity, remaining
  native control, RF/co/causality/coherence/observer admission, full-Pre functional
  refinement and independently compatible completion, allocation/in-flight
  lifetime, runtime/Iris correspondence and general output geometry remain.
  Original scope stays active; Hopper/double-buffer remain partial and exact
  paper 81-form parity is unconfirmed. The exact-output target is unchanged.
- Goal ledger snapshot at 2026-11-06 02:18:25 UTC: 9,807,782 tokens versus the
  preceding published 9,730,205, a difference of 77,577. Interim tool-reported
  usage, not final billed usage or a goal-completion report.


### 2026-11-06 — Exhaustive actual resource inventories and admitted histories

- Instance: the actual double-buffer GEMM's constructed source witness with
  arbitrary real tile inputs, both stages, all 128 lanes and `T<=2^28`, including
  zero tiles. Source/resource witness construction remains distinct from
  universal correctness for arbitrary admitted executions.
- Concrete gap: the constructed histories were unique, source ordered and
  protocol-correct, and every listed entry had an actual origin, but the reverse
  inclusion was missing. Those facts could omit a real resource operation or
  notification. The previous checked missing-invalidation counterexample exposed
  precisely this gap; no history record or full admission was assumed to close it.
- Generic `TmaInventoryUnique` proves that unique trace IDs give unique event
  indices and tagged resource origins, and hence duplicate-free inventories.
  It preserves actual origin identities through the source/notification filters;
  it does not assume a kernel's proposed history or protocol is valid.
- `HopperDoubleBufferResourceCases` classifies each actual loop iteration's
  resource positions. `ResourceTraceCases` extends indexed classification through
  initialization, arbitrary loop prefixes and the output/return suffix. Every
  actual rich source resource event is one of the two initializations, a bounded
  tile expectation/wait/A-copy/B-copy, or a final invalidation. Copies retain
  actual source IDs and normalized descriptors/coordinates/payloads. CTA and
  native fence events are correctly excluded from the mbarrier inventory.
- `ResourceMembership` proves that every classified actual resource origin is
  in its stage history. `ResourceAdmission` combines reverse inclusion, previous
  soundness and uniqueness into exact inventory permutations and constructs
  `Tma.HistoryValid` for each stage. Inventories at every other location are empty,
  including non-gate shared data addresses and other CTAs. `dataHistories` now
  has valid records for every location. Actual inventory lengths equal
  `2+131*uses(T,slot)`. Current notification/wait phase observations can now use
  the core actual-phase theorem with a complete history record.
- `TmaAgreement` classifies all actual TMA copies, rather than only proving facts
  about selected identified copies. All have descriptor agreement with `dataMaps`,
  initial payload agreement with independently represented packed tile storage,
  and symbolic tensor-map storage provenance. This closes the prior exhaustive
  descriptor/payload inventory gap. Combined control acyclicity remains required
  before `Unified.TmaComponents` is complete; history validity does not imply
  control, shared-memory RF/coherence, native eligibility or observer admission.
- Reuse/method: generic event/resource uniqueness and indexed local-to-complete
  source classification apply across both buffer slots, all rounds, both transfer
  sizes and zero/unused stages. These are proved compositions of existing
  semantics, not a newly assumed rule or a demonstrated new general ownership
  method across distinct optimizations. No speedup or safe-overwrite claim.
- Validation: seven new Lean modules, 58 audited public theorems, including 19
  test theorems. Parameterized tests expose valid histories for every location;
  zero-/three-/five-tile instances check unused gates, actual inventory lengths
  and empty outside-gate inventories. Removing an A completion notification is
  formally rejected by `HistoryValid`. Inserting a virtual zero-byte completion
  after initialization passes the local protocol but has no actual TMA source
  and is also formally rejected by `HistoryValid`. These two record negations
  are checked proofs, separate from strict decidable refutation counts.
- Sixteen new strict decidable false assertions reject dropped/extra entries,
  wrong retained origins, missing-notice protocol success, treating local ghost
  protocol failure as sufficient, invented outside-gate histories, confusing CTA/
  proxy/native fences with mbarrier resources, ignored TMA issues and unknown
  tensor maps. They use Nat/Bool/origin/protocol metadata, not a real-state
  equality decider. Import/type/syntax/timeouts never count as logical rejections.
- Full gate `/tmp/ptx-double-buffer-resource-admission-gate.log` exited zero:
  47 Rust tests, Clippy warnings denied, six rejection-harness integration tests,
  30 generated AST comparisons, 3491 Lean jobs, 5116 audited declarations,
  5085 resolved public names and 520 individually refuted assertions. All 30 PTX
  examples assemble. Observed target checks included 1.5 seconds for local
  iteration cases, 1.2 seconds for history admission, 1.4 seconds for agreement
  and 1.4 seconds for the new test module. These are proof costs, not GPU timings.
  Updated coverage metadata and whitespace checks pass.
- Assembly evidence refreshed at 2026-11-06 02:38:07 UTC, 30/30 current hashes.
  Existing GPU evidence stays at 2026-11-05 07:46:53 UTC, 15/15 current hashes,
  25 sm_89 cases (24 exact-byte results and one completion-only). No new Hopper
  GPU, IEEE/logits/token-equivalence or performance result is added.
- Remaining: combined source/CTA/internal/resource control acyclicity, remaining
  native-control/eligibility and coupled shared-byte RF/co/causality/coherence/
  observer admission; full-Pre functional refinement for arbitrary admitted
  executions and an independently compatible completed-launch witness;
  allocation/in-flight lifetime, runtime/Iris correspondence and general output
  geometry. Other original acceptance-case/boundary obligations remain. All
  required cases are still partial; exact paper 81-form parity is unconfirmed.
  The original full goal remains active with its exact-output target intact.
- Goal ledger snapshot at 2026-11-06 02:38:54 UTC: 9,868,733 tokens versus the
  preceding published 9,807,782, a difference of 60,951. Interim tool-reported
  usage, not final billed usage or a goal-completion report.

### 2026-11-06 — Repeated TMA control acyclicity and complete TMA components

- Instance: the actual double-buffer GEMM's constructed first-attempt-successful-
  wait source witness, arbitrary real tiles, both stages and all 128 lanes.
  `data_tma_components` has the existing `T<=2^28` source-execution bound. This
  component witness is not a universal theorem for all admitted executions.
- Concrete gap: locally valid exhaustive resource histories, captured inputs
  and source completion did not establish that source PO, CTA rendezvous, TMA
  internals and resource serialization coexist without a cycle. Comparing raw
  producer/peer serials is invalid because their trace lengths differ and the
  producer omits the final prefetch.
- `ControlClock` embeds both event streams into one virtual clock, with the
  final three-event gap and the zero-tile tail handled explicitly. Source ranks
  are `1024*tick+lane`; implicit descriptor/read/write/notification nodes have
  distinct positive offsets from their actual issue rank. These numbers are a
  control proof device, not GPU timing, publication or ownership permissions.
  Source PO and each TMA internal-edge constructor strictly increase the rank.
- `ControlResourceRanks`/`ControlResources` identify every actual history origin's
  global rank and prove the full resource histories strictly sorted in that same
  order, including all 128 same-phase waits. This gives increasing ranks for all
  resource serialization edges, not just one selected notice/wait pair.
- `ControlGenerations` proves that ordinary bookkeeping, TMA issue and native
  arithmetic/writeback preserve CTA counters. Actual loop checkpoints have the
  derived generation list, reuse barrier 2 has generation equal to the tile,
  and the output barrier 1 still has generation zero. `ControlCtaCases`/`Trace`
  exhaustively classify actual initialization, every reuse and output CTA tag
  through the complete rich trace and its Hopper view. No participant/generation
  matching is assumed as a precondition to those source cases.
- `ControlCtaRanks` places the last arrival before the first return for every
  actual matched CTA tag across all lanes. `ControlAdmission` combines the four
  increasing edge classes with the fixed path/rank rule, proving
  `Tma.ControlAcyclic`. The source, completion, descriptor, payload, exhaustive
  history and control fields now construct `Unified.TmaComponents` for the
  repeated source witness and independently represented initial inputs.
- Method/reuse: the same global order covers zero tiles, both buffer slots,
  arbitrary reuse rounds, both TMA sizes, producer/peers and implicit operations.
  This is a proved composition using the existing event semantics; it is not a
  demonstrated new ownership method across distinct optimization mechanisms.
  Neither control order nor this record grants shared-byte visibility, protects
  overwrite, admits native ISA eligibility or proves observable output.
- Validation: nine new Lean modules and 91 audited public theorems, including
  20 test theorems. Actual source projections check CTA generations at zero,
  three and five tiles, cross-lane matching, wrong barrier/generation rejection,
  producer/peer final gaps, all-lane rank bounds and separated implicit steps.
  A checked actual notification-to-consumer resource edge, together with the
  acyclicity theorem, formally rejects its reverse control dependency. That
  record/path negation is separate from strict decidable refutation counts.
- Twenty new strict false assertions reject stale/wrapped CTA generations,
  arrival/return confusion, wrong CTA matching, omitted clock shifts, missing
  lane offsets, aliased implicit ranks and reversed notice/wait rank claims.
  They use closed Nat/Bool/tag metadata, not real-state equality decisions.
  Import/type/syntax/timeouts never count as semantic refutations.
- Regression preservation: an accidental new-test filename collision was
  corrected before integration. The original 59-line header/retry test module
  was recovered from its original creation heredoc, retaining all 11 public
  theorem names; SHA-256 is
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
  New tests use the separate `HopperDoubleBufferControlAdmission` module and
  namespace. Both modules checked independently and all prior rejection cases
  remain in the full gate.
- Full gate `/tmp/ptx-double-buffer-control-components-gate.log` exited zero:
  47 Rust tests, Clippy warnings denied, six rejection-harness integration tests,
  30 generated AST comparisons, 3500 Lean jobs, 5207 audited declarations,
  5176 resolved public names and 540 individually refuted assertions. All 30
  PTX examples assemble. Observed target checks included 3.3 seconds for local
  CTA cases, 2.0 seconds for resource ordering, 1.8 seconds for control admission,
  2.7 seconds for new tests and 4.5 seconds for restored header tests. These are
  proof costs, not GPU measurements. Updated coverage metadata and whitespace
  checks pass. A metadata-read approval timeout was resolved by the explicitly
  permitted single retry; the command was not executed on the timed-out attempt.
- Assembly refreshed at 2026-11-06 03:10:13 UTC with 30/30 current hashes.
  Existing GPU evidence stays at 2026-11-05 07:46:53 UTC, 15/15 current hashes,
  25 sm_89 cases (24 exact-byte and one completion-only). No Hopper GPU,
  IEEE/logits/token-equivalence or speedup evidence is added.
- Remaining: actual repeated native-control/eligibility and coupled shared-byte
  RF/co/causality/coherence/proxy/observer admission; full-Pre functional refinement
  for arbitrary admitted executions and independently compatible completed-launch
  nonvacuity; allocation/in-flight lifetime, runtime/Iris correspondence and
  general output geometry. Other original acceptance-case and boundary work
  remains. All required cases stay partial, exact paper 81-form parity is
  unconfirmed, and the original goal stays active with the exact-output target.
- Goal ledger snapshot at 2026-11-06 03:13:55 UTC: 9,976,926 tokens versus the
  preceding published 9,868,733, a difference of 108,193. Interim tool-reported
  usage, not final billed usage or a goal-completion report.


### 2026-11-06 — Repeated native publication, completion and buffer reuse

- Optimization instance: the existing two-slot Hopper GEMM prefetch pipeline,
  with a fixed 64x8 output tile, arbitrary supported K-tile count and arbitrary
  real A/B inputs. The source, generated AST, launch geometry and exact-output
  target are unchanged. The cost/overlap of its CTA reuse rendezvous still needs
  measurement on Hopper hardware; this milestone claims no speedup.
- Concrete previous limitation: source/TMA/control admission and tensor-shaped
  replies did not establish that native operand reads see the corresponding
  actual TMA writes, or that an in-flight read completes before the same slot
  is overwritten. The one-phase unique-writer argument cannot cover repeated
  writes at one shared byte. Merely ordering source events or observing an
  mbarrier/CTA rendezvous would not discharge native completion.
- Formal components: `HopperDoubleBufferNativePublication` derives
  `Access.CompletionObserved` from the actual exhaustive `HistoryValid` records
  for both A and B, at each tile's own lifetime/phase. Actual source PO connects
  each of 128 member waits to that member's WGMMA issue. The resulting
  `Unified.TmaReady`, `NativePublished` and byte-order proofs are per operand
  byte, for every supported tile and arbitrary real input; they do not assume a
  blanket resource/control-to-memory publication rule.
- `HopperDoubleBufferNativeCompletion` identifies the actual PC 79
  `wait_group 0` event in every tile/lane, with mark sequence 4*tile+3, groups
  tile+1, a checked previous completion frontier, final frontier tile+1 and the
  actual query index. A source-indexed collective and native ledger facts prove
  `WgmmaCompletedAt` and completion byte-order edges. No CTA event is treated as
  completing an outstanding native operation.
- `HopperDoubleBufferNativeReuse` reconstructs both actual CTA 2 endpoints with
  generation equal to the tile. Every lane's native wait precedes its arrival,
  which connects through the matching CTA return to the producer's later copy
  issue. For any later tile at least two rounds ahead in the same slot, actual
  write locations agree byte-for-byte with the old operand location. This
  derives `NativeReuse` and byte-order edges from the completed read to that
  later A/B write, including nonadjacent reuse such as tile 0 to tile 4.
- Method classification/reuse evidence: this applies existing semantic
  publication/completion/reuse rules to a repeated source pipeline, rather than
  introducing a new unproved rule or claiming a new research method. Both
  operands and arbitrary repeated phases share the construction. They are one
  optimization instance, not evidence of reuse across independent optimization
  mechanisms. Allocation/in-flight ownership and runtime/Iris correspondence
  remain separate work.
- Tests: the new `HopperDoubleBufferNativePublication` test module adds 26
  public facts, including parameterized arbitrary-real publication/completion/
  reuse, last-lane ordering, nonadjacent reuse and formal rejection of both CTA
  and mbarrier substitutes for native completion. Stale A/B observations are
  rejected after parity wrap. Metadata-only source checks cover one/three/five
  tiles, producer/peer query differences, the omitted final prefetch, native
  group history, distinct reused-slot producer IDs and both byte boundaries.
  Twenty additional closed decidable false assertions are individually refuted
  by the strict diagnostic harness. Record/Prop rejection proofs are separately
  checked and are not counted among those twenty. No real-valued state equality
  decider or weakened arithmetic/output goal is introduced.
- Validation: the registered full gate
  `/tmp/ptx-double-buffer-native-admission-components-gate.log` exited zero:
  47 Rust tests, Clippy with warnings denied, six rejection-harness integration
  tests, 30 generated AST comparisons, 3504 Lean jobs, 5267 audited declarations,
  5236 environment-resolved public names, 560 individually refuted assertions
  and all 30 PTX examples assembled. The three source modules contain 34 new
  public theorems; with 26 test facts, all 60 have exact `#print axioms` entries
  and are included in the resolved environment inventory. Targeted build times
  were 1.7 seconds (publication), 2.0 (completion), 2.0 (reuse) and 2.1 (tests).
  These are proof costs, not GPU performance. Coverage metadata and scoped
  whitespace checks pass.
- Check-run accounting: an initial registration script used the wrong relative
  root and failed before writing files. Its unregistered preliminary gate was
  explicitly stopped (exit 143) and is not counted as validation. Registration
  was corrected using an absolute root before the successful gate above. The
  existing header-control test module remains at SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 03:34:27 UTC; all 30 source hashes
  match. GPU evidence remains 2026-11-05 07:46:53 UTC, all 15 source hashes
  match, with 25 sm_89 cases (24 exact-byte and one completion-only). No Hopper
  hardware execution, IEEE/logits/token equivalence or speedup evidence is added.
- Remaining: actual repeated native schedules/control admission and eligibility;
  coupled shared-byte RF/co, causality, coherence, proxy and observer admission;
  full-Pre functional refinement over arbitrary admitted executions and an
  independently compatible fully admitted completed-launch witness. General
  output geometry and allocation/lifetime/runtime/Iris links remain open. The
  new byte-order components alone do not supply these obligations. All required
  cases remain partial, exact paper 81-form parity remains unconfirmed, and the
  original goal remains active with its exact-output requirement.
- Goal ledger snapshot at 2026-11-06 03:34:40 UTC: 10,124,922 tokens versus the
  preceding published 9,976,926, a difference of 147,996. Interim tool-reported
  usage, not final billed usage or a goal-completion report.


### 2026-11-06 — Repeated native schedules and combined control admission

- Optimization instance: the same two-slot Hopper GEMM pipeline, fixed 64x8
  output geometry and arbitrary supported K-tile count/real inputs. This round
  changes proofs, tests and evidence only; the PTX/AST, mathematical result and
  exact hardware-output requirement are unchanged. No Hopper timing, overlap
  or speedup claim is made.
- Concrete previous limitation: valid TMA histories/control and actual native
  publication/completion/reuse components did not establish complete native
  participation or combined construct control. Reusing the one-phase native
  proof would lose dynamic group/sequence identity. Also, using a lane's source
  return rank as its native arrival rank would not put a high-lane arrival
  before a matching low-lane return, because repeated resource histories retain
  lane offsets. Source completion alone cannot close these control obligations.
- Formal schedule/source components: `HopperDoubleBufferNativeSchedules`
  derives the actual four-operation sequence in every tile (PCs 76..79, dynamic
  sequence 4*tile+index, actual MMA descriptors/ordinal/group, commit group and
  wait group count). Leader-specific prefetch/query work and the omitted final
  prefetch do not change that native sequence. All 128 aligned schedules match,
  including zero/one/repeated rounds; checked located replay connects schedules
  to the same rich interpreter execution.
- `NativeCases` and `NativeInventory` exhaustively classify every actual rich
  native signature in the complete candidate by tile, lane and one of the four
  source-event indices. Initialization, TMA/header work and output cannot forge
  a native signature. Signature sequence recovers tile/instruction identity;
  different rounds remain distinct when they reuse identical descriptors.
  `NativeRanks` proves each actual native event has virtual tick
  12+10*tile+index, identifies actual MMA groups and native wait frontiers, and
  proves matching native signatures have equal ticks.
- `NativeControl` adds separate native arrival and operand-read ranks around
  the existing source/resource rank. An arrival precedes all matching warp
  returns while retaining source/resource lane offsets. Native issue precedes
  operand reads, and a source-matched completed wait follows them; the actual
  issue-group/wait-frontier relation handles any later finishing round. Together
  with source PO, CTA, implicit TMA and resource edges, all combined control
  edges strictly increase one rank. This proves `Unified.ControlAcyclic` and
  `Unified.ControlAdmitted` for arbitrary real inputs and supported tile counts
  in the chosen source witness. It is construct control admission, not
  byte-memory/ISA eligibility, observer admission or hardware correspondence.
- Method classification/reuse evidence: this is engineering closure using the
  existing native construct model and source semantics. The rank and source
  classification are reused across all four native operations, producer/peers
  and arbitrary repeated slots; this remains one optimization instance, not a
  claim of a new ownership protocol or independent optimization-method reuse.
- Tests: the new `HopperDoubleBufferNativeControl` module adds 27 public facts,
  including arbitrary-real control admission, zero/repeated concrete cases,
  all-warp actual source-PC links, wrong warp/round/instruction rejection,
  missing native wait/participant rejection and an actual rendezvous reversal
  rejection. Missing-thread/wait cases check the full schedule admission
  predicate using participation and schedule-length proofs. Sync and participant
  metadata adapters have audited parameterized correspondences to actual source
  signatures/schedules; they are not independent assumed checkers. Twenty new
  strict assertions use only closed decidable metadata (including these linked
  adapters), never real-valued event/state equality.
- Verification: registered full gate
  `/tmp/ptx-double-buffer-native-control-admitted-gate2.log` exited zero:
  47 Rust tests, Clippy with warnings denied, six rejection-harness integration
  tests, 30 generated AST comparisons, 3510 Lean jobs, 5334 audited declarations,
  5303 environment-resolved public names, all 580 individually refuted
  assertions and all 30 PTX examples assembled. All 40 new source theorems and
  27 test facts have exact `#print axioms` entries and resolved environment
  coverage. Observed targeted builds were 1.0 seconds (schedules), 2.2 (local
  cases), 2.4 (inventory), 1.3 (ranks), 1.3 (control), and 1.3 (final tests).
  These are proof/check costs, not kernel performance. Coverage metadata and
  scoped whitespace checks pass. No new semantic assumptions or forbidden
  proof escape is introduced.
- Check-cost/debug accounting: three preliminary test compilations were
  deliberately terminated while confirmed active after high CPU/memory usage
  (observed approximately 4 GiB RSS). An isolated sequential probe exposed a
  missing `Ptx.Kernels` namespace import and resulting error recovery terms;
  the import was fixed, and expensive direct candidate normalization was also
  replaced with source-corresponding metadata/structural proofs. A later test
  attempt identified a missing finite Boolean contradiction proof, which was
  fixed. The first full gate correctly rejected an `isDefEq` heartbeat timeout
  in a five-tile participant assertion; a timeout was never counted as a false
  assertion proof. The participant adapter correspondence removes that repeated
  normalization. All 20 additions then passed the isolated strict harness under
  its unchanged default heartbeat limit, followed by the successful full gate.
  Preliminary failed/stopped checks are not validation evidence. Existing
  header-control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 04:07:37 UTC, all 30 hashes current.
  GPU evidence remains 2026-11-05 07:46:53 UTC, all 15 hashes current, with 25
  sm_89 cases (24 exact-byte and one completion-only). No Hopper GPU execution,
  hardware IEEE/logits/token-equivalence or speedup evidence is added.
- Remaining: native eligibility and the coupled repeated shared-byte RF/co,
  causality, coherence, proxy and observer witness; full-Pre functional
  refinement for arbitrary admitted executions and independently compatible
  fully admitted completed-launch nonvacuity; allocation/in-flight lifetime,
  runtime/Iris links and general output geometry. The coverage case's remaining
  field was compacted to the current proven boundary and open obligations;
  existing evidence paths and regression cases are retained. All required
  acceptance cases stay partial, exact paper 81-form parity remains unconfirmed,
  and the original goal remains active with its exact-output requirement.
- Goal ledger snapshot at 2026-11-06 04:07:51 UTC: 10,242,777 tokens versus the
  preceding published 10,124,922, a difference of 117,855. Interim tool-reported
  usage, not final billed usage or a goal-completion report.


### 2026-11-06 — Repeated shared-writer inventory, phase order and conditional RF

- Optimization instance: the same two-slot Hopper GEMM source with arbitrary
  supported K-tile count and real inputs, fixed 64x8 output geometry. PTX/AST,
  execution semantics, input representation and exact-output target are
  unchanged. This adds proof/test components, with no new hardware performance
  or overlap claim.
- Concrete previous limitation: the one-phase shared-input proof relied on a
  unique writer at each native operand byte and initialization-only coherence.
  Repeated slots have multiple actual writers at the same byte. Source/native
  control legality and individual publication/completion/reuse edges did not
  classify all of those writers or establish the phase-writer rule's premises.
- `HopperDoubleBufferMemoryInventory` proves an exhaustive memory envelope over
  actual rich source events, including initialization, every loop iteration and
  output. Ordinary source events are global output stores or CTA events, and there
  is no non-bulk copy. Thus an actual write at a shared location must be a TMA
  write, not an omitted generic/RMW/non-bulk access or a native-read write.
- `MemoryGeometry` classifies every actual tensor-write location using the
  existing exhaustive source-copy inventory. The A/B regions and opposite
  slots are disjoint, and byte offsets invert uniquely within a region. At a
  native operand byte, every writer is exactly the corresponding operand's
  actual TMA producer in some supported same-slot round. It does not assume
  the round is the current one or that all rounds share one writer identity.
- `MemoryPhases` composes existing byte publication and actual native completion/
  reuse edges. Same-slot distinct rounds are at least two apart. Every older
  writer precedes the current producer; the current producer publishes to the
  read; future overwrites follow the read's checked native completion. Every
  pair of actual writers at that byte is equal or byte-ordered by round, even
  for nonadjacent reuse such as tile 0 to tile 4. These are byte-preserved
  paths, not a blanket control-to-memory rule.
- `MemoryInputs` excludes local native-byte taint for arbitrary RF, both from
  writer/read races and from races among the repeated writers. Eligibility
  still explicitly requires global no-mixed-size-race evidence. Under full
  `Unified.MemoryConditions` and that global premise, the existing phase-writer
  rule forces RF to the current actual TMA producer. Stale and future producer
  choices are rejected, including after parity wrap. These are conditional
  theorems: neither premise is asserted to be inhabited here, and they are not
  a complete memory-existence or universal functional-correctness proof.
- The initial-only `InitialCo` relation is formally incompatible with coherent
  repeated same-byte writes, for arbitrary RF. A concrete test supplies two
  distinct actual TMA writers of the same shared byte and refutes the global
  unique-writer assumption. This identifies a real proof-construction limit
  rather than silently applying the old one-phase helper.
- Method classification/reuse evidence: this is engineering application of the
  existing native byte-order and phase-writer rules, not a new semantic axiom
  or claimed ownership protocol. The construction covers A/B operands,
  producer/peer execution and arbitrary repeated rounds. Those are instances
  within one optimization mechanism; independent optimization-method reuse and
  allocation/in-flight ownership/runtime/Iris correspondence remain open.
- Tests: the new `HopperDoubleBufferMemoryPhases` module adds 22 public facts.
  They cover actual source envelopes, absent non-bulk operations, first/last/
  out-of-range copy byte offsets, opposite/reused slots, distinct real source
  writers, rejected unique-writer/initial-only-co assumptions, nonadjacent
  writer order, arbitrary-real local untaintedness and conditional current/
  stale/future RF conclusions. The conditional tests retain their full-memory
  and global no-mixed-size-race hypotheses and are not completed-launch
  witnesses. Twenty additional closed decidable metadata assertions are
  individually refuted. Prop/record rejection proofs are separately checked
  and are not included in those twenty; no real-valued equality decider is used.
- Validation: full gate `/tmp/ptx-double-buffer-memory-phases-gate.log` exited
  zero: 47 Rust tests, Clippy with warnings denied, six rejection-harness
  integration tests, 30 generated AST comparisons, 3515 Lean jobs, 5389 audited
  declarations, 5358 environment-resolved public theorem names, 600 individually
  refuted assertions, and all 30 PTX examples assembled. All 33 new source
  theorems plus 22 test facts have exact `#print axioms` entries and resolved
  environment coverage. The isolated twenty-assertion harness also passed
  under its unchanged default budget. Observed final targeted builds were
  1.4 seconds (inventory), 1.0 (geometry), 1.3 (phases), 1.5 (inputs), and 1.7
  (tests). These are proof/check costs, not GPU measurements. Coverage metadata,
  scoped whitespace and new-source whitespace checks pass.
- Development accounting: initial compile attempts caught incorrect Ampere
  constructor patterns, missing finite-case contradiction/offset rewrite and
  descriptor argument details, and unspecified existential byte values in a
  test. Those were fixed before the successful checks; no recovery term or
  failed run is counted as proof evidence. The existing header-control test
  module retains SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 04:25:45 UTC, all 30 source hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC, all 15 hashes current,
  with 25 sm_89 cases (24 exact-byte and one completion-only). No Hopper GPU
  execution, hardware IEEE/logits/token-equivalence or speedup evidence is added.
- Remaining: global no-mixed-size-race exclusion/unconditional eligibility;
  independently compatible coupled RF/co, causality, coherence, atomicity,
  per-location SC, proxy and observer admission for the complete repeated
  candidate; full-Pre functional refinement over arbitrary admitted executions
  and fully admitted completed-launch nonvacuity; allocation/in-flight lifetime,
  runtime/Iris links and general output geometry. All required cases remain
  partial, exact paper 81-form parity is unconfirmed, and the original goal
  stays active with its exact-output requirement.
- Goal ledger snapshot at 2026-11-06 04:26:17 UTC: 10,313,584 tokens versus the
  preceding published 10,242,777, a difference of 70,807. Interim tool-reported
  usage, not final billed usage or a goal-completion report.


### 2026-11-06 — Global mixed-size exclusion, derived eligibility and explicit RF values

- Optimization instance: the same repeated two-slot Hopper GEMM, arbitrary
  supported K-tile count/real inputs and fixed 64x8 output geometry. Source
  PTX/AST, operational/event semantics, numeric target and represented input
  layout are unchanged. No Hopper execution, prefetch-overlap or speedup result
  is claimed by these proof changes.
- Concrete previous limitation: phase-correct RF still required a caller's
  global no-mixed-size-race premise. Local native-byte untaintedness did not
  discharge it because it covers the whole unified inventory. Also, a
  conditional RF conclusion under assumed `MemoryConditions` did not construct
  any independently compatible read-value witness.
- `HopperDoubleBufferSourceFootprints` recovers actual ordinary footprints from
  the complete source/global-write inventory. Every such access is an aligned
  four-byte output word in [8192,10240); CTA/native/resource events do not
  become ordinary memory accesses through erasure. This uses actual rich event
  identities and source/spec output bytes, not an assumed layout checker.
- `AccessRegions` exhaustively classifies ordinary, non-bulk, TMA, tensor-map
  and native footprints. Non-bulk operations are absent; native/TMA shared
  accesses are single bytes, global tensor input reads are single bytes at or
  above 65536, and tensor-map blocks have 128 bytes ending no later than 4352.
  Writers are shared bytes or aligned output words. Any writer/access conflict
  therefore has the same footprint: shared overlaps are the same byte; output
  overlaps are the same aligned word; input/descriptor regions cannot overlap
  an output writer. The candidate contains different access sizes, but those
  do not imply mixed-size races at conflicting locations.
- The new generic `Unified.compatible_conflicts_no_mixed_size_race`
  theorem derives exclusion directly from the existing `MixedSizeRace`
  definition and actual conflicting footprints. Both the one-stage baseline
  and repeated source use it. The original one-stage theorem names/APIs are
  preserved and rechecked. This adds a proved reusable rule, not a semantic
  axiom, relaxed race condition or eligibility oracle.
- `NativeEligibility` excludes global mixed-size races for arbitrary RF and
  supported tile counts, including the zero-tile path. Combined with the prior
  local untaintedness result, it derives native eligibility without a caller
  no-race premise. Current/stale/future RF results now require only their
  explicit full-memory admission premise; constructing that full predicate
  remains mandatory and is not inferred from eligibility.
- `ReadWitness` goes beyond a conditional RF claim: actual representative MMA
  calls are classified by source tile and lane zero. The explicit RF map
  selects that tile's actual TMA producer for native reads and initial memory
  for global input/descriptor reads. Initial proxy values use the existing
  independently represented packed input/tensor-map memory and arbitrary
  frame; no desired native reply is used to define initial shared memory.
  Stored tensor-map provenance, actual transfer payloads and source-call bytes
  prove value agreement for every actual read and hence `ReadAgreement` using
  the model's eligibility predicate. No assumed causal or full memory execution is a
  construction premise. This is value/source agreement only, not a complete
  causal/coherent/atomic/SC/observer memory witness.
- Method classification/reuse evidence: engineering closure using existing
  byte, source, input and race definitions. The footprint-conflict rule is
  shared between the one-stage and repeated sources; A/B and every repeated
  round use the same source/value construction. This is not independent
  optimization-method reuse or a new ownership/runtime protocol. Allocation,
  in-flight lifetime and runtime/Iris correspondence remain open.
- Tests: the new `HopperDoubleBufferEligibility` module adds 23 public facts.
  They project actual output/native/TMA-input/TMA-write/tensor-map footprints,
  absent notification/CTA/non-bulk footprints, zero/repeated cases, region
  boundaries and current versus reused RF producer IDs. Parameterized tests
  cover arbitrary-real global mixed-size exclusion, eligibility for arbitrary
  RF, and independently constructed read agreement for arbitrary input/frame.
  The remaining full-memory premise in universal RF forcing is explicit.
  Twenty extra closed decidable metadata assertions are individually refuted:
  wrong sizes/addresses, unaligned or out-of-range regions, and old/future RF
  producer IDs. The region adapter has an audited correspondence to the region
  predicate; no real-valued equality decider is used.
- Validation: full gate
  `/tmp/ptx-double-buffer-eligibility-read-witness-gate.log` exited zero:
  47 Rust tests, Clippy with warnings denied, six rejection-harness integration
  tests, 30 generated AST comparisons, 3521 Lean jobs, 5431 audited declarations,
  5400 environment-resolved public names, all 620 individually refuted
  assertions and all 30 PTX examples assembled. All 19 new source theorems
  (including the generic rule) and 23 test facts have exact `#print axioms`
  entries and resolved environment coverage. The old single-stage eligibility
  module checked independently after its refactor (1.9 seconds); observed new
  eligibility/read-witness/test builds were 1.5/1.4/2.1 seconds. These are proof
  costs, not GPU performance. The isolated twenty-assertion check, coverage
  metadata, scoped whitespace and new-source whitespace checks also pass.
- Development accounting: initial compile attempts caught destructured location
  naming/projection normalization, descriptor `Option` simplification order,
  explicit ordinary-read cases/finite-lane zero normalization, and the finite
  region adapter's typeclass normalization. These were fixed before successful
  checks; failed attempts are not proof evidence. Existing header-control tests
  retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 04:54:19 UTC, all 30 source hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC, all 15 hashes current,
  with 25 sm_89 cases (24 exact-byte and one completion-only). No Hopper GPU,
  hardware IEEE/logits/token-equivalence or speedup evidence is added.
- Remaining: causal/coherence/atomicity/per-location-SC admission and suitable
  co for the explicit RF, byte/proxy/observer consistency and independently
  compatible fully admitted completed-launch existence. Full-Pre functional
  refinement over arbitrary admitted executions, allocation/in-flight lifetime,
  runtime/Iris links and general output geometry remain open. No full memory
  premise was hidden or treated as inhabited. All required cases stay partial,
  exact paper 81-form parity remains unconfirmed, and the original goal remains
  active with its exact-output requirement.
- Goal ledger snapshot at 2026-11-06 04:54:51 UTC: 10,389,339 tokens versus the
  preceding published 10,313,584, a difference of 75,755. Interim tool-reported
  usage, not final billed usage or a goal-completion report.

### 2026-11-06 — Independent full memory witness for the repeated Hopper source

- Optimization instance: the same two-slot Hopper GEMM with arbitrary represented
  real inputs, frame and supported tile count (at most 2^28), including zero
  tiles, and fixed 64x8 output geometry. PTX, generated AST, numeric target and
  operational/event definitions are unchanged. These are model-relative proofs,
  with no new Hopper execution, overlap or speedup measurement.
- Concrete previous limitation: independently choosing RF and proving read values
  did not establish causal, coherent, atomic or per-location-SC admission. The
  old initialization-only `InitialCo` remains unsuitable for repeated writers of
  a reused physical shared byte; its previous rejection results are preserved.
- `UnifiedMemoryControl` proves a reusable one-way refinement from actual byte
  edges/order to checked native-control paths, with an explicit no-nonbulk
  source fact. It covers publication, completion and reuse; it does not treat
  arbitrary control order as publication. The rule is checked against both the
  one-stage and repeated candidates. A rank on those control nodes then orders
  the repeated candidate's byte, observation and causality edges.
- `ReadConflicts` uses the actual inventory: base reads are global immutable
  input/descriptor bytes; read/write conflicts are native shared operand reads.
  `SourceFootprints.data_source_footprint_owner` recovers the actual output
  word's lane, slot and thread. Overlapping aligned output words have the same
  lane/thread and hence their writers are identical or ordered by source PO.
  Shared writers are ordered using their actual operand-byte owner and tile
  phase. `WriteConflicts` therefore orders all actual same-byte writers without
  assuming a globally unique shared writer or a source serial identity oracle.
- The explicit coherence witness is `Unified.RankedCo` over actual writers.
  `UnifiedRankedCoherence` proves its domain, initialization, transitivity,
  comparability, race and causality requirements from writer ordering. This is
  a witness construction, not an extra rank restriction on admitted executions.
  `CausalWitness` combines the previously explicit RF/value witness with current,
  older and future producer classification to prove all causal constraints.
- `MemoryAtomicity` proves single-copy atomicity for actual singleton native
  reads and derives RMW atomicity from the absence of nodes that both read and
  write. `MemorySC` ranks PO, RF, coherence and from-read communication; reuse
  paths establish native-read-before-future-writer order. `MemoryWitness` then
  constructs all fields of `Unified.MemoryConditions` for arbitrary represented
  input/frame and supported tile count. No assumed memory execution or newly
  admitted semantic axiom is used. A test theorem combines source/TMA, native
  control and this full memory witness for the same candidate and parameters.
- Method classification: engineering closure using the current model and
  reusable byte-to-control/coherence lemmas, not a new asynchronous ownership
  protocol or independent optimization-method reuse. The initial memory still
  comes from packed input/tensor maps and an arbitrary frame, rather than being
  defined by desired native replies. Observer/final-output admission remains
  a distinct obligation; full memory admission alone does not prove it.
- Tests: 41 new public source theorems (including the stronger source-owner
  helper) and 20 test facts, all with exact axiom-audit entries. Tests cover
  actual ranks, initialized/current/reused co edges, absent/read/descriptor
  endpoints, wrong locations, both source candidates, zero/repeated rounds,
  arbitrary-real memory existence and compatible source/control/memory.
  Twenty additional closed decidable metadata assertions are individually
  refuted under the unchanged heartbeat limit; no real-valued equality is
  placed in the rejection decider.
- Validation: `/tmp/ptx-double-buffer-full-memory-gate.log` ends with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness integration tests, 30 generated AST comparisons, 3532 Lean jobs,
  5492 audited declarations, 5461 environment-resolved public names, all 640
  individually refuted assertions and 30 assembled PTX examples. The isolated
  twenty-rejection run also passed. Targeted new kernel builds were about
  1.3–1.7 seconds and the new test module 1.9 seconds; these are proof-checking
  costs, not GPU performance. Failed development attempts involving missing
  imports, endpoint/history inference and location/finite-zero normalization
  were corrected before successful checks and are not counted as evidence.
- Assembly evidence refreshed at 2026-11-06 05:22:06 UTC; all 30 hashes match.
  GPU evidence remains 2026-11-05 07:46:53 UTC; all 15 source hashes match,
  with 25 sm_89 cases (24 exact-byte and one completion-only). The existing
  header-control test retains SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Remaining: a compatible observer/final-output witness; full-Pre functional
  refinement over arbitrary admitted executions; fully admitted completed-launch
  existence including profile/allocation/lifetime; runtime/Iris correspondence
  and general output geometry. All required cases stay partial, exact paper
  81-form parity remains unconfirmed, and the original full goal stays active.
  No Hopper GPU, hardware IEEE/logits/token-equivalence or speedup result is
  claimed. The exact-output requirement is unchanged.
- Goal ledger snapshot at 2026-11-06 05:24:58 UTC: 10,916,018 tokens versus the
  preceding published 10,389,339, a difference of 526,679. Interim tool-reported
  usage, not final billed usage or a goal-completion report.

### 2026-11-06 — Compatible completed observation of repeated Hopper outputs

- Optimization instance: the same repeated two-slot Hopper GEMM, arbitrary
  represented real inputs/frame and supported tile count up to 2^28, including
  zero tiles, with fixed 64x8 output geometry. PTX, generated AST, operational
  and event semantics, initial-input representation and numeric target are
  unchanged. No Hopper hardware execution, overlap or performance is measured.
- Concrete previous limitation: full `Unified.MemoryConditions` was inhabited,
  but it did not construct an observer satisfying completion, global-write
  coverage, value agreement and no-stale-output conditions. The unindexed
  output-address inventory recovered lane ownership but not the actual source
  event serial, so it could not establish a unique global writer.
- `StoreInventory` defines `dataStoreId` from the actual pre-output event length
  and store slot. Interpreter-derived event lookup proves the selected event
  exists. Any actual global write is outside the write-free prefix/return
  suffix and hence is one of the four real output stores. This recovers exact
  event ID, address, size and specification payload. Overlap of aligned output
  words and the existing output-layout injectivity then prove unique global
  writers. Shared bytes still have multiple TMA writers on reused rounds; no
  global unique-writer premise is applied to them or to coherence admission.
- `ObserverWitness` constructs a completed generic-proxy observation covering
  all 2048 output bytes and four adjacent frame bytes on either side. Its
  selection uses actual source-indexed stores, not the desired matrix values.
  It satisfies `Unified.ObserverConditions` with exactly the previous initial
  proxy memory, RF, ranked co, histories and source candidate. Global observer
  eligibility follows from the previously derived mixed-size exclusion and
  now-proved unique global writers, for arbitrary RF.
- `ObservedOutput` proves actual store bytes equal the independent tiled
  specification. For any compatible RF/co/observer of this fixed source
  candidate, causality and observer rules force those output bytes; unmodified
  adjacent frame bytes retain their independently represented initial value.
  The independently constructed observer therefore computes the ordinary real
  matrix product with inner dimension 16*T, using the existing algebraic
  specification bridge. A parameterized conjunction combines source/TMA,
  native control, full memory and observation for the same inputs and frame.
  No assumed memory/observer witness or new semantic axiom is a construction
  premise. Universal reconstruction of arbitrary full-Pre source executions is
  not inferred from a theorem about compatible observers of this candidate.
- Negative observer proofs reject both an empty observation domain (missing
  emitted global writes) and observation from initial memory instead of an
  emitted output write. These are parameterized logical rejections, distinct
  from the finite decidable negative harness and from GPU execution tests.
- Method classification/reuse: engineering closure of the current semantics,
  using the existing selected-observer and unique-writer observation rules
  shared with the one-stage baseline. This is not a new ownership protocol,
  runtime correspondence result or independent optimization-method reuse.
- Tests: 22 new public source theorems and 21 test facts, all exactly audited.
  Tests cover domain/frame boundaries and spaces, first/last byte ownership,
  selected actual stores and distinct serials, zero/repeated rounds, arbitrary
  real matrix/frame results, arbitrary compatible RF/co/observers, simultaneous
  component compatibility, and omitted/stale observer rejection. Twenty extra
  closed metadata assertions are individually refuted at the unchanged default
  heartbeat limit. They check incorrect domains, owners, source IDs and writes
  to input/descriptor/shared/frame locations; no real equality decider is used.
- Validation: `/tmp/ptx-double-buffer-observed-output-full-gate.log` exited zero
  and ends with `All verifier checks passed`: 47 Rust tests, Clippy with warnings
  denied, six rejection-harness tests, 30 generated AST comparisons, 3536 Lean
  jobs, 5535 audited declarations, 5504 environment-resolved public names, all
  660 individually refuted assertions and 30 assembled PTX examples. The
  isolated twenty-refutation run also passed. Targeted successful store,
  observer and observed-output builds took 1.4/1.5/1.4 seconds; the 21-fact test
  module took 3.3 seconds. These are proof-checking costs, not GPU performance.
  Development compile failures caught event-ID alias unfolding, lambda/Fin
  normalization and destructured bounds naming; they were corrected before
  successful checks and are not proof evidence.
- Assembly evidence refreshed at 2026-11-06 05:40:09 UTC; all 30 hashes match.
  GPU evidence remains 2026-11-05 07:46:53 UTC, with 15 matching source hashes
  and 25 sm_89 cases (24 exact-byte, one completion-only). The existing
  header-control test retains SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Remaining: full-Pre functional/refinement correctness over arbitrary admitted
  source executions, fully admitted completed-launch existence including the
  remaining profile/allocation/lifetime conditions, runtime/Iris correspondence
  and general output geometry. All required cases remain partial; exact paper
  81-form parity remains unconfirmed. The full goal stays active with its exact
  output requirement. No Hopper GPU, hardware IEEE/logits/token-equivalence or
  speedup result is claimed by these model-relative observed-byte proofs.
- Goal ledger snapshot at 2026-11-06 05:41:47 UTC: 11,026,771 tokens versus the
  preceding published 10,916,018, a difference of 110,753. Interim tool-reported
  usage, not final billed usage or a goal-completion report.

### 2026-11-06 — Actual memory reads identify collective arithmetic inputs

- Optimization instance: the same repeated Hopper GEMM with two reused shared
  slots, arbitrary represented real inputs/frame, supported tile count at most
  2^28 and fixed 64x8 output geometry. The one-stage source checks reuse of the
  generic rule. PTX, generated AST, operational/event predicates and exact
  output target are unchanged; no performance or Hopper hardware test is added.
- Concrete limitation: source-matched tensor arithmetic and actual native RF
  visibility had separate proofs. Tensor correctness used a logical shared
  view whose agreement was constructed from the selected operand reply. A
  reusable rule was needed to identify arithmetic's matrices through admitted
  representative reads and actual producer bytes, before applying that rule to
  arbitrary-source reconstruction. This is an explicit component connection,
  not the completed full-Pre theorem.
- `UnifiedTensorMemory` quantifies over arbitrary candidates, source-matched
  collectives and compatible causal RF/co. Eligibility, RF selection and actual
  producer bytes imply representative `InputAgreement`. Symbolic f16 decoding
  and represented matrix storage identify any matrices in the separately
  admitted arithmetic component. Cohort descriptor equality and uniform input
  values propagate agreement to all 128 lanes; the rule constructs tensor
  conditions and derives the accumulator matrix step. The generic rule keeps
  its eligibility/RF/producer/arithmetic/storage premises explicit. It does not
  manufacture publication, source execution, arithmetic or lifetime admission.
- `HopperDoubleBufferTensorMemory` derives the chosen producer's value directly
  from actual TMA transfer locations/payloads and the independent shared-tile
  representation, without using the native operand reply to define that value.
  Existing phase rules force current-round RF and derive eligibility for any
  compatible full-memory RF/co, including shared-slot reuse. The generic rule
  then proves tensor inputs, tensor admission and matrix-step results. An
  independent bundle uses the same represented input/frame, candidate, RF/co,
  per-tile tensor family and completed observer, with no caller memory-witness
  assumption. Its zero-tile tensor family is empty, as the source requires.
- `HopperStageTensorMemory` applies the same generic memory-to-tensor and
  accumulator-result rules to the actual one-stage collective and its unique
  TMA producers. Method classification: engineering closure and rule reuse
  across one-stage/repeated sources, not a new asynchronous ownership protocol
  or independent optimization-method contribution. Both integrations still
  use constructed source families and their separately proved arithmetic;
  neither establishes arbitrary-source reconstruction from full Pre.
- Tests: 12 new public source theorems and nine public test facts, each exactly
  audited. Parameterized compatible-memory tests derive the actual reused A
  byte and accumulated matrix point. Negative logical proofs reject old and
  future A tiles at the same physical slot, wrong B inputs and an incorrect
  accumulated point. These are symbolic real-valued proofs, not extra decidable
  rejection assertions or hardware comparisons. Existing 660 strict metadata
  refutations remain unchanged. Tests also check the one-stage application,
  arbitrary-real repeated memory/tensor/observer compatibility and the zero-tile
  family. No real-valued equality decider or new semantic axiom is introduced.
- Validation: `/tmp/ptx-tensor-memory-full-gate.log` exited zero and ends with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness integration tests, 30 generated AST comparisons, 3540 Lean jobs,
  5556 audited declarations, 5525 environment-resolved public names, all 660
  individually refuted assertions and 30 assembled PTX examples. The generic,
  one-stage and repeated proof builds each took 1.4 seconds; the nine-fact test
  module took 1.6 seconds. These are proof-checking costs, not GPU performance.
  Development compile failures identified result/gather normalization, explicit
  descriptor inference, placeholder goal order and a concrete natural-to-real
  cast; all were corrected before successful checks and are not proof evidence.
  Coverage metadata, scoped whitespace, new-source scans and exact new audit
  entry checks pass. The coverage capability text was also corrected to reflect
  previously completed repeated-source components; its status stays partial.
- Assembly evidence refreshed at 2026-11-06 05:53:25 UTC, all 30 hashes current.
  GPU evidence stays 2026-11-05 07:46:53 UTC with 15 matching source hashes and
  25 sm_89 cases (24 exact-byte, one completion-only). The old header-control
  test retains SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Remaining: source reconstruction for arbitrary compatible replies/retries and
  completed execution lengths; full-Pre functional/refinement correctness over
  arbitrary admitted executions; fully admitted completed-launch existence with
  remaining profile/allocation/lifetime conditions; runtime/Iris correspondence
  and general output geometry. All required cases remain partial, exact paper
  81-form parity remains unconfirmed, and the full goal stays active. No Hopper
  hardware IEEE/logits/token-equivalence or speedup claim follows from this
  component bridge. The exact-output requirement remains unchanged.
- Goal ledger snapshot at 2026-11-06 05:53:41 UTC: 11,104,878 tokens versus the
  preceding published 11,026,771, a difference of 78,107. Interim tool-reported
  usage, not final billed usage or a goal-completion report.

### 2026-11-06 — Reconstruct retries from actually completed source execution

- Optimization instance: the same repeated two-slot Hopper GEMM and generated
  PTX. No source, AST, event/operational semantics, arithmetic or exact-output
  target is changed. The new inverse rules concern finite completed source
  runs; no GPU speedup, prefetch-overlap or hardware execution is measured.
- Concrete previous limitation: forward header/iteration theorems accepted a
  supplied retry schedule with explicit false/true oracle answers. They did not
  derive that schedule from an arbitrary completed source execution. Complete
  source reconstruction also needed count comparison and exact suffix rules
  for the full rich WGMMA state and events, not just the erased base state.
- `WgmmaTrace` proves done-step rejection, zero successful suffix length after
  completion, unique complete run count/state/events for a fixed interpreter
  and oracle, successful prefixes, strict count ordering before a running
  prefix, availability of its next step, and exact state/event suffix
  decomposition. These rules cover arbitrary programs/oracles/states. Done
  status suffices for count comparison; it is not equated with the stronger
  native completion predicate that also requires an empty pending ledger.
- `WaitReconstruction` derives existence of a successful wait from an actually
  completed run at PC 55 with the explicit running/empty-pending and operand
  bounds hypotheses. If all answers up to that finite count were false, the
  existing failed-wait execution theorem would produce a longer still-running
  prefix, contradicting finite completion. The least success supplies every
  preceding false answer, and a separate lemma proves first-success uniqueness.
  The exact failed/successful prefix and remaining full-state/event execution
  are then reconstructed. A never-ready oracle cannot have a completed run
  under these hypotheses. No fairness or eventual-success premise is added;
  the positive results remain conditional on actual finite completion.
- `HeaderReconstruction` starts at PC 45 with `SelectionReady`, an arbitrary
  oracle and an actually completed run. It splits the real selection prefix,
  derives retries at the selected wait loop and reconstructs selection,
  failed/successful waits, phase update and exact remaining suffix. Tile number
  and retries are arbitrary; neither a retry count nor a selected data oracle
  is a premise. The existing phase/address rules provide operand bounds.
  This closes header inversion, not the rest of an iteration or the kernel.
- Tests: 15 new public source theorems and 13 public test facts, all exactly
  audited. An actual generated-source consumer suffix fails three waits,
  succeeds on the fourth and reaches done. Its source execution and metadata
  are independently checked, the header prefix composes into that same
  completed suffix, and inversion recovers exactly three failures and retained
  wait events. Other proofs reject completion at/before the successful wait
  boundary, a never-ready header, and padding a completed source by one step.
  Canonical arbitrary-real source runs have exactly their proved completion
  count/state/events. Metadata checks inspect only decidable projections; no
  real-valued state/event equality decider is introduced. Existing 660 strict
  rejection assertions are unchanged; the new logical rejections are separate.
- Method classification/reuse: engineering source reconstruction using finite
  interpreter determinism and existing wait/selection/phase execution rules.
  The count/suffix rules apply to the rich interpreter generally; the wait
  rule feeds the header rule. This is not a new asynchronous ownership method
  or independent optimization-method reuse. In particular the nonzero-retry
  test is source evidence, not a newly memory/resource-admitted launch witness.
- Validation: `/tmp/ptx-source-reconstruction-full-gate.log` exited zero and
  ends with `All verifier checks passed`: 47 Rust tests, Clippy with warnings
  denied, six harness integration tests, 30 generated AST comparisons, 3544
  Lean jobs, 5584 audited declarations, 5553 environment-resolved public names,
  all 660 individually refuted assertions and 30 assembled PTX examples. Rich
  trace/wait/header targeted builds took 1.5/1.5/1.4 seconds; the final test
  module took 7.7 seconds in the full gate. These are proof costs, not GPU
  performance. Coverage metadata, scoped whitespace, source scans and all 28
  exact new audit checks pass. Existing header-control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Development accounting: an already-closed suffix equality was corrected.
  An added header-composition test initially reached the existing 2,000,000
  heartbeat limit while normalizing a full run under `change`. Reusing the
  explicit checked run equality through `Except.bind` removed that unfolding;
  the same limit passes. It was not increased. Failed builds are not proof
  evidence, and the unchanged strict rejection harness keeps its own limit.
- Assembly evidence refreshed at 2026-11-06 06:06:03 UTC, all 30 hashes current.
  The hardware inventory's stale 28-fixture assembly count was corrected to
  the 30 reported fixtures, including the collective-cycle and repeated-GEMM
  targets. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 current source
  hashes and 25 sm_89 cases (24 exact-byte, one completion-only).
- Remaining: prefetch/compute/iteration and whole-kernel reconstruction for
  arbitrary compatible replies; resource/control/memory history connections
  for extracted nonzero retries; full-Pre functional/refinement correctness and
  fully admitted completed-launch existence; remaining profile/allocation and
  in-flight lifetime, runtime/Iris correspondence and general output geometry.
  All required cases remain partial; exact paper 81-form parity is unconfirmed.
  The full goal stays active, with no Hopper hardware IEEE/logits/token or
  speedup claim and no relaxation of the exact-output requirement.
- Goal ledger snapshot at 2026-11-06 06:06:15 UTC: 11,157,322 tokens versus the
  preceding published 11,104,878, a difference of 52,444. Interim tool-reported
  usage, not final billed usage or a goal-completion report.

### 2026-11-06 — Derive prefetch shapes and reconstruct a full iteration

- Optimization instance: the same two-slot Hopper GEMM. The new rules concern
  arbitrary-oracle finite completed executions from the loop/prelude/transfer
  entry points, under the explicit existing loop register, accumulator and
  native-ledger invariants and tile-count bound. PTX, AST, execution/event
  semantics and exact-output target are unchanged. No GPU performance,
  prefetch-overlap or Hopper hardware execution is added.
- Concrete previous limitation: header inversion derived retries, but the
  forward prelude/iteration still required the caller to supply both producer
  payload-length equations. Without deriving these from completed source,
  those forward rules did not reconstruct an arbitrary completed iteration.
- `WgmmaTmaInversion` proves that a successful actual TMA instruction forces
  the payload length to match its queried descriptor. The base Hopper rule
  lifts to the rich WGMMA interpreter through successful delegation, and a
  completed-run prefix rule obtains the actual next TMA step. These are
  necessary source shape conditions; descriptor/input values, transfer
  completion, publication, profiles and memory admission are not inferred.
- `TransferReconstruction` executes the actual expectation and A-issue
  prefixes. Finite completion forces the next A step to succeed and hence its
  length equation. That equation permits reconstructing the A prefix; the
  subsequent actual B step then forces its own length equation. The B result
  therefore does not assume that either copy's length was already correct.
- `PreludeReconstruction` splits the actual producer guard and address
  preparation, derives both required TMA lengths through those prefixes and
  reconstructs the exact prefetch state/events and remaining run. A small
  `PreludeRegisters` predicate packages existing concrete register facts and
  is derived from the header/loop invariant; it is not a new ISA admission
  axiom. Consumer and last-tile paths keep their unused replies unrestricted.
- `IterationReconstruction` connects header inversion with the prelude rule.
  It extracts `LoopReplies` from finite completion: failed retries, first
  success and required producer payload sizes are conclusions rather than
  caller premises. The existing compute/advance execution rule then gives one
  exact complete iteration and the remaining full-state/event suffix, with a
  strict iteration-fuel bound. Arithmetic replies remain arbitrary here;
  tensor/value correctness and whole-launch admission are separate obligations.
- Tests: 11 new public source theorems and 15 test facts, all exactly audited.
  A real producer source suffix with three failed waits completes two tiles;
  emitted prefetches retain A's full 2048-byte and B's full 256-byte extents at
  actual queries 8/10. The fixture adjusts the A descriptor/payload query after
  retries so it still transfers the complete A operand, instead of accidentally
  using the baseline oracle's B-sized reply at that shifted query. Inversion
  recovers exactly three retries, derives both lengths and reconstructs the
  actual iteration/remainder. Separate logical proofs reject any completed run
  with short A or B at the transfer entry, and the short-B mutation preserves
  the A reply. Last-tile producer and consumer suffixes complete with unused
  empty TMA replies. The fixtures start at explicit loop/transfer entries and
  are source evidence, not newly admitted initial launches or memory histories.
- Method classification/reuse: engineering source reconstruction using existing
  TMA execution guards, finite prefix rules and register/accumulator frames.
  The shape rule spans base/rich delegation and feeds both A/B issues and
  prelude/iteration composition. This is not a new asynchronous ownership
  protocol or independent optimization-method reuse. No desired matrix result,
  fairness, eventual-readiness or new semantic axiom is introduced.
- Validation: `/tmp/ptx-iteration-reconstruction-full-gate.log` exited zero and
  ends with `All verifier checks passed`: 47 Rust tests, Clippy with warnings
  denied, six harness integration tests, 30 generated AST comparisons, 3549
  Lean jobs, 5610 audited declarations, 5579 environment-resolved public names,
  all 660 individually refuted assertions and 30 assembled PTX examples.
  New logical payload rejections are separate from those unchanged strict
  metadata assertions. No real-valued equality decider is used. Successful
  targeted shape/transfer/prelude/iteration builds were about 1.4/1.7/1.7/1.8
  seconds; the final 15-fact test module took 15 seconds. These are proof costs,
  not GPU performance. Coverage metadata, source/whitespace scans and all 26
  exact new audit-entry checks pass.
- Development accounting: compile attempts caught nested error delegation,
  namespace closure, one-step run/word-wrap normalization and the Boolean
  conjunction equality-versus-iff interface. They were corrected before
  successful checks; failed attempts are not proof evidence. Existing
  header-control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 06:22:32 UTC, all 30 hashes current.
  GPU evidence remains 2026-11-05 07:46:53 UTC with 15 current source hashes and
  25 sm_89 cases (24 exact-byte, one completion-only). No new hardware
  IEEE/logits/token-equivalence or speedup claim follows from these proofs.
- Remaining: composition into whole-loop reconstruction with extracted retry
  schedules; arbitrary initialization/output and complete source reconstruction;
  resource/control/memory history links for nonzero retries; full-Pre
  functional/refinement correctness and fully admitted completed-launch
  existence, remaining profiles/allocation/in-flight lifetime, runtime/Iris
  correspondence and general output geometry. All required cases remain partial,
  exact paper 81-form parity is unconfirmed, and the full goal stays active
  without relaxing its exact-output requirement.
- Goal ledger snapshot at 2026-11-06 06:23:06 UTC: 11,226,445 tokens versus the
  preceding published 11,157,322, a difference of 69,123. Interim tool-reported
  usage, not final billed usage or a goal-completion report.

### 2026-11-06 — Extract and reconstruct the whole source K loop

- Optimization instance: the same repeated two-slot Hopper GEMM. The new
  source rules quantify over arbitrary oracles, real accumulator fragments,
  active starting tile and supported tile count under the existing loop-entry
  register/native-ledger invariant and actual finite completion. PTX, AST,
  operational/event semantics and exact-output target are unchanged. No new
  GPU execution, overlap or performance measurement is added.
- Concrete previous limitation: inversion of a single iteration did not
  provide one schedule for the entire loop. Extending an extracted schedule
  needed a checkable reason that a future retry entry leaves all previously
  executed source states, query IDs and events unchanged; otherwise later
  oracle replies could be related to the wrong query.
- `LoopLocality` proves exact prefix equalities for `loopQuery`, `loopFuel`,
  full `loopCheckpoint` (including arithmetic fragments) and `loopEvents`
  whenever retry entries agree on the executed tile range. These are the
  original source-loop definitions, not a new executor or a relaxed trace
  equivalence. Entries outside that range are intentionally irrelevant.
- `LoopReconstruction.completed_loop_reply_prefix` inductively obtains each
  next retry count from the actual completed remaining run. Updating only that
  tile preserves earlier queries; the existing forward loop theorem replays
  the enlarged prefix and the rich finite-run rules obtain the exact next
  suffix. Thus all executed `LoopReplies`, including required producer TMA
  shapes, follow from actual finite completion rather than a caller schedule.
- `completed_loop_reconstruct` reconstructs all remaining iterations through
  `tiles-first`, the exact loop events and full remaining state/event suffix.
  It proves a strict fuel bound, output-entry PC 85 and no pending WGMMA calls.
  It does not assert eventual completion, initialize arbitrary launches or
  identify arbitrary arithmetic replies with the matrix specification.
- `loop_reply_schedules_unique` uses first-success uniqueness with prefix-query
  locality to show that any compatible schedules agree on executed entries.
  Future entries need not agree. A separate generic corollary re-expresses the
  extracted full execution at an independently proved compatible schedule;
  the main existence/reconstruction theorem still takes no schedule premise.
- Tests: eight new public source theorems and ten public test facts, each
  exactly audited. Actual producer and consumer suffixes with three failed
  waits now have whole-loop reconstruction and an exact output/return suffix.
  The producer test retains the full state/event result at its checked
  schedule, PC 85, empty pending ledger and strict fuel bound. Tests reject
  incorrect executed retry entries, check actual per-tile queries, and prove
  a future schedule update preserves full prefix state/events/fuel/queries
  for arbitrary real-valued input state and oracle. That future schedule is
  also compatible while differing as a function, explicitly testing the limit
  of schedule uniqueness. No real-valued state/event equality decider is used.
- Method classification/reuse: engineering source reconstruction using existing
  iteration inversion, finite-run decomposition and accumulator/register
  invariants. The same generic rule is applied to actual producer and consumer
  paths; this is not a new asynchronous ownership protocol or independent
  optimization-method contribution. Nonzero-retry source replay still needs
  resource/control/memory history connections before full launch admission.
- Validation: `/tmp/ptx-loop-reconstruction-full-gate.log` exited zero and ends
  with `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness integration tests, 30 generated AST comparisons, 3552 Lean jobs,
  5628 audited declarations, 5597 environment-resolved public names, all 660
  individually refuted assertions and 30 assembled PTX examples. New logical
  schedule rejections are separate from those unchanged strict assertions.
  Successful locality/reconstruction builds took 1.2/1.3 seconds; the final
  ten-fact test module took 6.2 seconds. These are proof costs, not GPU
  performance. Coverage metadata, scoped whitespace/source scans and all 18
  exact new audit entries pass.
- Development accounting: compile attempts caught implicit query parameters,
  the distinction between `0+i` and definitional reduction, and a prefetch
  predicate's conjunction. A concrete-state test compiler remained active
  with high CPU/memory usage and was explicitly cancelled after 279 seconds;
  it was not assumed terminal because an observation timed out, and that run
  supplies no proof evidence. Moving the same full-state/event rewrite into
  the parameterized compatible-schedule corollary avoided concrete-state
  normalization and checked successfully without raising the heartbeat limit.
  The producer test's conclusion was retained. The old header-control tests
  still have SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 06:39:26 UTC, all 30 hashes current.
  GPU evidence remains 2026-11-05 07:46:53 UTC, with 15 matching source hashes
  and 25 sm_89 cases (24 exact-byte, one completion-only). No Hopper hardware
  IEEE/logits/token-equivalence or speedup evidence is added.
- Remaining: arbitrary initialization/guard/output and complete source
  reconstruction (including the zero-tile path outside this active loop
  theorem); resource/control/memory histories for extracted nonzero retries;
  full-Pre functional/refinement correctness and fully admitted completed-launch
  existence; remaining profiles/allocation/in-flight lifetime, runtime/Iris
  correspondence and general output geometry. All required cases remain partial,
  exact paper 81-form parity is unconfirmed, and the original full goal stays
  active without relaxing its exact-output requirement.
- Goal ledger snapshot at 2026-11-06 06:39:54 UTC: 11,271,212 tokens versus the
  preceding published 11,226,445, a difference of 44,767. Interim tool-reported
  usage, not final billed usage or a goal-completion report.

### 2026-11-06 — Reconstruct complete arbitrary-reply kernel source traces

- Optimization instance: the same two-slot Hopper GEMM with the canonical
  launch parameters/geometry and supported tile-count bound. PTX, generated
  AST, operational/event semantics and exact-output target are unchanged.
  Replies, retry counts, completed-run length and real accumulator values are
  arbitrary in the source reconstruction theorem. No GPU overlap, speedup or
  Hopper hardware execution is measured.
- Concrete previous limitation: whole-loop inversion began at an assumed loop
  invariant and stopped at PC 85. It did not connect arbitrary initial TMA
  replies to that invariant, account for output/return fuel and events, or
  cover the zero-tile path. These gaps prevented classifying arbitrary
  completed candidate traces, even before proving their memory/tensor values.
- `InitialReconstruction` executes the actual expectation/A prefixes and
  derives initial producer A/B payload lengths from finite completion. The
  entire initial-copy segment then executes with arbitrary captured descriptor
  and byte replies, reaching the existing canonical loop-entry state. Entry,
  barrier initialization and zero-test reuse the previous arbitrary-reply
  rules. Consumers do not acquire unused producer reply-size premises.
- `OutputReconstruction` derives the output register frame through arbitrary
  retry loops. The output/return suffix has its exact count, state and events
  by full rich-run completion uniqueness. The complete zero-tile source path
  is proved for every lane and oracle, with its canonical zero accumulators
  and events independent of unused TMA/matrix/completion replies. Source
  completion here remains distinct from physical/runtime observation.
- `KernelReconstruction` composes initial source, extracted whole-loop schedule
  and output. Every finite completed raw run from the initial state at the
  canonical parameters/geometry has exactly the reconstructed instruction
  count, final rich state and full event list. Positive runs additionally
  yield the initial producer shape conditions and every executed `LoopReplies`.
  The zero and positive paths are both covered without assuming a selected
  data oracle, retry schedule or desired matrix value.
- Candidate lifting uses well-formed trace validity and checked lane/geometry
  coverage to obtain each trace's actual canonical context and source run.
  The theorem therefore classifies every trace of any well-formed completed
  candidate, including arbitrary captured replies and trace ordering; it does
  not restrict candidates to `dataCompleteCandidate`. This is source structure
  reconstruction. Arbitrary captured replies still need resource, memory,
  collective/tensor and observer constraints before functional correctness.
- Tests: 18 new public source theorems and ten test facts, each exactly audited.
  The previous three-failure producer loop is now composed with actual entry
  and initial TMA execution into a full kernel source witness and reconstructed
  with its recovered executed retry counts. All zero-tile lanes complete with
  hostile unused matrix/operand/wait/completion and empty TMA replies, and
  arbitrary completed zero runs have unique fuel/state/events. Whole-kernel
  initial short-A/short-B completion claims are logically rejected; the short-B
  mutation preserves A. A full consumer source executes with unused initial
  and prefetch payloads empty. Tests also apply arbitrary-candidate trace
  reconstruction to the arbitrary-real data family and reject post-completion
  padding. Real-valued states/events are never compared by a decider.
- Method classification/reuse: engineering closure using existing arbitrary
  entry rules, successful-TMA inversion, loop frames and finite-run uniqueness.
  The same source rules cover producer/consumer and zero/positive paths, not
  a new asynchronous ownership protocol or independent optimization-method
  contribution. No new semantic axiom, fairness/termination assumption or
  weakening of the numerical target is introduced.
- Validation: `/tmp/ptx-kernel-reconstruction-full-gate.log` exited zero and
  ends with `All verifier checks passed`: 47 Rust tests, Clippy with warnings
  denied, six harness integration tests, 30 generated AST comparisons, 3556
  Lean jobs, 5656 audited declarations, 5625 environment-resolved public names,
  all 660 individually refuted assertions and 30 assembled PTX examples. New
  logical initial-payload rejections are separate from the unchanged strict
  metadata assertions. Successful initial/output/kernel proof builds took
  about 14/1.5/1.4 seconds; the ten-fact test module took 5.2 seconds in the
  full gate. These are proof costs, not GPU performance. Coverage metadata,
  scoped whitespace/source scans and all 28 new audit-entry checks pass.
- Development accounting: compile attempts caught over-unfolding a known
  four-step suffix and a concrete elected-producer Boolean during rewriting.
  Splitting the run explicitly and using the checked producer flag corrected
  them; failed builds are not proof evidence. No heartbeat limit was raised.
  Existing header-control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 06:56:47 UTC, all 30 source hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 matching source
  hashes and 25 sm_89 cases (24 exact-byte, one completion-only). No Hopper
  hardware IEEE/logits/token-equivalence or speedup evidence is added.
- Remaining: connect arbitrary-candidate reconstructed source to actual
  resource/control/memory histories, including nonzero retries, and collective
  tensor arithmetic; full-Pre functional/refinement correctness and fully
  admitted completed-launch existence; remaining profiles/allocation/in-flight
  lifetime, runtime/Iris correspondence and general output geometry/parameters.
  All required cases remain partial; exact paper 81-form parity is unconfirmed.
  The original full goal stays active, with its exact-output requirement intact.
- Goal ledger snapshot at 2026-11-06 06:57:11 UTC: 11,326,807 tokens versus the
  preceding published 11,271,212, a difference of 55,595. Interim tool-reported
  usage, not final billed usage or a goal-completion report.

### 2026-11-06 — Classify arbitrary completed candidates' actual memory accesses

- Optimization instance: the same canonical two-slot Hopper GEMM, with
  arbitrary supported tile counts, lane replies and finite retry schedules.
  PTX, generated program, execution/event semantics and exact-output target
  are unchanged. No GPU overlap, speedup or Hopper hardware result is added.
- Concrete previous limitation: full source reconstruction classified arbitrary
  completed traces, but ordinary-memory and writer-region inventories still
  belonged to the selected data witness. Those inventories could not yet
  justify arbitrary-candidate input immutability or exclude hidden ordinary
  accesses before reasoning about RF, resource histories and tensor values.
- `ReplyInventory` proves ordinary-memory shape and the exact four output-word
  inventory while preserving arbitrary captured accumulator values through
  initialization, failed waits, loop iterations and output. Zero-tile and
  positive paths are both covered. Full source reconstruction lifts the facts
  to every trace and actual event/view of an arbitrary well-formed completed
  candidate at the canonical launch, with the existing tile-count bound.
- `CandidateMemory` excludes non-bulk copies, ordinary reads and ordinary
  shared writes. Every ordinary footprint has its actual lane/output-word
  owner, four-byte size, alignment and output-region bounds. Every shared byte
  writer has actual TMA origin; every global writer is an ordinary source
  writer within `[8192,10240)`. Global bytes outside that interval, including
  canonical inputs and descriptor storage, have no candidate writer. Barrier
  resource state is separate from these byte-access statements. The proofs
  choose no RF/co/history and assume no desired matrix output.
- `positive_complete_any_reply` composes actual initialization, arbitrary-retry
  loop and output execution. `ReplyCandidate` then constructs source-only
  well-formed completed candidates with independent per-lane replies and retry
  schedules, given the source's executed wait/payload conditions. This is not
  memory, resource, native-control, collective or tensor admission.
- Tests: 14 public facts use a full one-tile source candidate with lane retry
  counts 0/1/2 and arbitrary real matrix replies. Exact source output payloads
  retain those arbitrary replies and contain four words per lane. Tests apply
  actual footprint/writer classification, exclude hidden ordinary accesses,
  preserve input/descriptor and adjacent output-guard bytes, and logically
  reject a fabricated ordinary read or input write. This tests source-memory
  structure without accidentally assuming arithmetic correctness. Real states,
  events and payloads are handled by proof/rewrite, not a value decider.
- Method classification/reuse: engineering closure through reconstructed
  source shape, output inventory and existing byte-access inversion. The rules
  cover producer/consumer, zero/positive and heterogeneous-retry source traces;
  they are not a new asynchronous ownership protocol or an independent
  optimization-method contribution. No semantic axiom, eventual-readiness
  premise or relaxation of the numerical target is introduced.
- Validation: `/tmp/ptx-candidate-memory-full-gate.log` exited zero and ends
  with `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness integration tests, 30 generated AST comparisons, 3560 Lean jobs,
  5695 audited declarations, 5664 environment-resolved public theorem names,
  all 660 individually refuted assertions and 30 assembled PTX examples. The
  25 new source/inventory theorems and 14 test facts each have one exact audit
  entry. The new logical rejections are separate from the unchanged strict
  assertion batch. Inventory, writer, source-candidate and test proof builds
  took about 1.1/1.5/4.9/2.1 seconds respectively; these are proof costs, not
  GPU performance. Coverage metadata, audit-entry and source/whitespace scans
  pass.
- Development accounting: failed builds exposed projection normalization,
  ordinary-write case splitting, a redundant tactic after definitional
  equality, and multiline tactic layout. Explicit source projections and case
  branches corrected them. Failed builds are not evidence, and no heartbeat
  limit was raised. Existing header-control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 07:20:15 UTC, all 30 source hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 matching hashes
  and 25 sm_89 cases (24 exact-byte, one completion-only). No Hopper hardware
  IEEE/logits/token-equivalence or performance result is added.
- Remaining: connect arbitrary-candidate source/byte inventories to actual
  resource/control/memory histories, including nonzero retries, and collective
  tensor arithmetic; full-Pre functional/refinement correctness and fully
  admitted completed-launch existence; remaining profiles/allocation/in-flight
  lifetime, runtime/Iris correspondence and general output geometry/parameters.
  All required cases remain partial; exact paper 81-form parity is unconfirmed.
  The original full goal stays active, with its exact-output requirement intact.
  TTGIR integration was discussed as a future input/semantic boundary, with no
  TTGIR implementation or change to this goal's acceptance scope.
- Goal ledger snapshot at 2026-11-06 07:20:24 UTC: 11,458,797 tokens versus the
  preceding published 11,326,807, a difference of 131,990. Interim tool-reported
  usage, not final billed usage or a goal-completion report.

### 2026-11-06 — Derive arbitrary-candidate TMA input values from memory

- Optimization instance: the same canonical two-slot Hopper GEMM, with
  arbitrary supported tile counts, captured replies and independent finite
  retry schedules. Source PTX, generated AST, execution/memory semantics and
  exact-output target are unchanged. No Hopper execution, overlap or speedup
  measurement is added.
- Concrete previous limitation: arbitrary-candidate global immutability did
  not identify the actual TMA descriptor objects, input addresses or payload
  values. Input agreement still came from the selected data witness. Source
  completion alone also permits arbitrary descriptor/payload replies with the
  right lengths, so such replies cannot serve as a correctness premise.
- `CopyGeometry` classifies every actual source-issued TMA copy by its K tile,
  A/B descriptor address, signed coordinates, shared destination and barrier.
  It excludes copies from initialization/output and the complete zero-tile
  path, and traverses arbitrary waits, iterations and reconstructed completed
  traces. Descriptor/payload values, query indices and retry counts remain
  arbitrary. Coordinate normalization uses the existing supported tile bound.
- `UnifiedImmutable` supplies reusable immutable-byte taint/eligibility and
  RF/value rules for the full ordinary/non-bulk/TMA/native inventory. A read
  at an immutable location must select initial memory rather than a fabricated
  writer. Tensor-map identity follows from its actual descriptor read and
  independently stored symbolic tensor-map object. These opaque tagged objects
  are not physical CUDA encodings; host encoding/publication remain external
  correspondence obligations.
- Eligibility explicitly retains the existing model's global exclusion of
  mixed-size races. Local immutability alone does not prove that global
  property. It is a hypothesis of these intermediate rules, not a new semantic
  axiom, weakened acceptance target or proof of arbitrary-candidate race
  freedom. Removing caller obligations still requires the remaining full-Pre
  integration. Memory conditions alone, whose agreement is guarded by
  eligibility, are not claimed sufficient.
- `CandidateInputs` combines actual copy geometry, global immutability,
  independent initial maps/bytes and causal memory agreement. Every admitted
  descriptor matches the appropriate initial A/B object. All transfer offsets
  lie in bounds and read global addresses at or above 65536, outside output.
  Actual source-derived payload lengths and immutable read agreement then
  determine every payload byte. No zero-fill, chosen candidate, desired matrix
  result, selected retry schedule or caller-provided eligibility is assumed.
  Resource histories, shared publication, native operands and tensor arithmetic
  remain separate obligations.
- Tests: 15 public facts construct full one-tile source-only candidates with
  heterogeneous lane retries, arbitrary A/B global bases, arbitrary real TMA
  payloads and independent arbitrary matrix replies. They prove well-formed
  source/completion and actual initial A/B issue identities. Under the stated
  memory/race conditions, A/B bases and real payload values are forced to the
  independent initial input; wrong bases/payloads and fabricated input RF are
  logically rejected. The generic rules also derive input agreement from the
  independently constructed arbitrary-data memory witness for every supported
  tile count, providing positive nonvacuity evidence. A completed two-tile
  producer with three failed waits exercises copy classification; actual
  zero-tile copies are rejected. No real state/event/payload equality uses a
  decider, and source-only hostile candidates receive no full memory/tensor
  admission claim.
- Method classification/reuse: engineering closure using existing immutable
  input rules, actual byte-access inversion and arbitrary-reply source
  reconstruction. The full-inventory rules serve both hostile heterogeneous
  source tests and the independent arbitrary-data memory witness. This is not
  a new ownership protocol or a measured optimization-method contribution.
- Validation: `/tmp/ptx-candidate-inputs-full-gate.log` exited zero and ends with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied, six
  harness integration tests, 30 generated AST comparisons, 3564 Lean jobs,
  5729 audited declarations, 5698 environment-resolved public theorem names,
  all 660 individually refuted assertions and 30 assembled PTX examples. The
  19 new public proof rules and 15 test facts each have one exact audit entry.
  New logical rejections are separate from the unchanged strict assertion
  batch. Generic immutable, geometry, input and test module builds took about
  1.2/1.2/1.5/4.1 seconds respectively; these are proof costs, not GPU timing.
  Coverage metadata, scoped whitespace/source scans and exact audit entries
  pass. All required cases remain partial.
- Development accounting: failed builds caught hidden base-node/resolver
  arguments, event membership disjunctions, unnormalized location projections,
  free variables in closed decisions and rewrite patterns. Explicit node and
  resolver parameters, source projections, typed byte-read facts and local
  normalized equalities corrected them; failed builds are not proof evidence.
  No heartbeat limit was raised. One build command did not start because
  automatic permission review timed out; the tool-authorized single retry
  started successfully. Existing header-control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 07:40:00 UTC with all 30 source
  hashes current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 matching
  source hashes and 25 sm_89 cases (24 exact-byte, one completion-only). No
  Hopper hardware IEEE/logits/token-equivalence or performance evidence is
  added.
- Remaining: arbitrary-candidate global race exclusion and resource/control
  histories, including nonzero retries; actual shared-memory publication and
  native reuse/RF phases; collective tensor arithmetic and final observer;
  full-Pre functional/refinement correctness and fully admitted completed-launch
  existence; remaining profiles/allocation/in-flight lifetime, runtime/Iris
  correspondence and general output geometry/parameters. Exact paper 81-form
  parity remains unconfirmed. The original full goal remains active with its
  exact-output requirement intact.
- Goal ledger snapshot at 2026-11-06 07:40:15 UTC: 11,584,612 tokens versus the
  preceding published 11,458,797, a difference of 125,815. Interim tool-reported
  usage, not final billed usage or a goal-completion report.

### 2026-11-06 — Derive arbitrary-candidate mixed-size exclusion from descriptors

- Optimization instance: the same canonical two-slot Hopper GEMM with arbitrary
  supported tile counts, captured values and finite per-lane retry schedules.
  Source PTX, generated AST, execution/memory semantics and exact-output target
  are unchanged. No Hopper execution, prefetch-overlap or speedup is measured.
- Concrete previous limitation: the arbitrary-candidate input-value rules
  required a separate global no-mixed-size-race premise. Footprint-based
  exclusion existed only for the selected one-stage/repeated data witnesses,
  so it could not discharge that premise for arbitrary completed candidates
  satisfying the existing descriptor component.
- `HopperStageRegionRules` factors the region-overlap arithmetic out of the
  one-stage and constructed repeated proofs. Both existing clients now use
  the same rule with their original theorem signatures and source inventories.
  A shared byte or aligned output word overlapping any admitted region has
  exactly the same complete footprint. Input bytes and descriptor objects
  occupy separate global regions. The rule is also used by the new arbitrary
  candidate proof; this is proof reuse, not a new ownership protocol.
- `CandidateRegions` derives actual source-event CTA identity and TMA shared
  write footprints from source well-formedness. Complete source/copy geometry
  classifies ordinary output words and descriptor footprints. Under the
  existing descriptor agreement, all TMA reads lie in the global input region;
  every native representative read is a shared byte. All unified writers and
  overlapping accesses are covered, including ordinary, non-bulk, TMA and
  native nodes. Consequently mixed-size races are excluded for arbitrary RF,
  histories and cluster scope without a caller race, payload, arithmetic or
  memory-value premise. Same-size data races are not thereby excluded.
- `CandidateAdmission` removes a separate no-mixed-size premise from immutable
  input RF/value and payload closure. Its TMA-component constructor derives
  payload agreement from source/completion, descriptor agreement and causal
  memory, while retaining actual history validity and control acyclicity.
  Existing TMA components imply the derived mixed-size exclusion. Descriptor
  agreement is retained as the existing semantic component; it has not been
  derived unconditionally from causal memory alone. There is no circular
  attempt to establish initial descriptor values through eligibility before
  mixed-size exclusion, no changed admission semantics and no full-Pre claim.
- Tests: 15 public facts establish descriptor admission directly for full
  source-complete one-tile candidates with heterogeneous lane retries and
  arbitrary real payload/matrix replies. Mixed-size exclusion then holds for
  arbitrary RF/histories/cluster; actual input locations have no writer.
  Wrong payload and fabricated input RF are rejected without caller race
  hypotheses. The independent arbitrary-data source/memory/control witnesses
  reconstruct TMA components with the new constructor for all supported tile
  counts, including zero, without invoking their old payload theorem.
- Descriptor-boundary counterexample: a full source-only candidate uses A's
  global base 8192. Its actual TMA byte read and actual output source store
  both begin at 8192, with footprint sizes one and four. They are unequal
  complete footprints, while source well-formedness/completion still hold.
  The candidate fails descriptor admission. This proves an actual overlap and
  the need to retain the descriptor boundary; it is not falsely labeled a
  full data-race witness or an admitted memory/collective execution. Real
  state/event/payload equalities are never decided computationally.
- Method classification/reuse: engineering closure through exhaustive source
  inventories, footprint inversion and the existing mixed-size rule. Shared
  region arithmetic is reused in one-stage, selected repeated and arbitrary
  candidate proofs. This adds neither a semantic axiom nor a desired result,
  resource completion or lifetime premise disguised as a proof conclusion.
- Validation: `/tmp/ptx-candidate-admission-full-gate.log` exited zero and ends
  with `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness integration tests, 30 generated AST comparisons, 3568 Lean jobs,
  5757 audited declarations, 5726 environment-resolved public theorem names,
  all 660 individually refuted assertions and 30 assembled PTX examples. All
  13 new proof rules and 15 test facts have exact audit entries. New logical
  rejections are separate from the unchanged strict assertion batch. Shared
  region, candidate region, admission and test builds took approximately
  1.3/1.5/1.4/1.8 seconds respectively; these are proof costs, not GPU timing.
  Coverage metadata and scoped source/whitespace/exact-audit scans pass.
- Development accounting: failed builds caught substitution of footprint
  witness names, unconstrained frame binders, a folded source alias, monadic
  access normalization and graph-kind rewrite projections. Explicit types and
  source aliases, footprint reduction and typed equalities corrected them.
  Failed builds are not proof evidence, and no heartbeat limit was raised.
  A file-add request timed out in automatic permission review; a read-only
  check confirmed it had not changed the files, and the tool-authorized single
  retry succeeded. No approval remains pending. Existing header-control tests
  retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 07:56:59 UTC, all 30 source hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 matching hashes
  and 25 sm_89 cases (24 exact-byte, one completion-only). No Hopper hardware
  IEEE/logits/token-equivalence or performance evidence is added.
- Remaining: arbitrary-candidate resource/control histories, including nonzero
  retries; actual shared publication and native reuse/RF phases; collective
  tensor arithmetic and final observer; full-Pre functional/refinement
  correctness and fully admitted completed-launch existence; remaining
  profiles/allocation/in-flight lifetime, runtime/Iris correspondence and
  general output geometry/parameters. Mixed-size exclusion is now closed under
  the existing descriptor component, not for arbitrary unconstrained source
  descriptors. All required cases remain partial and exact paper 81-form
  parity remains unconfirmed. The full goal remains active without relaxing
  its exact-output requirement.
- Goal ledger snapshot at 2026-11-06 07:57:13 UTC: 11,646,123 tokens versus the
  preceding published 11,584,612, a difference of 61,511. Interim tool-reported
  usage, not final billed usage or a goal-completion report.

### 2026-11-06 — Reconstruct arbitrary-retry source collectives and wait order

- Optimization instance: the same canonical two-slot Hopper GEMM with arbitrary
  supported tile counts, captured replies and independent per-lane finite
  retry schedules. PTX, generated AST, operational/event/memory semantics and
  the exact-output target are unchanged. No Hopper execution, overlap or
  speedup is measured.
- Concrete previous limitation: source-indexed waits and collectives used
  event formulas for the selected zero-retry data witness. Failed waits shift
  every later event, and different lanes can have different shifts. Source
  completion/shape reconstruction did not yet recover actual per-tile
  collectives or post-wait source order for every completed candidate.
- `ReplyIndices` derives prelude/iteration lengths, prefix index retention,
  and failed/successful wait and MMA locations for arbitrary replies/retries.
  Complete event positions use actual initial/loop-prefix lengths. Failed
  attempt indices precede the successful wait at the recovered retry count;
  successful waits precede their MMA. These are finite source-event facts,
  with no eventual-readiness, fixed schedule or resource observation premise.
- `ReplyCollective` preserves arbitrary captured input/output/operand values
  while proving lane, A/B descriptor, ordinal/group and destination shape.
  Every tile's source mark is PC 77, sequence `4*tile+1`, warpgroup zero,
  independent of each lane's retries or oracle. Call cohorts do not assert
  matching operand values, tensor arithmetic or full native-control admission.
- `CandidateCollective` extracts actual trace/oracle/retry witnesses for every
  lane from any well-formed completed positive launch, using checked coverage
  and finite-completion reconstruction. Every executed tile then has an actual
  source-indexed 128-lane collective with matching marks and call shape.
  No selected data candidate, prescribed schedule or desired arithmetic reply
  is assumed. Zero-tile source reconstruction remains covered by the earlier
  complete zero path; no zero-tile MMA collective is invented.
- Actual candidate events establish successful-wait-before-MMA generic source
  order. For any history, scope and copy, an actual failed wait cannot be a
  `CompletionObserved` endpoint: valid observation necessarily identifies an
  actual successful parity wait. The TMA-ready rule now derives the source
  collective and post-wait order, while retaining actual per-lane completion
  observations and matching transfer/operand byte locations as explicit
  obligations. It does not derive observations from arbitrary histories, add
  blanket memory edges or equate source order with memory visibility.
- Tests: 14 public facts use a complete source candidate with independent lane
  retries 0/1/2 and arbitrary real matrix replies. They check actual failed and
  successful waits/MMA events, all lane coverage, matching marks despite
  different event serials, post-wait source order, and failed-wait observation
  rejection for arbitrary histories/copies/scopes. Captured matrix outputs
  remain the arbitrary test parameter, explicitly separating source structure
  from arithmetic correctness. The universal reconstruction is also applied
  to the independent arbitrary-data source for every executed tile. A full
  two-tile producer with three failed waits has actual success/MMA events at
  11/16. Closed decisions only check normalized natural-number metadata;
  real states/events/payloads are handled by proof and rewriting.
- Method classification/reuse: engineering closure through existing arbitrary
  source reconstruction, loop/call bookkeeping and the resource observation's
  actual-wait rule. The same indexing/cohort rules serve heterogeneous source
  replies, the full retrying producer and the independent data family. This is
  not a new asynchronous ownership method, native ISA admission or measured
  optimization contribution.
- Validation: `/tmp/ptx-candidate-collective-full-gate.log` exited zero and ends
  with `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness integration tests, 30 generated AST comparisons, 3572 Lean jobs,
  5798 audited declarations, 5767 environment-resolved public theorem names,
  all 660 individually refuted assertions and 30 assembled PTX examples. Each
  of the 27 new proof rules and 14 test facts has one exact audit entry. New
  logical rejections are separate from the unchanged strict assertion batch.
  Index, cohort, candidate and test builds took approximately 1.5/1.1/1.4/1.8
  seconds after normalization fixes; these are proof costs, not GPU timings.
  Coverage metadata, scoped source/whitespace and exact-audit scans pass.
- Development accounting: failed builds caught list association/subtraction,
  untyped event indices, hidden bookkeeping projections, a missing native-order
  import and CTA projection normalization. CPU-heavy library/diagnostic
  elaborations were deliberately stopped only after verifying their live
  processes; independent prefix builds localized the cohort-constructor cost.
  Typed call-count rewriting and explicit per-field cohort tactics preserved
  the theorem while reducing the final build to 1.1 seconds. Stopped or failed
  builds are not proof evidence. No heartbeat limit was raised and no stopped
  process was treated as successful. Existing header-control tests retain
  SHA-256 `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 08:24:52 UTC with all 30 hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 matching hashes
  and 25 sm_89 cases (24 exact-byte, one completion-only). No Hopper hardware
  IEEE/logits/token-equivalence or performance evidence is added.
- Remaining: derive actual resource/control phase/lifetime observations for
  arbitrary completed candidates and nonzero retries; connect shared
  publication and native reuse/RF phases; collective tensor arithmetic and
  final observer; full-Pre functional/refinement correctness and fully admitted
  completed-launch existence; remaining profiles/allocation/in-flight lifetime,
  runtime/Iris correspondence and general output geometry/parameters. Source
  collective reconstruction is now available, but complete native control and
  tensor admission remain open. All required cases remain partial, exact paper
  81-form parity remains unconfirmed, and the original goal stays active with
  its exact-output requirement intact.
- Goal ledger snapshot at 2026-11-06 08:25:12 UTC: 11,743,617 tokens versus the
  preceding published 11,646,123, a difference of 97,494. Interim tool-reported
  usage, not final billed usage or a goal-completion report.

### 2026-11-06 — Restore actual completion observations through failed-wait erasure

- Optimization instance: the same double-buffer source and its existing
  one-tile 128-lane heterogeneous-retry fixture. The resource/publication
  witness permits an arbitrary captured real matrix reply; it is not a tensor
  correctness witness for that reply. PTX, generated AST, operational/resource
  semantics and the exact-output target are unchanged. No Hopper execution,
  overlap or speedup is measured.
- Concrete previous limitation: arbitrary-retry source waits/collectives were
  located, but publication still needed caller-provided completion
  observations. The selected zero-retry resource histories could not account
  for actual failed-wait entries, shifted history positions or their protocol
  effects. Dropping those entries without a checked correspondence would lose
  original inventory exhaustiveness and could admit invalid pre-init waits.
- `MbarrierRetries` proves that an executed failed wait preserves a live
  resource object, successful runs survive failed-wait erasure, and insertion
  is valid at an explicitly live prefix. The existing model permits false
  replies even after completion; this overapproximation is preserved. False
  waits before initialization or after invalidation still reject. Erasure is
  not an unconditional equivalence of admitted operation lists.
- `TmaRetryErasure` maps retained entries to their actual filtered-prefix
  positions without changing origins. For arbitrary admitted finite histories,
  retained protocol prefixes, initialization/lifetime counts, phase stamps
  and notification-to-successful-wait observations agree before/after erasure.
  A rule restores `CompletionObserved` only with the original actual
  `HistoryValid`, matching endpoints/order and scope. The filtered list is not
  asserted exhaustive for the original candidate, and no resource edge is
  granted merely from successful erasure or history ordering.
- `RetryResourceView` proves a compact resource/control projection of the
  one-tile source for arbitrary failed-wait counts and arithmetic/payload
  replies at its explicit initial descriptor profile. It uses the existing
  generation-preservation rules to avoid expanding arithmetic state. The
  compact trace preserves actual source slots, barriers, CTA metadata and TMA
  metadata, while discarding payloads. It is not claimed source-produced,
  memory-admitted or physically encoded as a CUDA tensor map.
- The source-matched fixture has 127 failed and 128 successful waits. Closed
  resource-only metadata checks establish uniqueness, exact inventory
  permutation, thread-local source order and protocol execution for its two
  actual gate histories: 260 entries in the active gate and two in the unused
  gate. The proved erasure correspondence transfers these records to the
  actual source candidate for every captured real matrix reply. This supplies
  resource-history witnesses; it does not grant native arithmetic correctness
  to arbitrary replies or a full combined execution witness.
- Actual A/B completion observations for every lane are restored through the
  generic retry-erasure rule. Combining them with source-reconstructed
  collectives, actual transfer/operand locations and post-wait source order
  proves native TMA-ready publication and byte-order edges for every operand,
  with no caller observation premise in this fixture. This is model-relative
  resource/publication evidence for one tile. Arbitrary multi-tile/history
  construction, combined control acyclicity, reuse/RF and tensor/observer
  correctness remain separate obligations.
- Tests: 33 public metadata/source/protocol facts. They include actual gate
  admission and all-lane A/B publication, an erased list whose protocol passes
  but which fails original `HistoryValid` because actual failed waits are
  missing, and pre-init/post-invalidation counterexamples to unconditional
  insertion/reflection. A separate raw two-lifetime protocol keeps an old
  notification rejected after reinitialization while the current notification
  remains observed, both before and after erasure. These raw lifetime fixtures
  are not mislabeled source inventories. Real states/payloads are handled by
  proof/rewriting; closed decisions check only the proved compact metadata or
  resource protocol, never real-value equality.
- Method classification/reuse: engineering closure using the existing
  failed-wait step, list-prefix/filter correspondence and actual resource
  observation rules. The generic transformation is applied to the actual
  nonzero-retry source witness and the independent reinitialization protocol
  boundary tests. This is not a new ownership protocol, independent optimized
  kernel result or measured agentic-method contribution. No semantic axiom,
  eventual-readiness premise or weakened numerical target is introduced.
- Validation: `/tmp/ptx-retry-erasure-full-gate.log` exited zero and ends with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied, six
  harness integration tests, 30 generated AST comparisons, 3578 Lean jobs,
  5850 audited declarations, 5819 environment-resolved public theorem names,
  all 660 individually refuted assertions and 30 assembled PTX examples. All
  19 new proof rules and 33 test facts have exact audit entries. New logical
  rejections are separate from the unchanged strict assertion batch. Generic
  observation erasure and compact-view builds took about 1.9/4.3 seconds;
  finite metadata checks took 139 seconds, and derived source-publication and
  lifetime tests took about 1.5/1.2 seconds. The stable metadata checks are in
  a separate cached module. These are proof/check costs, not GPU timings.
  Coverage metadata and scoped source/whitespace/exact-audit scans pass.
- Development accounting: failed builds caught protocol-result substitution,
  filter-map/filter-filter normalization, missing structural decidability for
  the full history record, endpoint identity normalization and implicit
  observation indices. Direct equality of the fully expanded rich resource
  view exceeded the existing two-million-heartbeat budget; explicit event
  projection plus generation frames proves the same correspondence without
  raising that budget. History records check their four fields separately.
  Failed builds are not evidence. Existing header-control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 09:02:50 UTC with all 30 hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 matching source
  hashes and 25 sm_89 cases (24 exact-byte, one completion-only). No Hopper
  hardware IEEE/logits/token-equivalence or performance evidence is added.
- Remaining: construct/reconstruct actual resource/control phase histories and
  completion observations for arbitrary multi-tile candidates and retries,
  including reused slots; connect native reuse/RF, collective tensor arithmetic
  and the final observer; full-Pre functional/refinement correctness and fully
  admitted completed-launch existence; remaining profiles/allocation/in-flight
  lifetime, runtime/Iris correspondence and general output geometry/parameters.
  The finite one-tile resource/publication witness does not substitute for
  these universal obligations. All required cases remain partial, exact paper
  81-form parity remains unconfirmed, and the original full goal stays active
  with its exact-output requirement intact.
- Goal ledger snapshot at 2026-11-06 09:03:33 UTC: 11,855,178 tokens versus the
  preceding published 11,743,617, a difference of 111,561. Interim tool-reported
  usage, not final billed usage or a goal-completion report.


### 2026-11-06 — Actual multi-tile prefetch identities with arbitrary retries

- Instance: the existing Hopper double-buffer GEMM source, including initial
  transfer, prefetch into the other arena, and reuse of the original arena.
  The prior arbitrary-retry source family located waits and native MMA calls;
  old repeated-copy identities were tied to zero retries. A failed wait moves
  later expectation/issue indices and consumes an oracle query. Physical
  destination equality on reuse does not identify the same transfer.
- Engineering baseline: `HopperDoubleBufferReplyPrefetch` proves thirteen
  source rules using actual event prefixes. Each tile has an expectation and
  two distinct source copy identities, with its captured descriptor/payload
  and actual query counter retained. Rules cover initial and prefetched tiles,
  source expectation/A/B order, iteration-prefix growth, and B-issue-before-
  producer-successful-wait order. Existing completed-candidate reconstruction
  supplies the source family, so the candidate projection rules do not assume
  guessed event indices or add completion/visibility premises.
- Reuse evidence: the same parameterized indexing rule handles arbitrary
  finite retries and tile counts. Eleven test facts exercise a source-complete
  three-tile/128-lane candidate with heterogeneous nonzero waits on every tile,
  two arenas, and distinct transfer IDs at the same reused address. They check
  actual expectation/copy lookup, shifted query/source indices and reject an
  old zero-retry issue index, which now points at the expectation. Captured
  matrix values remain arbitrary reals. The closed wait-schedule metadata
  check uses `decide`; rich source correspondence uses proved rules, without
  real-valued event/state equality decisions. This is not a new asynchronous
  ownership protocol or an independent optimized-kernel research result.
- Development: Lean caught missing index type annotations, append-prefix
  normalization, reconstruction of source-ID thread fields, and incorrect
  record type/field names in tests. The first field-fix script used a wrong
  relative directory and changed no file; the field was corrected explicitly.
  Failed builds are not passing evidence. All proofs retain the existing
  two-million-heartbeat limit, with no semantic axiom or proof placeholder.
- Remaining: these source rules do not give multi-tile HistoryValid records,
  completion observations, control admission or native reuse/RF closure.
  Arbitrary-candidate collective tensor arithmetic and final observer,
  full-Pre functional refinement and admitted completed-launch existence,
  broader profiles/allocation/in-flight lifetime and runtime/Iris connection
  remain required. All required cases stay partial and exact paper 81-form
  parity remains unconfirmed. No TTGIR frontend, new GPU execution, performance
  measurement, IEEE/logits/token-equivalence result or numerical relaxation is
  introduced. The full goal remains active.

- Validation: `/tmp/ptx-reply-prefetch-full-gate.log` exited zero and ends with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated PTX-to-Lean comparisons, 3580 Lean jobs,
  5874 audited declarations and 5843 environment-resolved public theorem names,
  all 660 individually refuted strict assertions, and 30 assembled PTX examples.
  All thirteen new rules and eleven test facts have exact audit entries.
  These new source tests do not change the strict assertion count. Scoped
  whitespace/source scans and coverage metadata validation pass. Existing
  header-control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 09:19:22 UTC, with all 30 source
  hashes current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 matching
  source hashes and 25 sm_89 cases (24 exact-byte, one completion-only).
  No new Hopper hardware execution evidence is claimed.
- Goal ledger snapshot at 2026-11-06 09:19:46 UTC: 11,960,708 tokens versus the
  preceding published 11,855,178, a difference of 105,530. Interim tool-reported
  usage, not final billed usage or a goal-completion report. The next step is
  to construct/reconstruct actual multi-phase resource histories using these
  identities and close completion observations across slot reuse.


### 2026-11-06 — Construct actual-origin multi-phase retry histories

- Instance and limitation: the Hopper double-buffer GEMM source with arbitrary
  finite per-lane/per-tile retries, prefetch into alternating arenas and slot
  reuse. Prior source indexing located all issue/wait IDs, but the repeated
  resource/observation construction still omitted failed waits. One-tile
  erasure/publication witnesses did not cover reused resource phases.
- Method: `ReplyResourceEndpoints` proves actual initialization/invalidation
  and notification identities from the rich source family. Notification byte
  counts use the existing descriptor admission, including the variable B
  input base `dataBBase tiles`; it is not replaced with the finite fixture's
  fixed 131072 base. `RetryPhases` retains each actual failed/successful wait
  and copy identity. Protocol execution is proved for arbitrary finite phase
  counts, and every constructed entry is an actual source or notification
  resource under existing descriptor admission. `RetryPhasePrefixes` derives
  variable-length prefix positions without treating source serial numbers as
  resource-history indices. `RetryObservations` computes lifetime/phase stamps
  and both A/B observations for every lane, rejects other-phase notifications,
  and combines this with completed-candidate source reconstruction.
- Reuse: one parameterized construction covers both arenas, first reuse and
  further parity wrap. The full phase number distinguishes old notifications
  even when old/current parity agrees. This is an engineering baseline built
  from the existing mbarrier execution and actual-origin source rules, not a
  new ownership/synchronization protocol or independent optimized-kernel
  research contribution. No eventual-completion or new semantic assumption is
  added. Source completion and descriptor admission remain explicit premises.
- Tests/proofs: sixteen facts exercise the source-complete three-tile fixture
  with nonzero heterogeneous retries, actual resource lookup/notification
  identities, both arenas, 1030/516-entry histories, failed-wait counts
  255/383/511, current A/B observations and old A/B rejection. A separate
  generic five-tile source-family fact checks old-phase rejection despite
  repeated parity. Every fixture history entry belongs to the actual resource
  inventory; the converse/permutation is not asserted. Finite numeric metadata
  is separate from source and protocol proofs. Rich values stay arbitrary
  reals; no real-state/event equality decider is introduced.
- Development: type/append normalization, nested `ofFn` membership, false-wait
  filtering and CTA projections were corrected from Lean feedback. Direct
  definitional comparison of thousand-entry rich histories exceeded the
  unchanged two-million-heartbeat limit. A proved failed-entry length/schedule
  sum correspondence and phase-length recursion reduced metadata checking to
  closed integer counts; the final combined test module builds in about 2.1
  seconds. Source-prefix and observation modules build in about 1.4/1.2
  seconds. Failed builds are not verification evidence; no budget increase,
  placeholder proof or numerical relaxation is used.
- Remaining: unique origins, exhaustive inventory permutation, source ordering
  and control admission must still be proved for these constructed multi-tile
  histories. These results do not yet give HistoryValid/CompletionObserved or
  native publication for them, and do not prove observations for all arbitrary
  admitted histories. Native reuse/RF, tensor arithmetic and final observer,
  full-Pre functional/refinement correctness and fully admitted completed-launch
  existence, broader profiles/allocation/in-flight lifetime and runtime/Iris
  correspondence remain required. All required cases stay partial; exact
  paper 81-form parity is unconfirmed. No TTGIR implementation, new GPU
  execution, performance result or IEEE/logits/token-equivalence claim is added.

- Validation: `/tmp/ptx-multiphase-retries-full-gate.log` exited zero and ends
  with `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated PTX-to-Lean comparisons, 3585 Lean jobs,
  5941 audited declarations and 5910 environment-resolved public theorem names,
  all 660 individually refuted strict assertions and 30 assembled PTX examples.
  All 51 new rules and 16 test facts have exact audit entries. Source/whitespace
  scans and coverage metadata validation pass; the strict assertion batch is
  unchanged. Existing header-control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 09:40:13 UTC, all 30 source hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 matching source
  hashes and 25 sm_89 cases (24 exact-byte, one completion-only). No new Hopper
  hardware execution or GPU performance evidence is added.
- Goal ledger snapshot at 2026-11-06 09:40:27 UTC: 12,049,202 tokens versus the
  preceding published 11,960,708, a difference of 88,494. Interim tool-reported
  usage, not final billed usage or a goal-completion report. The original full
  goal remains active. Next: prove actual-origin uniqueness, resource inventory
  exhaustiveness/permutation and source ordering for the retry histories, then
  use HistoryValid to derive admitted completion observations/publication and
  connect control/memory/native arithmetic and the final observer.


### 2026-11-06 — Admit exhaustive, unique and source-ordered retry histories

- Instance: the existing Hopper double-buffer GEMM with arbitrary finite
  per-lane/per-tile retries and alternating/reused slots. The previous phase
  protocol and computed observations lacked HistoryValid's inventory,
  multiplicity and source-order fields; they were not yet admitted completion
  observations. Those constructed-history obligations are now proved.
- Classification: `RetryResourceCases` classifies all failed/successful waits
  and the three possible prefetch resource positions in an arbitrary
  iteration. Non-resource compute/advance events are excluded structurally.
  `RetryResourceTraceCases` extends this through initialization, arbitrary loop
  prefixes, output/invalidation and every actual candidate thread. The
  classification retains captured descriptor/payload replies and actual IDs;
  it assumes neither selected histories nor guessed retry counts.
- Inventory and multiplicity: `RetryResourceMembership` proves both membership
  directions and that no resource exists outside the two gates.
  `RetryResourceIdentities` proves strictly increasing tile/source/copy index
  ranges, preserving lane and attempt identity. `RetryResourceUnique` proves
  per-phase and full-history entry uniqueness, then origin uniqueness using
  actual resource soundness. Both membership directions plus uniqueness give
  an actual inventory permutation, rather than only set membership equality.
- Source order: the generic `TmaSourceOrder` rule turns pairwise forward source
  order plus origin uniqueness into the existing SourceOrder definition.
  `RetryResourceOrder` derives wait/iteration source intervals, within-phase
  order, cross-phase separation and endpoints. Arbitrary finite waits change
  indices without changing this order. This rule does not grant a GPU memory
  happens-before relation, proxy visibility or control acyclicity.
- Admission: `RetryResourceAdmission` combines all four HistoryValid fields at
  both gates, admits empty histories outside the gates, and derives A/B
  CompletionObserved for every executed tile and all 128 lanes. Any completed
  well-formed positive candidate at the canonical launch, with the existing
  descriptor admission and tile bound, yields such a constructed family.
  Descriptor admission remains explicit; no new readiness, ghost notification
  or control/memory premise is substituted for the proved history fields.
- Tests/proof boundary: thirteen facts build a source-complete three-tile
  fixture with nonzero heterogeneous retries on every tile. Its B descriptor
  uses `dataBBase 3`, and its full descriptor agreement is proved from the
  exhaustive issue classification. All resource histories, inventory
  permutations, origin uniqueness, source order and A/B completion observations
  are checked for arbitrary captured real matrix values. Rejections cover
  erasing actual failed waits, duplicate initialization, reversed forward
  source order and a reversed two-entry SourceOrder history. These tests do
  not assert input-memory/descriptor-byte agreement, causal RF/co, native
  control, tensor arithmetic or final output correctness. The prior fixture
  with a fixed 131072 B base is still only its documented source witness.
- Development: Lean feedback identified append/Bool normalization, source-ID
  thread substitution, opaque indexed dependency elimination and finite-copy
  wrapper inversion. Explicit record equalities and index intervals solve
  these without increasing the existing two-million-heartbeat budget.
  Classification/membership, uniqueness/order/admission and the test module
  build in about 1.2–1.6 seconds each. Failed builds are not verification
  evidence. These are proof-check costs, not GPU timings or optimization gains.
- Reuse/research status: source intervals and the generic pairwise rule are
  reused across failed/successful waits, both arenas and arbitrarily repeated
  phases. This is a proved engineering baseline for the existing resource
  model, not a new ownership/synchronization protocol or independent optimized
  kernel result. No semantic axiom, eventual-completion assumption or weakened
  numerical requirement is added.
- Remaining: characterize observations for arbitrary admitted histories, prove
  combined control acyclicity for the new constructed histories, connect
  native publication/reuse/RF, tensor arithmetic and the final observer, and
  prove full-Pre functional/refinement correctness plus fully admitted completed
  execution existence. Broader profiles/allocation/in-flight lifetime and
  runtime/Iris correspondence remain required. All required cases remain
  partial and exact paper 81-form parity is unconfirmed. No new GPU execution,
  performance evidence, TTGIR frontend or IEEE/logits/token-equivalence result
  is claimed. The original full goal remains active.

- Validation: `/tmp/ptx-retry-resource-admission-full-gate.log` exited zero and
  ends with `All verifier checks passed`: 47 Rust tests, Clippy with warnings
  denied, six harness tests, generated PTX-to-Lean comparisons, 3594 Lean jobs,
  6020 audited declarations and 5989 environment-resolved public theorem names,
  all 660 individually refuted strict assertions and 30 assembled PTX examples.
  All 66 new rules and 13 test facts have exact audit entries. New resource
  rejections are separate from the unchanged strict assertion batch. Source,
  exact-audit and whitespace scans and coverage metadata validation pass.
  Existing header-control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 10:12:58 UTC, all 30 source hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 matching source
  hashes and 25 sm_89 cases (24 exact-byte, one completion-only). No new Hopper
  hardware execution or GPU performance evidence is added.
- Goal ledger snapshot at 2026-11-06 10:13:18 UTC: 12,164,066 tokens versus the
  preceding published 12,049,202, a difference of 114,864. Interim tool-reported
  usage, not final billed usage or a goal-completion report. The full original
  goal remains active. Next: connect these admitted completion observations to
  actual native publication and reused-byte RF, establish combined control
  acyclicity and tensor/observer correctness, and close full-Pre refinement and
  admitted completed execution existence without adding unproved assumptions.


### 2026-11-06 — Connect retry histories to native byte publication and reuse

- Instance/limitation: the existing Hopper double-buffer GEMM with arbitrary
  finite heterogeneous retries, alternating slots and repeated use of the same
  bytes. The prior unit admitted all resource histories and completion
  observations, but actual TMA-to-native operand publication and native
  completion/reuse components still relied on the zero-retry data family.
- Locations/publication: `RetryNativeLocations` derives actual A/B descriptor
  snapshots from existing descriptor admission, preserves their real targets,
  and matches every native operand byte to its source TMA write location.
  `RetryNativePublication` combines those locations, actual source collectives,
  admitted per-lane transfer observations and wait-before-MMA source order to
  derive TmaReady, NativePublished and ByteOrder. The original source family
  retains arbitrary descriptor/payload/captured arithmetic replies and retry
  schedules. The completed-candidate constructor derives publications for
  every executed tile under the existing source and descriptor premises.
- Actual writer bytes: the reusable `UnifiedNativeWriter` rule derives byte
  existence from the actual source-produced copy and its payload-length rule.
  Captured operand agreement is not used as a writer-existence assumption and
  is not concluded from this publication rule. It remains a memory/RF duty.
- Native completion/reuse: `RetryNativeCompletion` derives real wait-group
  source IDs, dynamic query indices, marks and group counts for every lane;
  wait-zero completion follows the existing source semantics and checkpoint
  invariant. `RetryNativeReuse` proves that any later same-slot tile is at
  least two tiles ahead. Its A/B issues are source-after the producer lane's
  actual existing native wait, yielding NativeReuse and reused-byte ByteOrder
  through that lane's completed collective. No synchronization is inserted.
  This does not prove cross-lane CTA/native/control legality or full launch
  consistency; those admission fields remain separate.
- Tests/proofs: fourteen facts instantiate the source-complete,
  descriptor-admitted three-tile fixture with nonzero heterogeneous retries.
  They cover all operand byte publications and actual writer existence, every
  lane's native completion and read-to-wait byte edge, shifted producer and
  consumer native-wait IDs, wait-before-reuse A/B issues, first-reuse edges,
  equal reused locations with distinct copy identities and distinct alternating
  arenas. Rejections exclude mbarrier as native completion and publication
  beyond the A copy's actual byte count. Arbitrary captured real matrix values
  remain arbitrary; no arithmetic or GPU execution verdict is inferred.
- Development: Lean caught an implicit descriptor resolver, checkpoint
  refolding, native mark/group field normalization and operand-location alias
  rewriting. Explicit arguments and focused frame rewrites solve these within
  the unchanged two-million-heartbeat budget. Publication, native
  completion, reuse and test modules build in about 1.1, 1.2, 1.4 and 1.8
  seconds respectively. Failed builds are not passing evidence; these are
  proof-check costs, not GPU timings or measured optimization benefits.
- Reuse/research status: the same completion/publication rules cover both
  arenas and every repeated tile; the generic writer-existence rule is shared
  across A/B operands. The proof of producer-lane order reuses the actual
  native wait, source-index intervals and existing ByteOrder model. This is an
  engineering baseline, not a new asynchronous ownership protocol, independent
  optimized-kernel result or measured agentic-method contribution. No semantic
  axiom, completed-reply assumption or numerical relaxation is introduced.
- Remaining: derive causal RF/co selection and operand-value agreement from
  the actual writer inventory, prove all-lane CTA/native/combined control
  legality and a fully admitted completed execution, then connect tensor
  arithmetic and final output/full-Pre refinement. These constructed resource
  histories do not characterize observations in all arbitrary admitted
  histories. Broader profiles/allocation/in-flight lifetime and runtime/Iris
  correspondence remain required. All required cases stay partial, exact
  paper 81-form parity remains unconfirmed, and the full goal remains active.
  No new GPU execution, performance measurement, TTGIR frontend or
  IEEE/logits/token-equivalence claim is added.

- Validation: `/tmp/ptx-retry-native-full-gate.log` exited zero and ends with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated PTX-to-Lean comparisons, 3600 Lean jobs,
  6068 audited declarations and 6037 environment-resolved public theorem names,
  all 660 individually refuted strict assertions and 30 assembled PTX examples.
  All 34 new rules and 14 test facts have exact audit entries; new logical
  rejections are separate from the unchanged strict assertion batch. Source,
  exact-audit, whitespace and coverage metadata checks pass. Existing
  header-control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 10:28:33 UTC, all 30 source hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 matching source
  hashes and 25 sm_89 cases (24 exact-byte, one completion-only). No new Hopper
  GPU execution or performance evidence is added.
- Goal ledger snapshot at 2026-11-06 10:28:56 UTC: 12,238,447 tokens versus the
  preceding published 12,164,066, a difference of 74,381. Interim tool-reported
  usage, not final billed usage or a goal-completion report. The original full
  goal stays active. Next: classify every actual writer of a native read byte,
  establish causal RF/co selection and operand agreement, and close all-lane
  native/CTA/control legality, tensor/observer correctness and fully admitted
  execution existence without adding unproved assumptions.


### 2026-11-06 — Force actual native RF and identify arbitrary real input bytes

- Instance/limitation: the existing Hopper double-buffer GEMM with arbitrary
  finite heterogeneous retries and same-slot reuse. Prior publication and
  reuse byte edges did not classify every actual writer or force the native
  RF choice; a captured operand value was still not connected to global inputs.
- Writer inventory: `RetryMemoryGeometry` classifies every actual TMA issue
  using source reconstruction, then every actual shared writer using the
  completed candidate's ordinary-access inventory. Physical regions recover
  A/B, slot, byte offset and source tile. It uses neither a selected RF nor a
  blanket unique-writer premise across tiles. `RetryMemoryPhases` proves that
  old same-slot writes precede the current producer and future writes follow
  the native read/completion, and establishes writer/read comparability for
  every actual writer of the byte.
- RF/value closure: `RetryMemoryInputs` derives mixed-size exclusion from the
  existing descriptor admission and native eligibility from actual byte order.
  Under the existing full MemoryConditions it forces RF to the current source
  producer and derives the captured operand's actual written byte value. The
  model's coherence/no-stale/no-future rules reject stale/future RF and a co
  containing only initialization edges. No caller no-mixed-size, no-taint,
  selected-RF or desired operand-value hypothesis is added.
- Independent inputs: `RetryTensorInputs` proves bounded actual signed source
  coordinates, derives all A/B source addresses and payload values from
  independently represented arbitrary real global matrices and actual admitted
  TMA input reads, and combines this with current RF into native InputAgreement
  and MatrixStorage. Memory initialization is explicitly tied to that existing
  represented input. Matrix arithmetic/output admission is still separate;
  these input theorems do not assume a desired native matrix result.
- Tests and nonvacuity boundary: nine facts check actual writer classification,
  phase ordering and eligibility for arbitrary RF on the three-tile nonzero
  heterogeneous-retry source. Concrete memory/RF/co rejections cover empty RF,
  old/future producer RF, initialization-only co and fabricated operand-byte
  agreement. The previous resource/publication fixture has bits payloads but
  realPart operands. A proved actual bits byte plus the new current-writer
  value rule refutes its MemoryConditions for every initial/RF/co. It remains
  a valid resource/publication test and is now explicitly a memory negative
  case, not a purported positive full-memory/execution witness. The rejection
  concerns distinct symbolic representations; it is not a GPU numerical-error
  result or an assumed floating bit-reinterpretation theorem. Conditional
  memory/input proofs are reported separately from admitted-execution existence.
- Reuse/research status: the existing per-byte phase-writer and regional
  disjointness rules now cover arbitrary actual source candidates, A/B,
  different arenas and reused slots. Actual input-byte and collective-input
  rules connect the same mechanism to independent global tensor storage.
  This is an engineering baseline for the existing model, not a new ownership
  protocol, independent optimized-kernel result or measured agentic-method
  contribution. No semantic axiom, readiness assumption or numerical relaxation
  is added.
- Development: focused source-copy/region inversions and existing prefix bounds
  replace fixed zero-retry assumptions. Implicit source premises and frame
  normalization remain explicit in the final proofs. Final input/RF and tensor
  modules build in about 1.3 and 1.4–1.5 seconds; the test module takes about
  1.1 seconds. The two-million-heartbeat budget is unchanged. These are proof
  checking costs, not GPU timings or performance improvements.
- Remaining: construct a positive fully admitted memory/native/control
  execution, prove all-lane CTA/native/combined control legality, connect tensor
  arithmetic, the final observer and full-Pre functional/refinement correctness.
  The new RF/input results use constructed retry histories; observations in all
  arbitrary admitted histories still need characterization. Broader
  profiles/allocation/in-flight lifetime and runtime/Iris correspondence
  remain required. All required cases stay partial, exact paper 81-form parity
  remains unconfirmed and the original full goal stays active. No new GPU
  execution, performance measurement, TTGIR frontend or IEEE/logits/token
  equivalence result is claimed.

- Validation: `/tmp/ptx-retry-memory-inputs-full-gate.log` exited zero and ends
  with `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated PTX-to-Lean comparisons, 3605 Lean jobs,
  6103 audited declarations and 6072 environment-resolved public theorem names,
  all 660 individually refuted strict assertions and 30 assembled PTX examples.
  All 26 new rules and nine test facts have exact audit entries. New memory
  rejections are separate from the unchanged strict assertion batch. Source,
  exact-audit, whitespace and coverage metadata checks pass. Existing
  header-control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 10:46:02 UTC, all 30 source hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 matching source
  hashes and 25 sm_89 cases (24 exact-byte, one completion-only). No new Hopper
  GPU execution or performance evidence is added.
- Goal ledger snapshot at 2026-11-06 10:46:40 UTC: 12,304,169 tokens versus the
  preceding published 12,238,447, a difference of 65,722. Interim tool-reported
  usage, not final billed usage or a goal-completion report. The original full
  goal remains active. Next: close native/CTA/combined control legality and
  tensor arithmetic/final observer refinement, and build positive fully
  admitted memory/execution witnesses; preserve the distinction between
  conditional RF/input rules and such existence evidence.

### 2026-11-06 — Derive actual retry accumulation and output-store payloads

- Instance/limitation: the existing Hopper double-buffer GEMM, with arbitrary
  finite heterogeneous lane/tile retries. The preceding memory results
  identified the actual input bytes but did not connect actual captured matrix
  replies across iterations or derive final source-store values.
- Method: `RetryArithmetic` proves actual call input/output bridges to adjacent
  checkpoints and an induction over the source K loop. It reuses the existing
  WGMMA Arithmetic/TensorConditions and the memory-to-independent-input bridge.
  Under full MemoryConditions for the constructed retry histories and an
  existing TensorConditions component for each actual collective, it derives
  arithmetic for the independent inputs, the final accumulator's equality to
  the independent GEMM specification, and the payload inventory of the actual
  family traces' global stores. No desired kernel-output premise, semantic
  axiom, numeric relaxation or new global admission predicate is introduced.
- Tests: seven checked facts cover arbitrary-real source accumulation, the
  nonzero three-tile A=1/B=2 result 96, zero-valued checkpoints, actual operand
  representation, heterogeneous-retry tensor components and final accumulation,
  and rejection of a fabricated first matrix reply for every logical memory.
  The heterogeneous-retry fixture still has bits payloads and realPart operands;
  its positive tensor/source checks are component evidence, while its full
  memory conditions remain refuted. These facts do not claim a positive
  fully admitted memory/control execution. The arbitrary-real data-oracle
  positive check separately establishes satisfiable arithmetic/accumulation.
- Reuse/research status: one induction handles all lanes, output fragments,
  tile counts and finite retry schedules, while the existing collective input
  identification rule connects both operand arenas to it. This is baseline
  semantic composition, not a new permission protocol, independently measured
  optimization or agentic-method contribution. Focused module/test checking
  takes about 1.1/1.2 seconds with the unchanged two-million-heartbeat budget;
  these are proof-checking costs, not GPU timings.
- Remaining: final observer refinement, all-lane native/CTA/combined control
  legality and a positive fully admitted execution witness. Resource-history
  observations still need characterization for all arbitrary admitted histories;
  broader profiles, allocation/in-flight lifetime and runtime/Iris connections
  remain open. Every required case stays partial and the exact paper 81-form
  inventory remains unconfirmed. No new GPU execution, performance measurement
  or IEEE/logits/token-equivalence result is claimed.
- Frontend discussion: current CLI directly calls the PTX parser, and Program
  owns PTX-oriented emission. Shared memory/event rules can support future
  frontends through checked semantic connections; direct TTGIR support also
  needs layout, SSA/control and asynchronous-operation semantics. Compiling
  Triton to PTX would reuse the current entry point but would not itself prove
  TTGIR-to-PTX compilation correct. No TTGIR frontend or goal expansion is added.
- Validation: `/tmp/ptx-retry-arithmetic-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated PTX-to-Lean comparisons, 3607 Lean jobs,
  6117 audited declarations and 6086 environment-resolved public theorem names,
  all 660 individually refuted strict assertions and 30 assembled PTX examples.
  All seven new rules and seven test facts have exact audit entries. After
  the gate, coverage evidence paths were added and metadata validation rerun;
  no proof or executable source changed. Existing control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 11:02:50 UTC, all 30 hashes current.
  GPU evidence remains 2026-11-05 07:46:53 UTC with 15 current hashes and
  25 sm_89 cases (24 exact-byte, one completion-only). No new Hopper hardware
  evidence is added.
- Goal ledger snapshot at 2026-11-06 11:03:03 UTC: 12,421,952 tokens versus
  the preceding published 12,304,169, a difference of 117,783. Interim tool
  usage, not final billed usage or a completion report. The original full goal
  remains active. Next: close all-lane control and final observer correctness,
  and construct positive fully admitted execution evidence while keeping the
  existing arithmetic and memory admission components explicit.

### 2026-11-06 — Actual retry output writers and final observed GEMM bytes

- Instance/limitation: the Hopper double-buffer GEMM with arbitrary finite
  heterogeneous lane/tile retries. The preceding accumulation proof identified
  source-store payloads, but an unindexed inventory did not identify every
  actual writer or establish that a compatible final observer reads its value.
- Source ownership: `RetryStoreInventory` locates each actual output store by
  the full initial/loop event-prefix length and output-fragment offset. Its
  reverse source classification excludes writes in initial/loop/return events,
  recovers source lane and store serial from every ordinary global footprint,
  and derives unique writers for each global byte using the output layout.
  Actual captured output bytes are proved directly from the source event.
  No unique-writer premise is imposed on the repeatedly written shared buffers.
- Observer/refinement: `RetryObservedOutput` derives global observer eligibility
  from existing descriptor admission and actual unique writers, for arbitrary
  histories, cluster scope and RF. It constructs a compatible completed
  observer component from existing co irreflexivity; full MemoryConditions
  derive that premise through coherence and derived mixed-size exclusion.
  Existing causal/observer conditions force observed output bytes to equal
  actual source-store bytes, and observed global bytes outside the output
  region retain the initial generic-proxy value. Combining the preceding
  memory/input and arithmetic induction proves every observed GEMM specification
  byte for the constructed retry histories, including for the constructed
  observer. No desired observed-output premise or semantic axiom is added.
- Tests: ten facts check actual producer/consumer store serials (41..44 and
  35..38), all lanes/fragments/bytes of arbitrary-real captured replies, actual
  global writer uniqueness, global eligibility for arbitrary histories/RF,
  positive completed-observer components and selected values, adjacent frame
  preservation, and rejection of omitted writes, stale initialization selection
  and fabricated observed values. The fixture still has bits TMA payloads and
  realPart native operands; its full memory conditions remain refuted. Its
  observer-component witness with initialization-only co is deliberately
  separate from full memory/coherence and fully admitted execution existence.
  The three new negative facts are separate from the unchanged strict batch.
- Reuse/research status: actual source indexing and byte ownership are reused
  for all global writer/selection/eligibility rules; the existing observer
  rules then apply to both arbitrary compatible observations and the selected
  observation. The shared multi-writer RF mechanism remains distinct. This is
  engineering composition within the existing model, not a new ownership
  protocol or measured optimized-kernel/agentic-method result. Focused store,
  observer and test checking takes about 1.2/1.1/1.3 seconds respectively with
  the unchanged two-million-heartbeat setting. No GPU timing is inferred.
- Remaining: all-lane native/CTA/combined control legality, positive fully
  admitted retry execution existence, allocation/in-flight lifetime and
  runtime/Iris/physical-observer correspondence. Input/history observations
  still need characterization for all arbitrary admitted resource histories;
  the new GEMM refinement uses the constructed retry histories. Conditional
  observer refinement does not close full-Pre admission/correctness. All seven
  required acceptance cases stay partial and exact paper 81-form parity remains
  unconfirmed. No TTGIR frontend, new GPU execution, performance measurement
  or IEEE/logits/token-equivalence result is added.
- Validation: `/tmp/ptx-retry-observer-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated PTX-to-Lean comparisons, 3610 Lean jobs,
  6143 audited declarations and 6112 environment-resolved public theorem names,
  all 660 individually refuted strict assertions and 30 assembled PTX examples.
  All 16 new rules and ten test facts have exact audit entries. Existing
  control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 11:14:44 UTC, all 30 hashes current.
  GPU evidence remains 2026-11-05 07:46:53 UTC with 15 current source hashes and
  25 sm_89 cases (24 exact-byte, one completion-only); no new Hopper hardware
  evidence is added.
- Goal ledger snapshot at 2026-11-06 11:15:00 UTC: 12,486,402 tokens versus
  the preceding published 12,421,952, a difference of 64,450. Interim tool
  usage, not final billed usage or a completion report. The original full goal
  remains active. Next: close all-lane native/CTA/combined control legality and
  construct positive fully admitted execution evidence, retaining explicit
  memory/tensor components and the distinction between observer components
  and full memory/execution admission.

### 2026-11-06 — All-candidate native participation and actual retry signatures

- Instance/limitation: the Hopper double-buffer GEMM with arbitrary finite
  heterogeneous lane/tile retries, plus zero K. Prior native participation and
  signature inventory proofs applied to the selected zero-retry data family;
  actual source serials and query counts shift with each lane's retries.
- Participation: `RetryNativeSchedules` proves that failed mbarrier waits,
  initialization, prefetch work and output add no native signatures, while each
  compute block has the fixed fence/MMA/commit/wait schedule. Source geometry,
  coverage and unique trace IDs recover every actual lane and all actual traces
  of an arbitrary source family. This derives the checked SchedulesAdmitted
  condition without a caller participation premise. Source reconstruction then
  proves it for every well-formed completed canonical candidate with the
  existing tile-count bound, without assuming a source family, descriptor,
  resource-history, RF or tensor component. Zero K is handled by reconstruction
  of the exit path and proof that its native schedule is empty.
- Actual signatures: `RetryNativeCases` retains retry/prefetch prefix lengths
  in each native event ID. Forward and reverse source-list proofs classify
  every actual native signature by tile, lane and instruction and locate each
  expected signature in the actual candidate. Inverting MMA recovers the exact
  actual source mark/call; inverting wait recovers the actual tile+1 completed
  count through the existing source semantics. NativeSync matches equal
  tile/instruction identities. These are derived source facts, not assumed
  arithmetic replies or desired completion metadata.
- Tests: twelve checked facts cover the actual native schedule, producer and
  consumer source serials, exhaustive actual signature classification, all 128
  aligned participants, all 32 physical-warp participants' checked source PCs,
  and same-warp matching of actual instructions. Negative facts reject matching
  different physical warps, instructions or same-slot reuse rounds, completing
  a later native group with an earlier wait, and a candidate missing the other
  aligned lanes. Warp-local .sync rendezvous is distinct from the full 128-lane
  aligned-participation condition. Closed decision procedures only inspect
  fixed thread geometry; real-valued states/events/payload equality is not
  decided. Source PC evidence uses the existing located-run/source connection.
- Boundary/nonvacuity: these are positive source/participation components, not
  full ControlAdmitted or memory/native-control execution witnesses. The retry
  fixture keeps arbitrary matrix replies and its known bits/realPart mismatch;
  full memory conditions remain refuted. No new semantic axiom, blanket native
  visibility rule, readiness premise, inserted kernel wait or numerical
  relaxation is introduced. Combined TMA/resource/CTA/native ControlAcyclic
  remains open for arbitrary retries. Existing zero-retry combined-control
  proofs are not relabeled as that result.
- Reuse/research status: one source reconstruction supplies all actual traces
  and all native participants, and one signature inventory handles each tile,
  lane and instruction across arbitrary finite retry schedules. Existing
  participant/source-PC and signature-identity rules apply to these actual
  events. This is baseline semantic composition, not a novel permission method
  or measured optimized-kernel/agentic-method contribution. Final focused
  schedule/case/test builds take about 1.3/1.4/1.3 seconds respectively with the
  unchanged two-million-heartbeat setting; these are proof-checking costs.
- Remaining: retry-aware combined-control ranks/acyclicity, positive fully
  admitted execution existence, input/history characterization for all arbitrary
  admitted resource histories, allocation/in-flight lifetime and runtime/Iris/
  physical-observer connections. Conditional GEMM/observer refinement retains
  the existing memory and tensor components and constructed histories. All seven
  required acceptance cases stay partial and exact paper 81-form parity remains
  unconfirmed. No TTGIR frontend, GPU execution, performance measurement or
  IEEE/logits/token-equivalence result is added.
- Validation: `/tmp/ptx-retry-native-participation-full-gate.log` exited zero
  with `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated PTX-to-Lean comparisons, 3613 Lean jobs,
  6181 audited declarations and 6150 environment-resolved public theorem names,
  all 660 individually refuted strict assertions and 30 assembled PTX examples.
  All 26 new rules and twelve test facts have exact audit entries. New native
  negative facts are separate from the unchanged strict assertion batch.
  Existing control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 11:29:57 UTC, all 30 source hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 current source
  hashes and 25 sm_89 cases (24 exact-byte, one completion-only); no new Hopper
  hardware evidence is added.
- Goal ledger snapshot at 2026-11-06 11:30:37 UTC: 12,551,675 tokens versus
  the preceding published 12,486,402, a difference of 65,273. Interim tool usage,
  not final billed usage or a completion report. The original full goal remains
  active. Next: use the actual retry signature/resource identities to establish
  combined-control ranks and acyclicity, then construct positive fully admitted
  execution evidence while preserving the existing memory/tensor boundaries.

### 2026-11-06 — Retry-aware source clocks and actual program-order ranks

- Instance/limitation: the positive-path Hopper double-buffer GEMM source
  family with arbitrary finite heterogeneous retries. The old zero-retry
  control clock uses fixed serial formulas: the same first native fence has
  actual serials 13 and 6 on producer lane 0 and consumer lane 2, but the old
  clock assigns ticks 13 and 15. It cannot directly witness native alignment
  for these actual retry traces. Its early notification placements also cannot
  simply be reused with the constructed failed-wait resource serialization.
  This is a proof-clock limitation, not a newly discovered invalid execution.
- Clock construction: `RetryControlClock` computes a finite retry budget from
  all actual family schedules and a positive scale with room for all lane/
  attempt ordinals. Every failed wait lies in a checked interval before the
  successful wait; later lanes' failed waits have larger ordinals. Separate
  initial, failed, successful, prefetch, compute/CTA and output blocks contain
  one clock entry per corresponding source event. Length equality is proved
  against actual rich source-event lists, not assumed from a desired schedule.
- Order/actual identities: `RetryClockOrder` proves block bounds and strict
  order within and across iterations and the output suffix. `RetrySourceRank`
  connects present actual source IDs to valid clock indices and proves that
  every actual ProgramOrder edge strictly increases the source rank. Prefix
  lookup preservation locates the actual native and failed/successful wait
  events: native ranks recover canonical tile/instruction ticks plus lane
  offsets despite different serials/queries, while failed-wait ordinals support
  cross-lane resource serialization. The default for absent indices cannot
  supply a rank for an actual edge because event presence proves the bound.
- Tests: nine checked facts cover the fixture's finite budget (1150), scale
  (147201), actual producer/consumer clock counts (49/41), every actual native
  clock position, heterogeneous native alignment, the old-clock misalignment
  counterexample, actual failed-before-success and cross-lane failed order,
  actual source order from native wait to reused-copy issue, and rejection of
  source-only cycles using the new rank. Closed budget/geometry calculations
  do not decide real-valued state, event or payload equality.
- Development/cost: an implicit finite-sum inference initially exhausted the
  unchanged two-million-heartbeat budget. Explicit sum domains/functions
  eliminated the expansion and the budget module checked in about 1.3 seconds.
  Independent Nat bounds avoid dependent-Fin Boolean branching, and explicit
  projection rewrites connect actual IDs without unfolding captured states.
  Final focused clock/order/test checks are about 1.3/1.6/1.4 seconds; these are
  proof-checking costs, not GPU timings. No heartbeat increase or semantic
  axiom is introduced.
- Reuse/research status: the same finite clock budget supports strict source
  sequences and actual cross-lane failed-wait ordering, and the same prefix
  lookup bridge identifies native, failed and successful wait positions. This
  is baseline control-proof engineering, not a new ownership/synchronization
  protocol, independently measured optimization or agentic-method contribution.
  The kernel and its synchronization, numerical semantics and memory-visibility
  rules are unchanged.
- Remaining: this closes the source-order portion of the retry control rank,
  not combined ControlAcyclic. Notification/resource, implicit TMA, CTA and
  native arrival/rendezvous/operand/completion edge ranks still need checks;
  the source-only cycle test is not a full graph theorem. The existing zero-K
  exit remains a separate control-proof branch. Positive fully admitted retry
  execution existence, arbitrary admitted-history input characterization,
  allocation/in-flight lifetime and runtime/Iris/physical-observer connections
  remain open. The positive source fixture still has its known negative full
  memory status. All seven required acceptance cases stay partial; exact paper
  81-form parity is unconfirmed. No TTGIR frontend, new GPU execution,
  performance measurement or IEEE/logits/token-equivalence result is added.
- Validation: `/tmp/ptx-retry-source-rank-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated PTX-to-Lean comparisons, 3617 Lean jobs,
  6227 audited declarations and 6196 environment-resolved public theorem names,
  all 660 individually refuted strict assertions and 30 assembled PTX examples.
  All 37 new rules and nine test facts have exact audit entries. The new
  source-only cycle fact is separate from the unchanged strict assertion batch.
  Existing control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 11:54:47 UTC, all 30 source hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 current source
  hashes and 25 sm_89 cases (24 exact-byte, one completion-only); no new Hopper
  hardware evidence is added.
- Goal ledger snapshot at 2026-11-06 11:55:17 UTC: 12,629,472 tokens versus
  the preceding published 12,551,675, a difference of 77,797. Interim tool usage,
  not final billed usage or a completion report. The original full goal remains
  active. Next: connect completion-notification/resource and implicit TMA ranks,
  then CTA/native control edges, and build positive fully admitted execution
  evidence without replacing the existing memory/tensor components by assumptions.

### 2026-11-06 — Actual implicit TMA and full retry resource-history ranks

- Instance/limitation: the positive-path Hopper double-buffer GEMM source
  family with arbitrary finite heterogeneous retries. The source clock alone
  did not rank actual implicit TMA or resource serialization edges. An immediate
  completion rank derived from an early copy-issue clock leaves no room for
  the failed waits serialized before its notification in the constructed
  history. This is a proof-clock incompatibility, not a physical execution bug.
- Source/role connection: `RetryResourceRanks` locates actual initial/output
  and prefetch events in the checked clock lists and recovers expect/copy issue
  and init/inval ranks. Equal A/B copy IDs would contradict their recovered
  source ranks; same-role tile injectivity gives unique bounded tile identities.
  `RetryTmaControl` uses standard mathematical choice solely to select that
  already-proven unique tile for each notification role. The absent-copy default
  cannot justify an actual implicit edge: existing exhaustive source-copy
  classification recovers a bounded A/B role for every actual completion.
- Implicit edges: descriptor, read and write ranks extend the actual source
  issue rank. Notification ranks depend on the consumed tile and follow all
  failed waits, with A before B and B before successful waits. Every actual
  TMA InternalEdge increases this rank, including the write-to-notify completion
  edge; source ProgramOrder increases the same rank. Actual copy classification
  derives these results without a caller notification/readiness/rank premise.
- Resource closure: `RetryResourceControl` proves sorted ranks for all failed
  waits, successful waits, whole phases and complete resource histories in both
  shared slots. Bounds separate same-slot rounds and the initialization/
  invalidation endpoints. The generic resource-edge rule then proves that every
  ResourceEdge of the constructed retry histories increases the same rank.
  Every failed source wait is retained; no synchronization is inserted or erased.
- Tests/nonvacuity: ten checked facts cover actual source endpoints and copy
  roles, positive actual A-byte completion edges with derived WritePresent,
  failed/notification/success ranking, positive admitted and sorted resource
  components, 1030/516-entry history sizes, an immediate-notification-clock
  counterexample, reverse completion rejection and cycle rejection for the
  explicitly source/implicit-TMA/resource-only subgraph. That cycle fact omits
  CTA/native edges and is not a renamed ControlAcyclic theorem. The fixture's
  known bits/realPart mismatch still refutes full MemoryConditions; positive
  byte-completion/resource components are not a full memory/execution witness.
- Development/cost: explicit match/projection normalization exposes descriptor
  facts after copy lookup. A concrete rank `change` initially hit the unchanged
  two-million-heartbeat budget by expanding the finite budget; a local abstract
  Nat inequality and focused rewrites avoid that expansion. Focused source-role,
  implicit-TMA, resource-history and test builds take about 1.4/1.4/3.3/7.5
  seconds respectively. No heartbeat increase, semantic axiom, memory-visibility
  rule or numerical relaxation is introduced. These are proof-checking costs,
  not GPU performance measurements.
- Reuse/research status: actual source ranks, implicit byte-access stages and
  resource-history origins now share a single increasing control rank. The
  source-copy identity rules support both notification selection and edge
  inversion, and the generic resource-edge theorem applies across slots and
  repeated phases. This is baseline semantic/control composition, not a new
  ownership protocol or measured optimized-kernel/agentic-method contribution.
- Remaining: CTA and native arrival/rendezvous/operand/completion rank checks,
  then combined ControlAcyclic and positive fully admitted retry execution
  existence. The zero-K exit remains a separate control-proof branch. Input/
  observation characterization over all arbitrary admitted resource histories,
  allocation/in-flight lifetime and runtime/Iris/physical-observer connections
  remain open. All seven required acceptance cases stay partial and exact paper
  81-form parity remains unconfirmed. No TTGIR frontend, new GPU execution,
  performance measurement or IEEE/logits/token-equivalence result is added.
- Validation: `/tmp/ptx-retry-tma-resource-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated PTX-to-Lean comparisons, 3621 Lean jobs,
  6265 audited declarations and 6234 environment-resolved public theorem names,
  all 660 individually refuted strict assertions and 30 assembled PTX examples.
  All 28 new rules and ten test facts have exact audit entries. New clock/
  subgraph counterexamples are separate from the unchanged strict batch.
  Existing control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 12:20:28 UTC, all 30 source hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 current source
  hashes and 25 sm_89 cases (24 exact-byte, one completion-only); no new Hopper
  hardware evidence is added.
- Goal ledger snapshot at 2026-11-06 12:22:00 UTC: 12,711,858 tokens versus
  the preceding published 12,629,472, a difference of 82,386. Interim tool usage,
  not final billed usage or a completion report. The original full goal remains
  active. Next: establish actual retry CTA identities/ranks, close native control
  edge ranks, and construct positive fully admitted execution evidence while
  retaining all existing source, memory and tensor obligations.

### 2026-11-06 — Actual retry CTA identities and TMA base-control closure

- Instance/limitation: positive-K Hopper double-buffer GEMM with arbitrary
  finite heterogeneous retries. The shared source/TMA/resource rank still
  lacked actual CTA generation, event-index and matching-edge connections.
- Source connection: `RetryCtaCases` derives checkpoint, prepared and output
  generations, excludes CTA tags from failed waits and prefetch events, and
  classifies initial/reuse/return events. `RetryCtaTrace` lifts classification
  to every actual candidate trace and proves the reverse actual-tag direction.
  Initial barrier 0, reused barrier 2 and output barrier 1 remain distinct;
  reused barrier generations follow actual tile indices.
- Control closure: `RetryCtaControl` locates both actual CTA instructions in
  each iteration's six-event compute suffix and recovers their source ranks.
  Matching arrivals precede all returns across all 128 lanes. Combining this
  with the existing source, implicit TMA and resource edge rules closes
  `Tma.ControlAcyclic` for the constructed retry histories. Source reconstruction
  supplies a family/control witness for every source-well-formed completed
  positive-K canonical candidate, without adding readiness/convergence premises
  or changing the kernel's synchronization.
- Positive component and tests: twelve facts check actual retry-dependent
  indices, generations, all initial/reuse/return tags and all-lane CTA edges,
  and reject cross-generation, cross-barrier and return-to-arrival paths.
  Actual reply payloads are constant bits-zero lists; checked source payload
  length and an independent constant bits-zero initial memory prove payload
  agreement. This yields a positive complete existing `TmaComponents` fixture,
  including descriptor, resource and TMA base-control fields. It is not a
  fully admitted execution: the fixture's bits/realPart mismatch still refutes
  full MemoryConditions. Descriptor decoding from physical descriptor bytes is
  not established by this fixture.
- Reuse/research status: the same rank now handles source, implicit TMA,
  resource serialization and CTA edges across both slots and repeated reuse.
  Actual-event classification supports both graph inversion and positive
  component construction. This is baseline semantic/control composition, not
  a new ownership protocol, measured optimization or agentic-method result.
  Focused cases/trace/control/test builds take approximately 1.9/2.1/1.2/1.3
  seconds. No heartbeat increase, semantic axiom or numerical relaxation is
  introduced; these are proof-checking costs, not GPU performance measurements.
- Remaining: `Unified.ControlAcyclic` still needs native arrival, rendezvous,
  operand and completion edge checks. Fully admitted execution existence,
  zero-K control, arbitrary admitted-history input characterization, allocation/
  in-flight lifetime and runtime/Iris/physical-observer correspondence remain
  open. All seven required acceptance cases stay partial; exact paper 81-form
  parity remains unconfirmed. No TTGIR frontend, new GPU execution, performance
  measurement or IEEE/logits/token-equivalence result is added.
- Validation: `/tmp/ptx-retry-cta-full-gate.log` completed with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated PTX-to-Lean comparisons, 3625 Lean jobs,
  6307 audited declarations and 6276 environment-resolved public theorem names,
  all 660 individually refuted strict assertions and 30 assembled PTX examples.
  All 30 new rules and twelve test facts have exact audit entries. New negative
  facts are separate from the unchanged strict assertion batch. Existing control
  tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 12:49:33 UTC, all 30 source hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 current source
  hashes and 25 sm_89 cases (24 exact-byte, one completion-only); no new Hopper
  hardware evidence is added.
- Goal ledger snapshot at 2026-11-06 12:52:50 UTC: 12,795,050 tokens versus
  the preceding published 12,711,858, a difference of 83,192. Interim tool usage,
  not final billed usage or a completion report. The original full goal remains
  active. Next: close actual native edge ranks in the unified control graph,
  then build positive fully admitted execution evidence while retaining the
  existing source, memory and tensor obligations.

### 2026-11-06 — Full unified construct control for finite retry families

- Instance/limitation: positive-K Hopper double-buffer GEMM with arbitrary
  finite heterogeneous retries. The preceding turn closed TMA/resource/CTA
  control but left native arrival/rendezvous/operand/completion edges outside
  that theorem. That turn was progress; the original full goal stays active.
- Actual arrival gap: `RetryClockGaps` classifies every actual source clock as
  a regular lane clock or a bounded failed-wait clock. For a same-thread source
  event preceding an actual native instruction, the strict source-clock order
  therefore leaves a lane-independent interval before that instruction's tick.
  Presence bounds exclude the source rank's out-of-range fallback. No kernel
  event or wait is inserted, erased or reordered.
- Native ranks: `RetryNativeRanks` recovers native ticks by dividing actual
  source ranks by the positive retry unit and tick spacing. Actual signatures
  force matching warp-local rendezvous to use the same tile/instruction tick;
  arrivals precede all source returns at that tick. Operand issue follows the
  actual MMA source rank. Completion inversion reconstructs the actual issue
  tile, collective group and native wait tile from source events: group equality
  across actual collective members and the source wait's completion count imply
  issue tile <= wait tile. This ranks all actual completion edges, including
  source-matched later waits, without an added eventual-readiness premise.
- Unified closure: `RetryUnifiedControl` uses one rank for every actual source,
  implicit TMA, resource-history, CTA, native arrival/rendezvous, operand issue
  and completion edge. It proves full `Unified.ControlAcyclic`, then combines
  it with already-derived aligned participation to prove `ControlAdmitted`.
  Source reconstruction supplies a family/control witness for every
  source-well-formed completed positive-K canonical candidate. Histories remain
  the constructed retry histories; this is not admission for arbitrary histories.
- Tests/nonvacuity: fourteen facts check native ticks, actual fence-to-MMA
  source/arrival edges, pre-arrival gaps, warp-local rendezvous, operand issue,
  all-lane native completion, positive complete control admission, reconstructed
  control witnesses and joint existing TmaComponents/control components. Actual
  byte publication supplies a mixed TMA/resource/source/native path; reverse
  publication, wait-to-operand and source-return-to-arrival paths are rejected
  in the full unified graph, rather than only in a source-only subgraph.
  The fixture's known bits/realPart mismatch still refutes full MemoryConditions;
  its positive TMA/control components are not a fully admitted execution witness.
- Reuse/research status: actual source classification and one finite retry
  clock compose all construct-control edge classes across lanes, slots and reuse
  rounds. Existing publication-to-control rules supply the mixed-path tests;
  control is never used to invent a memory-publication edge. This is baseline
  semantic/control proof engineering, not a new ownership protocol, measured
  optimization or agentic-method result. No numerical semantics, visibility
  rule, heartbeat budget or semantic axiom changes.
- Development/cost: focused clock-gap/native-rank/unified-control/test builds
  take approximately 1.5/1.6/1.9/1.5 seconds. Nested control-node patterns needed
  explicit base/source elimination. The first full run passed Lean compilation
  but rejected all 30 missing new audit entries after a registration script
  used the wrong working directory; registration was corrected and the full
  gate was rerun successfully. These are proof/tooling costs, not GPU timings.
- Remaining: positive fully admitted execution existence must satisfy the
  existing memory and tensor components together, not arbitrary captured matrix
  replies. Zero-K control, arbitrary admitted-history input characterization,
  allocation/in-flight lifetime and runtime/Iris/physical-observer correspondence
  remain open. All seven required acceptance cases stay partial and exact paper
  81-form parity remains unconfirmed. No TTGIR frontend, new GPU execution,
  performance measurement or IEEE/logits/token-equivalence result is added.
- Validation: `/tmp/ptx-retry-unified-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated PTX-to-Lean comparisons, 3629 Lean jobs,
  6337 audited declarations and 6306 environment-resolved public theorem names,
  all 660 individually refuted strict assertions and 30 assembled PTX examples.
  All 16 new rules and fourteen test facts have exact audit entries. New negative
  path facts are separate from the unchanged strict assertion batch. Existing
  control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 13:05:36 UTC, all 30 source hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 current source
  hashes and 25 sm_89 cases (24 exact-byte, one completion-only); no new Hopper
  hardware evidence is added.
- Goal ledger snapshot at 2026-11-06 13:06:01 UTC: 12,919,437 tokens versus
  the preceding published 12,795,050, a difference of 124,387. Interim tool usage,
  not final billed usage or a completion report. Next: construct positive fully
  admitted execution evidence, handle zero-K control, and retain all existing
  source, memory, tensor and observation obligations.

### 2026-11-06 — Independent real data and explicit retry RF values

- Instance/limitation: the positive-K Hopper double-buffer GEMM with arbitrary
  finite heterogeneous lane/tile retries. The preceding turn closed full
  unified construct control and was progress. The existing retry fixture still
  carried bits-zero TMA payloads versus realPart native operands, so it could
  not supply a positive full-memory witness even when its control and selected
  tensor components passed. A separate independent-data source is necessary;
  the negative fixture and its refutations are retained unchanged.
- Pure query connection: `RetryDataQueries` defines source wait/native/copy
  queries independently of interpreter replies. The source recurrence separates
  failed wait intervals from every successful wait, makes native queries strict,
  and orders A/B copy queries both within and across tiles. Query equality
  therefore identifies the unique tile/role. Actual prepared source states use
  these same native queries. No real-valued equality procedure is used.
- Data construction: `RetryDataOracle` selects the proven unique bounded Nat
  metadata tile using standard mathematical choice. It computes matrix replies
  from independent input matrices and the existing tile recurrence, and supplies
  represented operand/TMA bytes. Failed/successful waits and all payload lengths
  satisfy actual source reply requirements; every positive-K source candidate
  in this constructed family is checked well formed and complete under the
  existing tile bound. Defaults at unused queries do not justify actual events.
- Tensor/TMA closure: `RetryDataTensor` identifies actual call inputs, outputs
  and operand bytes with source checkpoints and independent matrices, proves
  every actual tensor component and the final accumulation. `RetryDataTma`
  recovers actual copy query bases, descriptor views and payloads. Existing
  packed-source and represented-initial-memory byte rules prove payload agreement
  for every actual copy, not a desired payload premise. Existing TmaComponents,
  full ControlAdmitted and all tensor components hold together on this family.
  Logical tensor-map bytes are supplied by the existing represented input;
  physical descriptor encoding and IEEE bit reinterpretation are not inferred.
- Explicit RF values: `RetryDataReads` constructs reads-from independently of
  admitted memory. Global input/descriptor reads select represented initial
  memory; native operands select the actual current tile's TMA producer.
  Source-derived representative identity excludes arbitrary tile selection.
  Every actual A/B producer byte matches its represented shared input, and every
  actual read has source-value agreement. This is stronger than agreement only
  at eligible reads, but it supplies no extra visibility or causality rule.
- Tests/nonvacuity: twelve facts cover the actual three-tile heterogeneous query
  schedule, all failed/successful waits, positive joint TMA/control/tensor and RF
  agreement components, actual selected writers and A/B byte values. Nonzero
  A=1, B=2 inputs accumulate to 96 across three tiles with nonzero retries.
  Bits-zero payloads are rejected. A stale RF reading tile zero's A byte when
  tile two reuses the slot violates ReadAgreement for tile-varying inputs;
  eligibility and the actual native read are derived rather than assumed.
- Reuse/research status: the same arbitrary-retry source reconstruction,
  resource histories, control rules, tensor storage and initial-read constructor
  now apply to an independent-data family. This removes the old fixture's known
  value inconsistency without weakening memory conditions or accepting arbitrary
  matrix results. It is baseline proof engineering, not a new ownership protocol,
  measured optimization or agentic-method contribution. No kernel, source wait,
  memory-visibility rule, numerical semantics or heartbeat budget changes.
- Development/cost: the six new files contain 685 source lines, including
  definitions/comments/tests, with 51 rules and twelve test facts. Focused oracle,
  tensor, TMA, read-value and test builds take approximately 1.2/1.2/2.2/1.2/1.3
  seconds. Pure Fin role normalization, explicit family/location aliases and
  concrete real-cast normalization avoid hidden equality procedures and larger
  tactic budgets. These are checking costs, not GPU performance measurements.
- Remaining: the new RF still needs causal/coherence/atomicity/SC-per-location
  witnesses and a compatible final observer before claiming a fully admitted
  retry execution. Control-to-byte refinement must only rank already justified
  byte edges, never invent publication. Zero-K control, arbitrary admitted-history
  characterization, allocation/in-flight lifetime and runtime/Iris/physical-
  observer correspondence remain open. All seven required acceptance cases stay
  partial and exact paper 81-form parity remains unconfirmed. No TTGIR frontend,
  new GPU execution, performance or IEEE/logits/token-equivalence result is added.
- Validation: `/tmp/ptx-retry-data-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated PTX-to-Lean comparisons, 3635 Lean jobs,
  6400 audited declarations and 6369 environment-resolved public theorem names,
  all 660 individually refuted strict assertions and 30 assembled PTX examples.
  All 63 new proofs have exact audit entries. New negative facts are separate
  from the unchanged strict assertion batch. Existing control tests retain
  SHA-256 `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 13:26:58 UTC, all 30 source hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 current source
  hashes and 25 sm_89 cases (24 exact-byte, one completion-only); no new Hopper
  hardware evidence is added.
- Goal ledger snapshot at 2026-11-06 13:27:24 UTC: 13,031,570 tokens versus
  the preceding published 12,919,437, a difference of 112,133. Interim tool usage,
  not final billed usage or a completion report. The original full goal remains
  active. Next: construct causal/coherence and remaining memory witnesses for
  the independent-data retry RF, then connect its final observer and handle the
  zero-K control branch without changing existing admission obligations.

### 2026-11-06 — Full retry memory and joint observer/execution components

- Instance/limitation: independent arbitrary-real Hopper double-buffer GEMM
  inputs, positive K under the existing tile bound and every given finite
  heterogeneous retry schedule. The preceding turn was progress: source/TMA,
  control, tensor and explicit RF values held together, but those values alone
  did not establish causal/coherence/atomicity/SC or a compatible final observer.
- Memory rank: `RetryDataMemoryRank` maps only already-justified byte edges to
  unified control paths, using source-derived absence of non-bulk copies.
  Actual RF, observed and observation-order edges, causality and program order
  increase the same checked rank. This is one-way refinement: control is never
  used to manufacture a visibility or publication edge. `RetryDataReadConflicts`
  derives immutable global input/map reads; every actual read/write overlap
  must be a native shared operand with an identified current tile.
- Causal/coherence construction: `RetryDataCausal` constructs ranked actual-
  writer coherence and proves that selected sources precede reads and are latest
  among preceding actual writers. Existing actual writer-phase classification
  rejects an earlier or future source when its rank is incompatible.
  `RetryDataCoherent` derives shared writer order from actual tile/operand owners
  and source-matched publication/completion/reuse. Global output uniqueness is
  used only for global writers, never imposed on repeatedly overwritten shared
  bytes. All existing coherence fields, including initialization, race guards
  and causal order, follow from the constructed relation.
- Full memory: `RetryDataAtomicity` derives single-copy atomicity from the
  actual one-byte native reads and initialization-selected base reads; actual
  read nodes never write, discharging RMW atomicity from source inventory.
  `RetryDataSC` ranks RF/co/from-read communication and derives per-location SC.
  `RetryDataMemory` now proves full existing MemoryConditions, including all
  causal fields and base acyclicity, for the independently chosen RF/co and
  represented initial memory. No admitted memory/SC/coherence premise or weaker
  replacement predicate is introduced.
- Joint witness and output: `RetryDataExecution` constructs a compatible final
  observer from the same memory witness and combines existing source/TMA,
  full unified control, full memory, every tensor and observer component.
  Observed output bytes satisfy the independent GEMM specification. The
  parameterized existential theorem explicitly preserves
  `family.schedules = schedules`; its witness cannot silently replace the
  supplied retries with a zero-retry execution. The observation domain remains
  the existing 2048 output bytes plus eight adjacent frame bytes. Positive-K
  joint execution existence is now closed in the current model.
- Tests/nonvacuity: fourteen facts check positive full memory and joint
  components for independent inputs on the actual nonzero heterogeneous
  three-tile fixture. Actual shared tile-zero/tile-two writes have forward
  coherence; reverse coherence is rejected, initialization precedes each actual
  writer, and the real from-read edge precedes the later reuse writer.
  Communication cycles are rejected. Every observed output byte follows the
  specification; A=1/B=2 observes 96, and adjacent frame bytes remain 17.
  Initial-only coherence and omitted/stale/fabricated final observations are
  rejected. These new negative facts are separate from the strict batch.
- Reuse/research status: existing control-to-byte refinement, ranked causal and
  coherence constructors, generic source inventory and observer rules compose
  over arbitrary finite retry schedules and repeated shared-slot use. The new
  shared-writer rule also applies to arbitrary actual reply source families.
  This closes a baseline consistency/nonvacuity obligation, not a new ownership
  protocol, measured optimization or agentic-method contribution. The kernel,
  source synchronization, visibility and numerical semantics are unchanged.
- Development/cost: nine new files contain 641 lines including definitions,
  comments and tests, with 30 rules and fourteen test facts. Focused rank,
  read-conflict, causal, coherence, atomicity, SC, memory, execution and test
  checks take about 1.1/1.3/1.1/1.2/1.3/1.2/1.2/1.2/1.3 seconds respectively.
  Explicit resolver parameters and existential/input binder types resolved
  elaboration gaps. No heartbeat increase, real-value equality procedure,
  semantic axiom or numerical relaxation is introduced. These are proof-checking
  costs, not GPU performance measurements.
- Remaining: zero-K control and reconstruction, characterization over all
  arbitrary admitted histories, allocation/in-flight lifetime, Iris/runtime and
  physical observer correspondence remain open. Joint components in this model
  do not establish full physical ISA/IEEE/CUDA execution correspondence. All
  seven required acceptance cases stay partial and exact paper 81-form parity
  remains unconfirmed. No TTGIR frontend, new GPU execution, performance or
  IEEE/logits/token-equivalence result is added.
- Validation: `/tmp/ptx-retry-data-memory-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated PTX-to-Lean comparisons, 3644 Lean jobs,
  6444 audited declarations and 6413 environment-resolved public theorem names,
  all 660 individually refuted strict assertions and 30 assembled PTX examples.
  Every new proof has an exact audit entry. Existing control tests retain
  SHA-256 `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 13:43:30 UTC, all 30 source hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 current source
  hashes and 25 sm_89 cases (24 exact-byte, one completion-only); no new Hopper
  hardware evidence is added.
- Goal ledger snapshot at 2026-11-06 13:43:52 UTC: 13,097,725 tokens versus
  the preceding published 13,031,570, a difference of 66,155. Interim tool usage,
  not final billed usage or a completion report. The original full goal remains
  active. Next: close the zero-K branch, characterize arbitrary admitted histories
  without a constructed-history restriction, and connect allocation/lifetime and
  permission/runtime obligations to the actual event semantics.

### 2026-11-06 — Universal zero-K components and lookup/inventory transport

- Instance/limitation: the zero-K Hopper double-buffer branch. The preceding
  turn closed positive-K joint execution existence and was progress. A standard
  zero-K data witness already existed, but arbitrary completed candidates could
  use different oracles and trace order. Their correspondence to that witness
  had not been connected to control/resource/memory/observer admission. Equal
  event lookups alone would also lose resource-inventory multiplicities.
- Source and multiplicity: `ZeroSource` reconstructs every actual completed
  zero-K trace and proves equality of rich event lookups in both directions.
  Source validity and completion remain premises proved by the executor, not
  inferred from that equality. `ZeroInventory` uses actual thread coverage and
  unique IDs to prove a thread-ID permutation, then lifts source-derived event
  lengths to an event-ID permutation. These comparisons use only metadata;
  no real-valued event equality procedure is introduced.
- Reusable transport: `TmaEventLookup` transports source/CTA/internal TMA
  control and source/notification resource accessors. Inventory transport also
  requires the explicit event-ID permutation, and preserves full HistoryValid,
  including unique origins, exhaustive permutation, source order and protocol.
  `UnifiedEventLookup` preserves actual collective calls/marks/source members,
  native completion and every unified control-edge class, plus access kinds and
  read/write-byte functions. It does not infer source production, participation
  or physical runtime admission from lookup equality.
- Zero-K closure: `ZeroControl` applies those rules only after proving actual
  lookup and multiplicity correspondence, derives every zero-K resource history
  and full unified control, and excludes actual TMA/native events. A common
  completed-candidate control-existence theorem now covers every bounded tile
  count, including zero. `ZeroMemory` derives absence of actual reads, actual
  output-writer uniqueness, byte/causal acyclicity and full existing MemoryConditions
  for every source-well-formed completed zero-K candidate and arbitrary initial
  bytes. Source writes and their observer obligations are retained.
- Observer/existence: `ZeroExecution` constructs a compatible observer and
  combines source/TMA, full control, full memory, native absence and observer
  components. Every observed matrix byte is represented f32 zero; observed
  frame bytes outside output retain initialization. Separate output/frame
  refinement rules allow arbitrary already-admitted RF/co/histories/cluster/
  proxy-initial memory/observer; they are not restricted to the constructed zero
  histories. The general frame rule retains the generic proxy's initial value
  on the observer domain. A source-checked zero execution exists for every
  supplied initial-byte function. Zero-K is closed in the current model.
- Tests/nonvacuity: sixteen facts instantiate arbitrary per-lane oracles and
  reversed trace order, including a checked first lane of 127. Actual lookup,
  event-ID permutation, positive joint components, observed zero matrix and
  adjacent frame bytes pass. Output refinement is also checked with arbitrary
  admitted RF/co/history inputs. A duplicate producer trace has exactly the
  same event lookup but changes its barrier-zero inventory length from two to
  four. Its source and history admission are rejected. This checks the need
  for multiplicities rather than silently treating inventory as a set.
  Invented notifications and omitted/stale final observations are rejected.
- Reuse/research status: lookup transport supports both native-control
  composition and actual byte-access/output correspondence; inventory transport
  handles source and implicit notification origins while retaining counts.
  It applies beyond the zero fixture when its explicit hypotheses are proved.
  This is baseline proof engineering and a soundness/nonvacuity check, not a new
  ownership protocol, measured optimization or agentic-method contribution.
  No kernel, source synchronization, visibility or numerical semantics changes.
- Development/cost: eight new files contain 783 lines including definitions,
  comments and tests, with 68 rules and sixteen facts. Focused source,
  inventory, TMA lookup, unified lookup, control, memory, execution and test
  checks take approximately 3.1/1.1/1.1/1.2/1.1/1.2/1.2/10 seconds. Explicit
  record/binder types, canonical aliases, Option reductions and the Nodup
  reverse rule resolve elaboration without increasing the existing heartbeat
  budget. No semantic axiom, native decision procedure or numerical relaxation
  is added. These are proof-checking costs, not GPU timings.
- Remaining: positive-K input/observation characterization over all arbitrary
  admitted resource histories, allocation/in-flight lifetime and Iris/runtime/
  physical observer correspondence remain open. Neither lookup transport nor
  joint components establish full physical ISA/IEEE/CUDA correspondence. All
  seven required acceptance cases stay partial and exact paper 81-form parity
  remains unconfirmed. No TTGIR frontend, new GPU execution, performance or
  IEEE/logits/token-equivalence result is added.
- Validation: `/tmp/ptx-zero-execution-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated PTX-to-Lean comparisons, 3652 Lean jobs,
  6528 audited declarations and 6497 environment-resolved public theorem names,
  all 660 individually refuted strict assertions and 30 assembled PTX examples.
  All 84 new proofs have exact audit entries. New negative facts remain separate
  from the unchanged strict batch. Existing control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 14:10:10 UTC, all 30 source hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 current source
  hashes and 25 sm_89 cases (24 exact-byte, one completion-only); no new Hopper
  hardware evidence is added.
- Goal ledger snapshot at 2026-11-06 14:10:43 UTC: 13,199,499 tokens versus
  the preceding published 13,097,725, a difference of 101,774. Interim tool usage,
  not final billed usage or a completion report. The original full goal remains
  active. Next: remove the constructed-history restriction on positive-K
  input/observation refinement and connect allocation/lifetime and permissions
  to actual event/runtime semantics.

### 2026-11-06 — Actual control bounds for arbitrary admitted resource histories

- Instance: the existing positive-K Hopper double-buffer GEMM, with arbitrary
  finite heterogeneous retry counts and actual source events. No PTX, numerical
  semantics or synchronization changes are made.
- Limitation: the positive-K publication/output proof still uses the constructed
  resource histories. Protocol-valid parity waits alone do not identify the
  intended tile's completion: an old-phase true wait can follow the next
  same-slot expect while transaction bytes remain outstanding.
- Method: `UnifiedHistoryControl` proves that an actual forward control path
  forces the corresponding order in every exhaustive admitted history; a reverse
  resource edge would form a control cycle. Its prefix rules preserve prior
  origins and exclude later origins through the current event. The path does
  not assume that the arbitrary history equals the constructed witness.
- Applications: `RetryHistoryPaths` derives expect-to-own-notification paths
  from actual copy issue/descriptor/write/completion events, and all-lane
  wait-to-later-expect paths from actual source order and matching CTA arrivals
  and returns. `RetryArbitraryHistory` derives both order families and prefix
  bounds from existing TMA components and unified control admission.
- Counterexample: `TmaHistorySwap` retains exact inventory multiplicities and
  source order with a separately checked swapped protocol run. An actual
  three-tile, 128-lane case swaps lane 127's tile-zero true wait with tile-two's
  producer expect. Protocol, source order, uniqueness and exhaustiveness still
  hold; unified CTA control rejects the resulting cycle. Twelve facts cover
  this case, arbitrary-history bounds and actual heterogeneous-retry instances.
- Reuse/research status: the same control/history rule supports TMA completion
  ordering and CTA storage-reuse bounds. This is baseline proof engineering;
  no new ownership protocol, optimization speedup or agentic-method claim is
  established. Five modules contain 409 lines, 24 rules and twelve test facts.
  The focused test build passes in 2.9 seconds without raising the existing
  heartbeat budget or adding semantic axioms/native decision procedures.
- Remaining: exact completion-phase stamps, publication, RF/input values and
  positive-K observed-output refinement for every admitted history are open.
  Allocation/in-flight lifetime and Iris/runtime/physical observer connections
  remain open. All seven required acceptance cases remain partial; exact paper
  81-form parity stays unconfirmed. No TTGIR frontend, GPU run, performance or
  IEEE/logits/token-equivalence result is added in this step.
- Validation: `/tmp/ptx-arbitrary-history-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated-program comparisons, 3657 Lean jobs, 6564 audited
  declarations and 6533 environment-resolved public theorem names, 660 strict
  assertions individually refuted, and 30 PTX examples assembled. All 36 new
  proofs have exact audit entries. Existing control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 14:32:29 UTC with 30 current source
  hashes. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 current hashes and
  25 sm_89 cases (24 exact-byte, one completion-only); no new Hopper execution.
- Goal ledger snapshot at 2026-11-06 14:33:09 UTC: 13,352,729 tokens versus
  the preceding published 13,199,499, a difference of 153,230. Interim tool usage,
  not final billed usage or a completion report. The full goal remains active.
  Next: derive exact completion-phase/transaction bounds for arbitrary admitted
  prefixes, then use them for positive-K publication and output refinement.

### 2026-11-06 — Operational conservation and counted arbitrary-history prefixes

- Instance: the existing positive-K Hopper double-buffer GEMM, retaining finite
  heterogeneous retries and arbitrary real inputs. The PTX and synchronization
  are unchanged. This extends the preceding arbitrary-history control bounds.
- Limitation: parity and protocol success do not attribute completion to a tile.
  The earlier order bounds alone did not characterize phase/transaction state
  at arbitrary prefixes. Global totals also fail after reinitialization.
- Method: `MbarrierAccounting` folds lifetime-local counters and proves expected
  arrivals, arrival potential `phase*expected + (expected-pending)` and signed
  credit conservation for every valid operational run. Initialization resets
  the counters. `MbarrierPrefixAccounting` replaces reset counters with prefix
  totals only after proving the single-init(1) shape from inventory and protocol
  admission. Its live-prefix lifetime count is one. `MbarrierTransactionCounts`
  gives weighted completion-class equations and monotone prefix counts.
- Additional operational rule: `MbarrierResting` proves that pending equal to
  expected implies nonpositive transaction credit. Negative completion debt
  remains permitted by the original signed semantics. Nonnegative actual credit
  still needs matched-copy prefix arguments; no new readiness assumption is
  introduced to bypass that obligation.
- Actual connection: `TmaPrefixAccounting` checks event-origin indices, actual
  protocol prefixes, successful waits, notifications and lifetime/phase stamps.
  `RetryPrefixAccounting` derives exactly one init(1), fixed arrive-expect(2304)
  and complete-tx sizes 2048/256 by actual inventory permutation. Only counts
  are transported; no equality with the constructed history order is assumed.
  Every actual live prefix has pending at most one and satisfies
  `phase+1 = arrivalCount+pending` and
  `tx = 2304*arrivalCount-2048*completionCount(2048)-256*completionCount(256)`.
  Its stamp has lifetime 1 and its actual operational phase.
- Tests/reuse: nineteen facts check two arrivers, immediate zero-byte completion,
  a valid reinitialization whose reset count differs from the global count,
  permitted signed debt, an old-phase true wait with next-phase credit, invalid
  phase/credit states and distinct completion-size classes. The same rules apply
  at arbitrary actual waits and notifications with real inputs and heterogeneous
  retries. A constructed second-phase prefix and the prior actual 128-lane
  swapped-history counterexample satisfy the equations. These laws support
  both notification accounting and wait/lifetime stamps, while preserving the
  earlier control rejection of the swapped execution.
- Cost/research status: seven modules contain 876 lines, 55 rules and nineteen
  facts. Focused checks take about 1.1–1.4 seconds per module, with the existing
  kernel/test heartbeat budget unchanged. No semantic axiom, native decision
  procedure, new permission protocol, measured speedup or agentic-method result
  is added. This is baseline semantic/proof engineering toward the full goal.
- Remaining: exact tile phase attribution and nonnegative matched-prefix credit,
  all-history completion observations, publication, input reads and positive-K
  observed-output refinement are open. Allocation/in-flight lifetime and
  Iris/runtime/physical observer correspondence remain open. All seven required
  cases stay partial and exact paper 81-form parity stays unconfirmed. No TTGIR
  frontend, new GPU execution, IEEE/logits/token or performance result follows.
- Validation: `/tmp/ptx-prefix-accounting-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated PTX-to-Lean comparisons, 3664 Lean jobs, 6638
  audited declarations and 6607 environment-resolved public theorem names,
  all 660 strict assertions individually refuted and 30 assembled PTX examples.
  All 74 new proofs have exact audit entries. Existing control tests retain
  SHA-256 `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 14:55:42 UTC, all 30 source hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC, with 15 current hashes
  and 25 sm_89 cases (24 exact-byte, one completion-only). No new Hopper hardware
  or GPU execution evidence is added.
- Goal ledger snapshot at 2026-11-06 14:55:52 UTC: 13,436,685 tokens versus
  the preceding published 13,352,729, a difference of 83,956. Interim tool usage,
  not final billed usage or a completion report. The original full goal remains
  active. Next: use actual expect/notification prefix matching and control order
  to derive nonnegative credit and the intended tile phase, then establish
  all-history completion observations and positive-K input/output refinement.

### 2026-11-06 — Derive arbitrary-history exact phases and completion observations

- Instance: positive-K Hopper double-buffer GEMM with arbitrary completed source
  candidates, finite heterogeneous failed-wait counts and arbitrary real inputs.
  The PTX, instruction subset, synchronization and numeric model are unchanged.
- Limitation: the earlier accounting equations allowed signed debt and did not
  connect notifications or successful parity waits to their intended tile.
  The constructed-history completion proof could not justify arbitrary admitted
  resource histories. Parity alone permits stale-phase success.
- Method: `TmaMatchedCounts` supplies injective-parent count bounds and strict
  bounds when a parent lacks its notice, retaining event multiplicities.
  `RetryMatchedPrefixes` proves the actual source metadata parents and uses
  already-proved source/TMA control paths for prefix presence. Each notice class
  has count at most the arrival count, so actual transaction credit is derived
  nonnegative rather than added as a readiness/matching premise.
- Phase proof: `MbarrierPhaseMonotone` follows the operational semantics between
  live prefixes in one initialization lifetime; it excludes reset explicitly.
  `RetryArrivalPrefixes` bounds arrivals through any current wait using actual
  inventory and all-lane CTA reuse control. `RetryExactPhases` inducts over
  same-slot rounds using source-ordered waits and phase monotonicity, deriving
  exact wait phase `tile/2+1`, pending 1, zero credit and lifetime stamp 1.
- Notice/observation proof: `RetryMatchedNotices` derives strictly positive
  credit if an arrived tile lacks its own notice. Exact settled wait state then
  forces both own notices into every lane's pre-wait prefix. Their phase is
  exactly `tile/2`, with pending zero and positive credit before the notice.
  `RetryArbitraryObservations` proves actual indexed observations and the
  existing `Access.CompletionObserved` relation for arbitrary histories, including
  rejection of a different same-slot tile. Its completed-positive-candidate
  entry reconstructs the reply family from existing source completeness and
  TMA/control components. No constructed-history equality, desired operand
  value, successful observation or new semantic assumption is a premise.
- Tests/nonvacuity: twenty facts cover arbitrary actual histories and real
  inputs, all lanes and both copy kinds, first/reused lifetime/phase stamps,
  old/future notice rejection and existing joint source/TMA/control/memory/tensor/
  observer witnesses. A valid reset lowers phase, demonstrating why lifetime
  exclusion matters. Duplicate notices retain count two against one arrival.
  The prior late peer-wait history is rejected via exact wait state. A second
  actual three-tile history swaps an expect with its own A notification:
  protocol, source order, uniqueness and exhaustive inventory survive, while
  the early prefix has one completion, no arrivals and transaction debt -2048.
  The derived nonnegative-credit rule rejects its unified control admission.
- Reuse/research status: the same parent-count rule handles the 2048- and
  256-byte notification classes, prefix nonnegativity, missing-notice positivity
  and notification/wait observations. This is semantic/proof baseline work,
  not a new ownership protocol, measured optimization or agentic-method result.
  Eight modules contain 1005 lines, 44 rules and twenty facts; the focused test
  module checks in about 2.6 seconds. Existing heartbeat limits are unchanged;
  no semantic axiom or native decision procedure is introduced.
- Remaining: arbitrary-history completion observations are now closed in the
  current positive-K model. Full publication/native RF/input/output refinement
  must still consume these observations instead of the constructed history.
  Allocation/in-flight lifetime, Iris/runtime and physical observer connections
  remain open. All seven required cases remain partial; exact paper 81-form
  parity stays unconfirmed. No TTGIR, new GPU execution, IEEE/logits/token or
  performance result is added.
- Validation: `/tmp/ptx-arbitrary-observations-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated PTX-to-Lean comparisons, 3672 Lean jobs, 6702
  audited declarations and 6671 environment-resolved public theorem names,
  all 660 strict assertions individually refuted and 30 PTX examples assembled.
  All 64 new proofs have exact audit entries. New negative facts remain separate
  from the unchanged strict batch. Existing control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 15:22:01 UTC; all 30 source hashes
  are current. GPU evidence remains 2026-11-05 07:46:53 UTC, with 15 current
  hashes and 25 sm_89 cases (24 exact-byte, one completion-only). No new Hopper
  hardware execution or GPU measurement is added.
- Goal ledger snapshot at 2026-11-06 15:22:17 UTC: 13,541,837 tokens versus
  the preceding published 13,436,685, a difference of 105,152. Interim tool usage,
  not final billed usage or a completion report. The full original goal remains
  active. Next: generalize publication, native byte-order/RF and tensor input
  correspondence to consume these arbitrary-history observations, then connect
  the existing accumulation and final observer/output proofs.

### 2026-11-06 — Arbitrary-history publication, actual inputs and GEMM observation

- Instance: existing positive-K Hopper double-buffer GEMM with independent real
  inputs/frame, finite heterogeneous retries, fixed 64x8 geometry and K at most
  2^28. No PTX, source synchronization, precision or arithmetic model changes.
- Limitation: completion observations had been generalized, but downstream
  publication/native RF/tensor input/output rules still used `retryHistories`.
  Their old signatures prevented applying the result to arbitrary admitted
  resource histories. Source-oracle operands alone do not establish inputs.
- Interface/method: `RetryPublicationInterface` isolates the actual per-byte
  producer-to-native-read order as `NativePublicationFacts`. The constructed
  implementation reuses the earlier regression proof. The arbitrary-history
  implementation derives actual TMA readiness and native publication from the
  existing TMA/control components and the new completion observations. Public
  correctness entries derive this interface internally; it is not a new
  readiness, RF choice or desired-value premise.
- Memory connection: `RetryPublicationPhases` classifies all actual writer
  phases using source inventories, publication and native completion/reuse.
  `RetryPublicationMemory` derives no taint, mixed-size exclusion/eligibility and
  current RF from the existing full memory conditions; it rejects stale/future
  sources and initialization-only coherence on reused bytes. Reuse continues
  to require native completion rather than mbarrier completion.
- Data/arithmetic connection: three existing transfer-byte/producer-storage
  rules in `RetryTensorInputs` are generalized over histories without new
  premises. `RetryPublicationTensor` combines those independently represented
  input values with derived actual RF, identifies native matrix inputs, and
  uses the same fixed-instruction TensorConditions for accumulation and stores.
- Result: `RetryArbitraryOutput` proves actual operand bytes, tensor input
  agreement, final GEMM matrix bytes and unchanged observed global frame bytes
  over arbitrary admitted histories/RF/co/observers. All source/TMA/control,
  memory, input representation, tensor semantics and observer obligations stay
  explicit. Its completed-candidate entry reconstructs the actual reply family
  and exposes the existing tensor-instruction obligation for that family; source
  completion alone is not tensor arithmetic admission.
- Tests/nonvacuity: fifteen facts use independent real inputs and heterogeneous
  retries. Universal fixtures vary histories, RF/co and observers. Existing
  joint source/TMA/control/full memory/tensor/observer witnesses instantiate the
  new result, including exact-real value 96 and adjacent frame byte 17. Both
  publication implementations feed the generic RF backend. Initial/stale/future
  reads, initialization-only reused coherence, inconsistent operand bytes and a
  final observer corrupted to zero are rejected. These facts do not add GPU
  execution evidence or claim IEEE equivalence.
- Cost/research status: six new files contain 576 lines, 27 rules and fifteen
  facts; three old payload rules acquire history parameters while retaining
  their audited names and proof bodies. The focused test checks in about 1.9
  seconds. Existing heartbeat budgets remain unchanged; no semantic axiom,
  native decision procedure, numerical relaxation, new ownership protocol,
  measured optimization or agentic-method result is added. This is a reusable
  proof interface connecting notification publication and native memory input
  reasoning, still baseline semantic engineering.
- Coverage bookkeeping: both Hopper summaries in `coverage.toml` now describe
  current results and open boundaries concisely. Historical step-by-step
  evidence remains here; stale earlier `remaining` statements no longer obscure
  the closed arbitrary-history component.
- Remaining: current-model positive-K all-history input/output refinement is
  closed under the existing source/TMA/control/memory/tensor/observer components;
  zero-K was already closed. A unified source-independent admission entry and
  full requirement audit remain, alongside allocation/in-flight ownership and
  the checked Iris/event/runtime adapter. Compiler/physical-memory/observer
  assumptions must stay explicit and require an evidence audit, not an invented
  claim of hardware correspondence. All seven required cases remain partial;
  exact paper 81-form parity is unconfirmed. No new GPU or performance result.
- Validation: `/tmp/ptx-arbitrary-output-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated PTX-to-Lean comparisons, 3678 Lean jobs, 6744
  audited declarations and 6713 environment-resolved public theorem names,
  all 660 strict assertions individually refuted and 30 PTX examples assembled.
  All 42 new proofs have exact audit entries; the three generalized old rules
  remain in their existing audit entries. Existing control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
  Reconciled metadata passes a separate coverage-structure check; no proof code
  changed after the full gate.
- Assembly evidence refreshed at 2026-11-06 15:37:50 UTC, all 30 source hashes
  current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 current hashes
  and 25 sm_89 cases (24 exact-byte, one completion-only). No new Hopper hardware
  execution or GPU measurement is added.
- Goal ledger snapshot at 2026-11-06 15:39:24 UTC: 13,613,285 tokens versus
  the preceding published 13,541,837, a difference of 71,448. Interim tool usage,
  not final billed usage or a completion report. The full original goal remains
  active. Next: combine source/TMA/control/memory/tensor/observer obligations in
  a source-independent acceptance entry, audit the remaining case requirements,
  then continue the checked allocation/in-flight ownership and Iris/event/runtime
  connection without treating external hardware assumptions as proved facts.

### 2026-11-06 — Unified actual-instruction admission, correctness and nonvacuity

- Instance: the same bounded-K, fixed-geometry Hopper double-buffer source and
  independent exact-real matrix/frame representation, including zero K and
  arbitrary finite heterogeneous lane/tile retries. No PTX or numerical model
  changes are made.
- Limitation: the completed-candidate output entry reconstructed a source family
  and then exposed a per-family tensor obligation. A caller needed to combine
  several components manually, leaving instruction coverage and the equivalence
  of a source-independent tensor condition to be checked explicitly.
- Method: `UnifiedExecution` packages existing source/TMA completeness, full
  unified control, memory, tensor and observer components in one record. Tensor
  admission requires coverage of every actual MMA and semantics for every actual
  source-matched collective. Coverage is separate from the arithmetic condition,
  so an orphan MMA cannot disappear behind vacuous collective quantification.
- Equivalence: `TensorAdmission` classifies each actual collective by its
  source-proved tile/group and lane identities, deriving its exact call family
  and source IDs. It proves candidate-wide tensor admission equivalent to the
  earlier per-tile TensorConditions under the existing source proof. Coverage
  is derived from actual MMA source cases. The unified Hopper entry therefore
  neither adds an unproved readiness/result premise nor silently strengthens
  the case's tensor assumptions.
- Result: `HopperDoubleBufferExecution.execution_refines_gemm` handles zero and
  positive K through one source-independent admission entry, over arbitrary
  admitted candidates/histories/RF/co/observers and matching represented initial
  proxy memory. `gemm_execution_exists` constructs all components and the result
  for every given bounded K/retry schedule; its positive branch explicitly
  retains a source-family witness with the requested schedule. The zero branch
  proves absence of MMA while retaining all output stores and final observation.
  A two-execution theorem derives equal matrix fragments for the same represented
  input and fixed kernel plan, including different retry schedules. These are
  model equalities, not physical IEEE or logits/token claims.
- Tests/nonvacuity: sixteen facts check zero/positive complete witnesses, retained
  schedules, two different retry schedules with equal output, nonzero result 96,
  adjacent frame byte 17 and coverage of every actual source MMA. Mixed-tile
  collective grouping, missing lanes, wrong arithmetic under any chosen memory,
  corrupted output and missing observer coverage are rejected. The isolated
  orphan/bad-collective fixtures test the tensor component alone and are not
  claimed as fully source/control-admitted PTX counterexamples.
- Reuse/cost: four new modules contain 386 lines, twelve authored rules and
  sixteen test facts; the focused test checks in about 1.9 seconds with unchanged
  heartbeat limits. The same package handles zero/no-native execution and
  positive native execution, while the tensor equivalence bridges source-level
  per-tile proofs and the candidate-wide interface. This is baseline semantic
  proof composition, not a new ownership protocol or measured optimization.
- Audit feedback: the first full check identified three generated proof
  projections (`ExecutionComponents.control`, `.memory`, `.observer`) missing
  from the explicit dependency audit. They now have exact audit entries, in
  addition to all authored proofs. No proof or admission condition was weakened
  to bypass the checker.
- Remaining: the unified Hopper current-model admission/correctness/nonvacuity
  entry is now checked. The full paper requirement/instruction inventory review,
  checked allocation/in-flight ownership and Iris/event/runtime adapters remain.
  Inspection confirms that the existing Iris transition/heap rules operate on
  the abstract async state and separated buffer fragments; they do not yet map
  outstanding actual GPU accesses to those loans. This is the next connection
  to establish. Compiler, physical-memory and observer assumptions remain
  explicit audit boundaries. All seven required cases remain partial and exact
  paper 81-form parity is unconfirmed; no new GPU or performance result is added.
- Validation: `/tmp/ptx-unified-execution-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated PTX-to-Lean comparisons, 3682 Lean jobs, 6775
  audited declarations and 6744 environment-resolved public theorem names,
  all 660 strict assertions individually refuted and 30 PTX examples assembled.
  All 28 authored proofs and the three generated proof projections have exact
  audit entries. Existing control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 15:58:14 UTC; all 30 source hashes
  are current. GPU evidence remains 2026-11-05 07:46:53 UTC with 15 current
  hashes and 25 sm_89 cases (24 exact-byte, one completion-only). No new Hopper
  hardware execution or GPU measurement is added.
- Goal ledger snapshot at 2026-11-06 15:59:14 UTC: 13,682,187 tokens versus
  the preceding published 13,613,285, a difference of 68,902. Interim tool usage,
  not final billed usage or a completion report. The full original goal remains
  active. Next: interpret actual outstanding GPU access/completion prefixes in
  the existing async loan/heap protocol, prove safe return/reuse conditions and
  connect the Iris rules to that interpretation; continue the full case and
  instruction-inventory audit without treating model packaging as hardware proof.


## Research record: actual access prefixes and prepared-plan loan completion

- Instance and missing capability: the existing async FIFO protocol could advance
  an entire abstract copy/use command and its counter without any link to the
  actual TMA descriptor/data or WGMMA operand accesses. Its resource-return
  theorem alone therefore did not establish completion of actual GPU accesses.
- `ControlPrefix` defines one-actual-node advances with all control predecessors
  already seen. Reached prefixes are valid and finite; validity and completion
  are monotone. Rank cuts supply structural closure only, not reachability.
- `InFlightAccess` identifies actual 128-byte tensor-map reads, TMA source reads
  and destination writes, and native operand reads. Source well-formedness
  supplies every in-bounds TMA payload byte. A TMA completion certificate requires
  a positive-sized actual copy, observation of that copy's own barrier phase and
  the actual true-wait endpoint; native work requires its own native group wait.
  Closure then puts every associated use before the observed completion. The
  descriptor path explicitly uses a data byte, hence zero-sized copies are not
  silently admitted by this rule.
- `Async.CompletionClock` proves exact counter changes in the original executable
  interpreter, covered-ticket completion, and that a loan actually removed by
  successful acquisition was complete before acquisition. `CompletionBridge`
  couples that protocol with the access prefix and a fixed ticket/work plan.
  A mapped device ticket advances only with a source-matched completion
  certificate. Access, host and device transitions preserve faithful counters,
  reached prefixes and the protocol invariant; finite runs inherit those facts.
  An actually removed mapped loan implies all of that work's actual uses are
  done. An unfinished use keeps its mapped loan after acquisition of an older
  event. Host actions here are record/acquire/reclaim/write on a prepared plan;
  dynamic submission is not yet connected.
- Reuse evidence: the same access-completion and ticket/loan rules cover TMA and
  WGMMA. Seventeen facts use the existing admitted independent-input data GEMM
  family for actual descriptor, tensor and native uses and own completion
  certificates. They check early acquisition with both descriptor and native
  work, structural cutoff rejection, future-loan retention after an old event,
  rejected reclamation/writes, and a device action that the old counter model
  would accept but the new actual-completion guard rejects. The prepared-plan
  regression binds a logical ticket to work; it does not identify a real
  allocation or claim that abstract value 17 represents the GPU tensor bytes.
- Cost and limits: five modules, 634 lines, 35 authored rules and 17 facts, with
  unchanged heartbeat limits. Focused tests check in about 1.2 seconds. This is
  a semantic adapter slice, not a measured optimization or a new concurrency
  logic. Positive reachable complete coupled execution witnesses, dynamic plan
  construction, actual command/allocation/location binding, Iris integration and
  physical runtime refinement remain open. Existing joint GEMM execution
  witnesses establish the underlying candidate's admissibility, not coupled
  prefix execution nonvacuity. No physical byte-value simulation follows from
  this bridge.
- Scope: all seven required cases remain partial and exact paper 81-form parity
  remains unconfirmed. No TTGIR frontend, new GPU run, IEEE/logits/token or
  performance result is added. The original goal remains active.
- Validation: `/tmp/ptx-completion-bridge-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated-file comparisons, 3687 Lean jobs, 6827 audited
  declarations and 6796 environment-resolved public theorem names, all 660
  existing strict assertions individually refuted, and 30 PTX fixtures
  assembled. All 52 new authored proofs have exact dependency-audit entries.
  Existing control test SHA-256 remains
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly report refreshed at 2026-11-06 16:34:07 UTC. GPU report remains
  2026-11-05 07:46:53 UTC; no new GPU execution is claimed.
- Goal ledger snapshot at 2026-11-06 16:34:40 UTC: 13,881,586 tokens versus
  the preceding published 13,682,187, a difference of 199,399. This is interim
  tool accounting, not final billed usage or a completion report. Next: establish
  reachable positive complete coupled runs, bind actual allocations/locations and
  protocol commands, then connect the coupled interpretation to Iris rules;
  continue the original requirement and instruction-inventory acceptance audit.


## Research record: reachable actual prefixes and positive loan-return runs

- Previous turn classification: progress. It added and fully checked the
  actual-access/completion-to-logical-loan bridge. The remaining concrete gap
  was nonvacuity of coupled complete runs: a structural rank cut alone was not
  shown reachable, and might contain absent nodes.
- `PrefixExistence` proves a finite valid downward-closed ranked cut can be
  reached one actual node at a time. The proof removes a maximal-ranked node,
  executes the remaining closed cut, then adds that node with all predecessors
  already present. This is a generic finite graph existence proof; no scheduler
  fairness, successful runtime wait, memory value or new completion axiom is
  assumed.
- `ControlInventory` supplies a finite upper inventory from actual source event
  IDs, actual copies and their descriptor byte counts, and all 2304 native
  operand bytes. It proves coverage of every actual control node. Extra entries
  are filtered by `Present`. `ControlPresence` derives actual endpoints of all
  source, CTA, TMA, native and resource control edges; resource endpoints require
  the existing checked source-matched `HistoryValid` records. Arbitrary raw
  histories are not silently admitted.
- `CompletePrefix` combines these facts: the full actual cut and every bounded
  actual rank cut have reachable prefixes. Bounded cuts require both presence
  and rank, so rank zero does not create a nonexistent operation.
  `PrefixExecution` lifts each such run into the coupled protocol while keeping
  prepared commands and loans fixed. `HopperDoubleBufferProgress` derives full
  positive-K data-GEMM prefix reachability from the existing source/history and
  strict-order proofs for all bounded K and finite heterogeneous retry schedules.
- Sixteen facts instantiate the admitted independent-input data GEMM family:
  complete actual prefixes; actual reachable unfinished-native cuts with rejected
  completion; own TMA/native completion; real interpreter device/acquire/reclaim
  actions; complete coupled runs for both work types; faithful counters and
  protocol invariant preservation; empty loans after reclamation; and rejection
  of a ghost prefix on an empty candidate. Prepared protocol validity is derived
  from public actions on the initial protocol, with only irrelevant event-list
  order changed. No positive reachable-prefix hypothesis is supplied by a caller
  in these source-family witnesses.
- Reuse/cost: seven modules, 418 lines, fourteen public rules, two local helper
  proofs and sixteen test facts; no heartbeat limits were raised. Focused tests
  check in about 1.3 seconds. The same graph execution/loan return rules serve
  TMA and WGMMA. Both clients deliberately use a logical prepared `use` ticket;
  the mapping does not yet prove that a concrete runtime command or allocation
  implements the GPU operation, or that scalar value 17 represents tensor bytes.
  This is baseline nonvacuity/semantic composition, not a performance result or
  a new concurrency-logic contribution.
- Remaining: the positive prepared-model prefix/run existence gap is closed.
  Actual allocation/byte-location and command binding, dynamic submission,
  memory-value transition correspondence, coupled Iris ownership/WP and CUDA
  runtime refinement remain. A control-graph linearization does not prove actual
  GPU scheduling fairness or eventual request completion. All seven required
  cases remain partial and exact paper 81-form parity remains unconfirmed; no
  TTGIR implementation, new GPU execution, IEEE/logits/token or performance
  result is added. The full original goal remains active.
- Validation: `/tmp/ptx-prefix-execution-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated-file comparisons, 3694 Lean jobs, 6857 audited
  declarations and 6826 environment-resolved public theorem names, all 660
  strict assertions individually rejected, and 30 PTX fixtures assembled. All
  thirty new public proofs have exact dependency-audit entries. Existing control
  tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly report refreshed at 2026-11-06 16:48:54 UTC with all thirty hashes
  current. GPU report remains 2026-11-05 07:46:53 UTC with fifteen current
  source hashes; no new GPU execution or performance claim is made.
- Goal ledger snapshot at 2026-11-06 16:49:16 UTC: 13,959,922 tokens versus
  the preceding published 13,881,586, a difference of 78,336. This is interim
  tool accounting, not final billed usage or a completion report. The full
  original goal remains active. Next: bind loans and protocol commands to actual
  byte regions and outstanding accesses, then connect that interpretation to
  Iris ownership/WP. Existing Iris heap rules still describe abstract scalar
  buffers, so they cannot yet be claimed to own the actual GPU byte locations.
  Continue the full case and instruction-inventory acceptance audit.


## Research record: selected-work byte regions and retained loans

- Previous turn classification: progress. It checked reachable actual prefixes
  and positive coupled return/reuse. Its prepared clients still associated work
  with scalar-buffer tickets without proving which actual byte regions each
  borrowed buffer protected.
- `RegionLoans` adds finite binding data with work, ticket, buffer, exact mode
  and a modeled byte region. `Mapped` checks ticket/work and layout identity;
  `Covers` quantifies over every actual use in a declared work scope, including
  its mode and byte location; `Separated` excludes overlapping regions under
  different buffer IDs. `Borrowed` requires a real live protocol loan for every
  incomplete bound ticket. All four conditions are checked for the concrete
  clients, rather than added as unproved premises to the GEMM correctness entry.
- `Async.LoanPreservation` proves properties of the existing executable
  interpreter: device steps preserve loans and advance completion monotonically,
  host acquire retains any incomplete ticket, and successful record, write or
  reclaim cannot invalidate an existing held loan. `Borrowed` is then preserved
  by every coupled finite access/host/device run. Faithful actual completion and
  a reachable prefix turn an unfinished actual use into a live, mode-matching
  region loan. Separation identifies the buffer for any containing region, so
  its reclaim or host overwrite is rejected. Without separation, an aliasing
  buffer ID could otherwise bypass the borrowed buffer's check.
- Source coverage: `HopperDoubleBufferRegions` derives all actual locations from
  the existing source family and descriptor agreement. Native reads cover both
  shared A/B operand regions; a selected TMA-A copy covers the complete 128-byte
  descriptor, global input A bytes and shared destination writes. The checks are
  parameterized by bounded tile count, tile and arbitrary captured replies/
  retries; no desired footprint is substituted for the source use. Constant
  descriptor byte counts use normalization lemmas, with no recursion/heartbeat
  limit increase.
- Seventeen facts use the independently admitted data GEMM fixture. Native
  preparation borrows two operand buffers through public `use` actions; TMA
  preparation borrows its descriptor via `use` and source/destination via `copy`.
  Public preparation, protocol validity, nonvacuous borrowing and faithful
  initial counters are checked. For every finite coupled run, any remaining
  selected native/TMA-A use blocks reclamation of its containing region. Full
  actual prefix/device/device/acquire/host-write runs return the loans and allow
  reuse for both clients. Negative certificates reject overlapping IDs, an
  undersized region, replacing target write permission with read permission,
  and omitting descriptor coverage.
- Cost/reuse: four modules, 534 lines, nineteen public rules, one normalization
  helper and seventeen facts. The same preservation/region safety rules cover
  TMA and WGMMA with distinct read/write footprints. This is baseline semantic
  binding, not a measured optimization or a new ownership-logic contribution.
- Limits: region addresses and actual uses are connected in the model, but the
  layout is not a CUDA allocation certificate. The prepared protocol actions
  are lifetime clients, not proven implementations of GPU launches; their Nat
  values are not a tensor-byte simulation. Whole-kernel/B-transfer/ordinary and
  resource-operation coverage, dynamic plans and layout generations, byte-value
  correspondence, actual allocation/command refinement and coupled Iris/WP/
  runtime interpretation remain. The declared work scope is explicit and does
  not silently claim protection of every operation in the kernel. All seven
  required cases remain partial and exact paper 81-form parity is unconfirmed;
  no TTGIR, new GPU execution, IEEE/logits/token or performance result is added.
- Validation: `/tmp/ptx-region-loans-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated-file comparisons, 3698 Lean jobs, 6893 audited
  declarations and 6862 environment-resolved public theorem names, all 660
  strict assertions individually rejected, and 30 PTX fixtures assembled.
  All thirty-six new public proofs have exact dependency-audit entries. Existing
  control regression SHA-256 is unchanged:
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 17:06:21 UTC with thirty current
  source hashes. GPU evidence remains 2026-11-05 07:46:53 UTC with fifteen
  current hashes; no new GPU execution or performance result is claimed.
- Goal ledger snapshot at 2026-11-06 17:07:06 UTC: 14,030,399 tokens versus
  the preceding published 13,959,922, a difference of 70,477. This is interim
  tool accounting, not final billed usage or a completion report. The original
  goal remains active. Next: extend checked region bindings to B transfers and
  whole-kernel/ordinary-resource uses, establish the full prepared-plan ownership
  invariant, then connect the coupled actual-region interpretation to Iris/WP.
  Runtime allocation/command, dynamic-layout/generation and byte-value refinement
  remain separate obligations; continue the full paper acceptance audit.


## Research record: aggregate A/B/native async region certificates

- Previous turn classification: progress. It checked source-derived region
  bindings and retained loans for a selected A copy or native collective. It
  lacked B transfer coverage, a shared layout across work items and proof that
  every actual async use was included without a selected-work premise.
- `HopperDoubleBufferBRegions` derives the distinct 128-byte descriptor, B input
  base and 256-byte shared destination from the source, with read/write coverage
  for every B transfer byte. `RegionComposition` preserves exact work, mode and
  region through logical buffer/ticket renaming and subset composition. A
  generic pairwise region-disjointness proof supplies layout separation. A
  Boolean held-loan check is proved equivalent to the actual protocol predicate;
  finite metadata checks therefore do not need an assumed loan witness.
- `HopperDoubleBufferAsyncBindings` uses eight separated modeled regions:
  descriptors A/B, global inputs A/B and shared A/B for both slots. Six tickets
  per tile identify descriptor/copy A, descriptor/copy B and native operand A/B
  clients; copies have source/destination loans at one ticket. Ticket decoding
  checks stream, positive sequence and the plan bound. Every binding matches the
  shared layout and actual work identity; slot reuse keeps the same buffer ID
  but receives new tickets.
- `HopperDoubleBufferAsyncCoverage` exhaustively classifies every actual
  `Progress.Use` into an in-range source tile's A copy, B copy or native issue.
  It composes local certificates into global coverage with scope `True`.
  `completed_async_region_certificate` reconstructs the source family from the
  existing well-formed/complete/descriptor components and produces separated,
  mapped coverage without a new selected-footprint or guessed-family premise.
  This still covers the asynchronous Use constructors, not ordinary or resource
  source operations that are outside that datatype.
- `HopperDoubleBufferAsyncCompletion` discharges every mapped ticket's own-phase
  TMA/native completion on the full actual prefix. `ProtocolScript` lifts a
  prepared script one actual interpreter command/coupled step at a time. Its
  language includes device and record/acquire/reclaim/write commands; dynamic
  issue/wait is outside this API. No source/event completion guard is bypassed
  by simply declaring a script successful.
- Twenty-three facts use the independent-input data GEMM family and a concrete
  publicly prepared three-tile protocol. Public preparation yields eighteen
  commands and twenty-four actual loans across eight buffers; protocol validity,
  faithful clocks and every aggregate borrowed binding are checked. All pending
  async uses, across both copies/native and all three tiles, block reclaim of
  their containing regions under every coupled finite execution. A full actual
  prefix followed by device/acquire/write steps returns all loans and reuses
  shared A. Separate interpreter regressions show an old event removes tile-zero
  loans but keeps tile-two loans on the same slot, rejecting reclaim/overwrite.
  Those regressions do not claim a specific unfinished physical GPU schedule.
  Zero/wrong-stream tickets, a B ticket naming A, and omission of all B descriptor
  bindings are rejected.
- Cost/reuse: seven modules, 544 lines, twenty-one public rules, one local byte
  count normalization helper and twenty-three facts. Focused tests check in
  about 2.9 seconds with unchanged heartbeat/recursion limits. Shared composition
  rules cover both transfer sizes and native consumers; prepared clients now
  combine work over slot reuse. This is baseline semantic composition, with no
  measured optimization or new ownership-logic contribution claimed.
- Limits/next: global source coverage, mapping, full-prefix reachability and
  completion rules quantify over bounded positive tile count and arbitrary
  finite heterogeneous replies. Public preparation/initial borrowing and a
  complete coupled protocol are checked here for three tiles; a generic public
  preparation theorem is still needed. Ordinary/resource source ownership,
  whole-kernel and zero-K ownership integration, dynamic layout generations,
  allocation/command and byte-value/operational correspondence, Iris/WP and CUDA
  runtime refinement remain. No hardware scheduling fairness or eventual request
  completion follows. All seven required cases remain partial and exact paper
  81-form parity is unconfirmed; no TTGIR, new GPU execution, IEEE/logits/token or
  performance result is added. The original goal remains active.
- Validation: `/tmp/ptx-aggregate-async-regions-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated-file comparisons, 3705 Lean jobs, 6937 audited
  declarations and 6906 environment-resolved public theorem names, all 660
  strict assertions individually rejected, and 30 PTX fixtures assembled. All
  forty-four new public proofs have exact dependency-audit entries. Existing
  control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly report refreshed at 2026-11-06 17:27:42 UTC with all thirty source
  hashes current. GPU report remains 2026-11-05 07:46:53 UTC with fifteen
  current hashes; no new GPU execution or performance claim is made.
- Goal ledger snapshot at 2026-11-06 17:28:48 UTC: 14,097,517 tokens versus
  the preceding published 14,030,399, a difference of 67,118. This is interim
  tool accounting, not final billed usage or a completion report. The full
  original goal remains active. Next: prove generic public preparation/initial
  borrowing for the aggregate plan, with fresh indexed event IDs rather than
  generalizing the finite client's fixed event labels; extend ordinary/resource
  operation ownership, then connect the coupled region state to Iris/WP and
  runtime/byte-value refinement. Continue the full paper acceptance audit.


## Research record: parameterized public preparation and loan provenance

- Previous turn classification: progress. It checked global async coverage and
  a complete three-tile coupled client, but initial borrowing and public
  preparation had only a finite instance. Arbitrary tile counts could not rely
  on that instance, and its fixed event labels could collide when generalized.
- `Async.Preparation` derives public `use`/`copy` readiness from the existing
  executable protocol. Ready states have one unexecuted stream, live buffers and
  loans to already issued tickets. A request updates loans and then enqueues its
  command, advancing the common upper bound. Copy readiness handles its two
  borrows in order and uses actual source/destination inequality to show that
  the first borrow does not alter the second buffer. No readiness, successful
  action or new ownership axiom is assumed. The request datatype admits only
  the supported public use/copy operations.
- `HopperDoubleBufferPreparation` proves by induction that all finite tile
  counts and arbitrary eight initial scalar values produce a successful real
  public run. Each tile's six requests are followed by an indexed record;
  event IDs are exactly a reversed finite range, so freshness and uniqueness
  follow for every count. The separate final event has the exact recorded
  frontier `(0,6*tiles)`. The prepared state has the actual queue, live buffers,
  issued-loan bounds and the original protocol invariant. The fallback branch
  in its total definition is proved unreachable under the stated eight-value
  resource layout; it is not used to turn failure into success.
- `HopperDoubleBufferPreparedLoans` proves every queue index `6*tile+part`
  contains the expected command. The original executable protocol invariant
  therefore supplies each binding's exact real loan, including both source/read
  and destination/write loans at a copy ticket. This derives `Borrowed` for the
  complete aggregate binding list without a caller premise, for every finite
  tile count and any source-family data. Faithful initial completion follows
  from the zero counters. Source-derived region reclaim and host-write rejection
  now quantify over bounded positive tile count and every coupled finite run,
  with all initial permission facts produced by public actions.
- Eighteen facts check the parameterized preparation, unique events and exact
  final frontier; four-tile concrete queue/loan counts; zero-work empty queue and
  loans, distinct events and successful zero-frontier acquire; 90-tile symbolic
  instantiation without the former fixed event-ID collision; actual duplicate
  final-event rejection; all binding provenance; and writes/readers across two
  uses of the same slot. The 90-tile facts instantiate the generic proof and are
  not reported as GPU execution or a benchmark.
- Cost/reuse: four modules, 449 lines, twenty-six public rules, one local event
  freshness helper and eighteen facts. Focused tests check in about 1.4 seconds;
  no heartbeat/recursion limit was raised. The public readiness rule is reusable
  beyond this kernel, and the source-family binding proof retains arbitrary
  captured replies and retry schedules. This is baseline proof/semantic
  composition, with no measured optimization or new concurrency-logic claim.
- Remaining: generic preparation and initial loan provenance are closed.
  Complete coupled drain/return still has the earlier three-tile witness;
  parameterized drain/return, ordinary/resource source ownership, whole-kernel
  and zero-K source ownership integration, dynamic layouts/generations,
  allocation/command and byte-value/operational correspondence, coupled Iris/WP
  and CUDA runtime refinement remain. Eight scalar resources are a logical
  client layout, not a tensor-byte or physical-allocation representation.
  No physical scheduling fairness, eventual request completion or new GPU
  execution follows. All seven required cases stay partial, exact paper 81-form
  parity stays unconfirmed, and no TTGIR/IEEE/logits/token/performance result is
  added. The full original goal remains active.
- Validation: `/tmp/ptx-parametric-preparation-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated-file comparisons, 3709 Lean jobs, 6981 audited
  declarations and 6950 environment-resolved public theorem names, all 660
  strict assertions individually rejected, and 30 PTX fixtures assembled. All
  forty-four new public proofs have exact dependency-audit entries. Existing
  control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly report refreshed at 2026-11-06 17:48:45 UTC with thirty current
  source hashes. GPU report remains 2026-11-05 07:46:53 UTC with fifteen
  current hashes; no new GPU execution or performance claim is made.
- Goal ledger snapshot at 2026-11-06 17:49:43 UTC: 14,164,070 tokens versus
  the preceding published 14,097,517, a difference of 66,553. This is interim
  tool accounting, not final billed usage or a completion report. The full
  original goal remains active. Next: derive generic FIFO drain/return from the
  real protocol invariant, no-wait prepared commands and the exact final event;
  lift it through the checked all-completed prefix/script rule. Then continue
  ordinary/resource and zero-K ownership integration, Iris/WP and runtime/value
  correspondence, together with the full paper acceptance audit.


## Research record: parameterized FIFO drain, loan return and coupled existence

- Previous turn classification: progress. It proved public preparation and every
  initial region loan for arbitrary tile count. Complete drain/return still had
  only the earlier finite three-tile witness, so a general coupled completion
  theorem could not assume that arbitrary queues would successfully finish.
- `Async.Drain` constructs a real FIFO interpreter execution by induction over
  a no-wait queue. The original protocol invariant supplies valid live accesses
  for each head command; each device action pops exactly one command and advances
  exactly one completion counter. A resource-frame theorem proves event records
  and every buffer's alive/loan pair remain unchanged while copy values may
  change. This transfers live/bounded-loan facts through the whole execution.
- Final acquisition uses the actual recorded frontier and real completion test.
  Since every retained loan belongs to that stream and is bounded by the final
  sequence, the actual await filter returns every loan. The post-state has live
  buffers, the original buffer count, empty loans and exact complete/issued
  clocks. No success, fairness or runtime-progress fact is supplied as a premise.
  No-wait is a genuine scope condition, derived from the typed use/copy request
  language rather than assumed for arbitrary protocol programs.
- `HopperDoubleBufferLoanReturn` instantiates the drain theorem for all finite
  tile counts and arbitrary eight initial scalar values. It proves the complete
  public prepare/device/acquire run succeeds, the total returned-state fallback
  is unreachable, and any valid modeled buffer can subsequently be written or
  reclaimed. For bounded positive-K source families with the existing checked
  TMA/source/history components, the reachable actual prefix plus own-phase
  completion certificates lift this public run into a complete coupled execution.
  No caller-supplied successful drain or initial Borrowed fact is added.
- The pending reclaim/write wrappers were also generalized from the constructed
  retry history to arbitrary resource-history environments in the coupled run.
  Their proofs use the existing source-derived global coverage, public borrowing,
  faithful completion and prefix closure; complete execution existence may still
  choose the independently admitted constructed history. This keeps universal
  safety and existential nonvacuity scopes distinct.
- Sixteen facts check parameterized public completion/return/reuse/reclaim,
  zero-work identity, a concrete four-tile full clock and empty loan state,
  both slots' actual scalar copy updates, a 90-tile symbolic return, rejected
  acquisition before progress and one command before the final frontier, and
  arbitrary independent-input data-family coupling. A self-waiting queue has
  a checked protocol invariant but its real device step returns notComplete;
  it is not Plain. This rejects a blanket termination inference from the
  lifetime invariant alone. These are model/formal execution facts, not GPU runs.
- Cost/reuse: three new modules, 317 lines, twenty-one public rules and sixteen
  facts, plus the two existing guard signature generalizations. Focused tests
  check in about 1.7 seconds with unchanged heartbeat/recursion limits. The FIFO
  drain/resource-frame theorem is reusable for other prepared use/copy clients;
  source-prefix/script lifting reuses the previous TMA/native rules. This is
  baseline composition, not a new concurrency logic or measured optimization.
- Remaining: generic prepared async client execution/return is now checked.
  Ordinary/resource source ownership, whole-kernel/source-zero ownership,
  dynamic layouts/generations, allocation/command and byte-value/operational
  correspondence, coupled Iris/WP and CUDA runtime refinement remain. Eight
  scalar resources still do not represent tensor bytes or CUDA allocations.
  Finite chosen no-wait executions do not prove physical scheduling fairness or
  eventual request completion. All seven required cases stay partial and exact
  paper 81-form parity stays unconfirmed; no TTGIR/IEEE/logits/token/performance
  or new GPU result is added. The full original goal remains active.
- Validation: `/tmp/ptx-parametric-loan-return-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six harness tests, generated-file comparisons, 3712 Lean jobs, 7018 audited
  declarations and 6987 environment-resolved public theorem names, all 660
  strict assertions individually rejected, and 30 PTX fixtures assembled. All
  thirty-seven new public proofs have exact dependency-audit entries. Existing
  control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly report refreshed at 2026-11-06 18:05:07 UTC with thirty current
  source hashes. GPU report remains 2026-11-05 07:46:53 UTC with fifteen
  current hashes; no new GPU execution or performance claim is made.
- Goal ledger snapshot at 2026-11-06 18:06:44 UTC: 14,218,601 tokens versus
  the preceding published 14,164,070, a difference of 54,531. This is interim
  tool accounting, not final billed usage or a completion report. The full
  original goal remains active. Next: ordinary/resource and zero-K source
  ownership, then the coupled Iris/WP interpretation and runtime/value bridge.
  The interpreter permits overlapping queued read/write loans when stream order
  allows them. Such loans are lifetime reservations, not simultaneous active
  byte permissions; the Iris interpretation must distinguish those roles and
  justify active permission transfer using actual control/completion edges.
  Continue the full case and instruction-inventory acceptance audit.

### Mode-tagged lifetime reservations and public finite clients

- Optimization instance: ordinary output writes and mbarrier storage need
  allocation lifetime protection without an unrelated read-only source buffer.
  The previous public protocol exposed read-only use or a two-buffer copy;
  obtaining a write reservation through a fabricated copy would misdescribe
  the operation and impose unused input resources on source-zero paths.
- Implementation: `Command.access` / `Action.access` and `submitAccess` reserve
  an explicit read/write mode and enqueue an opaque FIFO resource use. The
  access task checks live storage and leaves the abstract scalar value alone.
  Its data effects are not a PTX instruction simulation. Successful public
  submission derives the exact indexed loan and immediate host write/reclaim
  rejection. Existing reachable-state invariant, queue readiness, progress,
  buffer shape and metadata-preservation proofs cover the added constructor.
- Reuse: mode-generic preparation integrates with the existing valid-request
  interpreter and no-wait drain. `Async.AccessLifetime.client_returns`
  constructs a real initial/prepare/record/device/acquire execution for any
  finite valid mixture of use/copy/mode-tagged requests and arbitrary initial
  values. It derives live buffers, returned loans, unchanged buffer count,
  exact completed clocks and the protocol invariant. This is an engineering
  extension of the existing protocol, not a new research-method claim.
- Tests: nineteen public facts cover write-only storage without a dummy input,
  arbitrary finite same-stream write reuse, unordered cross-stream read/read
  acceptance and read/write conflicts, exact overlapping same-stream ticket
  modes, host overwrite/free rejection, device completion without acquisition,
  premature and partial acquisition, dependency waits blocked on a producer,
  producer acquisition retaining consumer loans, both-stream return/reclaim,
  invalid/dead storage, and absence of fabricated scalar output updates.
  All new facts and the six added public rules have exact dependency-audit
  entries. No native_decide, new axioms or assumed initial loans are used.
- Boundaries and next work: queued reservations protect allocation lifetime;
  ordered overlapping reservations are not simultaneous active byte ownership.
  Source-level ordinary/resource coverage, whole-kernel and zero-K ownership,
  actual allocation/value/command correspondence and coupled Iris/WP remain
  open. Existing source TMA/native completion guards are unchanged. There is
  no new TTGIR frontend, compilation proof, GPU execution or performance result.
  All seven required cases remain partial; exact paper 81-form parity is still
  unconfirmed. The original unbounded goal remains active.
- Multi-frontend discussion: existing Rust parsing/serialization separation and
  Lean event/byte/resource rules offer reusable boundaries, but ISA execution
  remains PTX-specific. Direct TTGIR verification would need its own SSA,
  tensor/layout/memdesc and async semantics plus checked semantic connections.
  Verifying supported generated PTX does not establish TTGIR/compiler
  correctness. Official reference consulted this turn:
  https://triton-lang.org/main/dialects/TritonGPUOps.html and
  https://triton-lang.org/main/dialects/TritonNvidiaGPUOps.html. TTGIR work has
  not been added to this goal's acceptance scope.
- Validation: `/tmp/ptx-mode-access-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six rejection-harness tests, generated-file comparisons, 3714 Lean jobs,
  7043 audited declarations and 7012 environment-resolved public theorem names,
  660 strict assertions individually rejected and 30 PTX fixtures assembled.
  The nineteen new facts and six public rules account for all 25 new audit
  entries. Existing control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 18:22:52 UTC with thirty current
  fixture hashes. GPU evidence remains 2026-11-05 07:46:53 UTC with fifteen
  current hashes and 25 cases; no new GPU execution is reported.
- Goal ledger snapshot at 2026-11-06 18:23:09 UTC: 14,322,437 tokens versus
  the preceding published 14,218,601, a difference of 103,836. This is interim
  tool accounting, not final billed usage or a completion report. The goal
  remains active. Next: connect ordinary accesses and actual resource uses to
  source completion/lifetime coverage, then coupled Iris ownership and WP.

### Actual ordinary/resource uses and conservative source-root leases

- Previous-turn classification: progress, verified by the mode-tagged public
  access implementation and its successful full gate. This turn continues the
  original goal without adding TTGIR to its acceptance scope.
- Optimization instance and missing capability: output stores and live mbarrier
  objects were absent from `Progress.Use`, which intentionally covered only
  descriptor/TMA/native work. A generic write reservation alone supplied no
  actual source-use or completion connection. Inspection of the actual PTX
  also confirms that zero K initializes and invalidates both mbarriers before
  returning; zero K cannot be modeled as output-only lifetime ownership.
- Source-use interpretation: `Hopper.KernelUse` derives ordinary read/write
  uses from actual source `readByte`/`writeByte` lookups. Its resource uses are
  actual `Tma.resourceAt` records for source operations or transfer
  notifications and cover every offset in the mbarrier storage span. They do
  not invent ordinary byte values for opaque resource contents. This uses the
  modeled layout-v0 eight-byte storage span, following PTX ISA 8.0 section
  9.7.12.14.1:
  https://docs.nvidia.com/cuda/archive/12.0.1/pdf/ptx_isa_8.0.pdf .
  Allocation validity, alignment and physical object representation are still
  separate obligations.
- Completion: the conservative `Work.kernel` constructor requires actual
  source termination and every present control node in the completed cut.
  Ordinary/resource use presence is derived from the actual lookup, and root
  completion therefore implies that each use has occurred. Existing TMA/native
  work and their more precise observed-wait/native-completion guards are
  unchanged. Host acquisition covering a mapped root ticket cannot succeed
  while such a use remains pending.
- Public construction: `KernelLease` builds finite mode-tagged reservation
  requests through the real public interpreter, records its final event and
  derives exact indexed loans through the reachable-state invariant. It proves
  mapped-ticket faithfulness, preservation of borrowed regions and actual host
  reclaim/write rejection for any pending covered use and separated layout.
  Its public guard derives preparation facts from a successful public run;
  there is no initial-loan assumption. A reachable full actual source prefix
  followed by the actual FIFO script and final acquire constructs an entire
  coupled run with all reservations returned and buffers live.
- Source coverage and reuse: `HopperDoubleBufferKernelOwnership` proves that
  every actual ordinary-source byte access lies in output storage and every
  resource span lies in the separate two-object barrier storage region. It
  covers arbitrary completed zero-K source candidates and bounded positive-K
  reply/retry source families. Both obtain public two-buffer source-coupled
  return witnesses for arbitrary abstract initial scalar values; zero K needs
  no unrelated descriptor or input allocation. The same generic lease rules
  protect source stores and both barrier lifecycle/notification operations.
  This is an engineering extension of the existing lifetime protocol, not a
  claimed new research method or performance result.
- Tests: twenty public facts check the real public preparation, source
  well-formedness/termination, all ordinary output-store bytes, all eight bytes
  of both barriers' initialization/invalidation operations, exhaustive zero-K
  use coverage, actual presence, local termination versus prefix completion,
  derived reservations, pending source init/store guards, zero and arbitrary
  positive data-family complete coupled lifetimes, rejection of output-only
  coverage, exact storage boundaries and premature acquisition. All twenty
  facts and the twenty-seven added public rules have exact audit entries.
- Remaining: merge this conservative output/barrier client with the existing
  eight-buffer TMA/native client into one allocation/layout/launch certificate;
  then connect the resulting actual-region state to Iris ownership and WP.
  Lifetime reservations are not simultaneous active byte permissions.
  Actual allocation/command/value/runtime refinement, dynamic layouts and
  generations, complete case/instruction audits and Hopper hardware evidence
  remain. All seven required cases remain partial and exact paper 81-form
  parity remains unconfirmed. No GPU, IEEE/logits/token, performance or TTGIR
  result is added. The original unbounded goal remains active.
- Validation: `/tmp/ptx-kernel-ownership-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six rejection-harness tests, generated-file comparisons, 3718 Lean jobs,
  7090 audited declarations and 7059 environment-resolved public theorem names,
  660 strict assertions individually rejected and 30 PTX fixtures assembled.
  The 47 new public proofs all have exact dependency-audit entries. Existing
  control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
  All four new files pass explicit whitespace/proof-escape checks; the repository
  diff whitespace check also passes.
- Assembly evidence refreshed at 2026-11-06 18:41:10 UTC with thirty current
  fixture hashes. GPU evidence remains 2026-11-05 07:46:53 UTC with fifteen
  current hashes; no GPU execution was added this turn.
- Goal ledger snapshot at 2026-11-06 18:41:28 UTC: 14,422,965 tokens versus
  the preceding published 14,322,437, a difference of 100,528. This is interim
  tool accounting, not final billed usage or a completion report. The original
  goal remains active. Next: one combined ordinary/resource plus eight-buffer
  async allocation/layout/launch certificate, then the coupled Iris byte
  ownership/WP connection and remaining acceptance audits.

### One combined ten-region source/control/protocol client

- Previous-turn classification: progress, verified by the ordinary/resource
  source-use implementation and successful full gate. This turn preserves
  the full original goal and combines the two previously separate clients.
- Optimization instance and previous limitation: the async client used logical
  buffers 0..7, while the conservative output/barrier client used its own
  buffers 0..1 and ticket sequence. Their separate correctness theorems did
  not give one simultaneous layout, one queue or one final ownership return.
  Simply treating both certificates as a single allocation would collide
  buffer/ticket identities and leave joint separation/provenance unchecked.
- Layout and work mapping: `HopperDoubleBufferWholePlan` appends output and
  mbarrier storage as buffers 8 and 9, proves all ten modeled regions separated,
  and preserves every old async region and mapped work ticket. It appends two
  kernel-root tickets after the six-per-tile async sequence and records one
  final event at sequence 6*tiles+2. Existing TMA/native observed-completion
  guards are retained; the two roots require the full actual source prefix.
- Public loan provenance: `WholeLoans` derives every descriptor/input/shared,
  output and resource reservation from actual successful public submission
  and the reachable-state queue invariant. Callers supply no initial Borrowed
  premise. Arbitrary finite protocol tile counts and ten arbitrary initial
  scalar values have checked preparation and positive indexed work tickets.
- Joint coverage and guards: `WholeCoverage` unifies async and ordinary/resource
  uses with exact modes and actual controls. It proves joint coverage for the
  bounded positive-K source family and rejects host reclaim/write whenever
  a covered use is still pending in any finite coupled execution. The same
  public queue supplies the loans and completion faithfulness for both cases.
- Exhaustive inventory: `WholeInventory` reconstructs joint uses from every
  actual Unified readByte/writeByte lookup and preserves its memory-control
  endpoint. Descriptor offsets follow from actual encoded-byte bounds;
  per-byte TMA and native operand identities come from real lookups. Non-bulk
  copies are ruled out by the actual source theorem rather than excluded by
  a coverage scope. Actual resource records cover every byte in their storage
  span, including transfer notifications. Direct pending actual-access guards
  require no guessed role, binding or permission certificate from the caller.
- Complete execution and reuse: `WholeExecution` constructs actual preparation,
  complete FIFO execution and final acquire with empty loans, live buffers,
  exact clocks and subsequent write/reclaim for any region. On the bounded
  positive-K source family this lifts to one complete actual-prefix/protocol
  execution. The original minimal two-buffer zero-K source client remains
  available; the generic ten-buffer zero-work protocol fact does not impose
  unused descriptor/input allocation premises on that source-zero theorem.
- Tests: twenty-one facts include generic public preparation/return/reuse,
  symbolic 90-tile return, a concrete four-tile 26-command/34-loan execution,
  exact root tickets 25/26, data-family complete source coupling and actual
  byte/resource inventory coverage. Negative cases cover a missing final root
  device step, freeing output after only async work, early-event acquisition
  retaining both completed root loans and preventing barrier reclamation, and
  aliased output/barrier layouts. Opaque roots leave abstract output/resource
  values unchanged; they do not fabricate real tensor or mbarrier byte effects.
- Research and remaining boundaries: this is checked composition/reuse of the
  existing lifetime protocol, an engineering baseline rather than a claimed
  new permission method or optimization speedup. The certificate concerns a
  separated modeled layout and source/control/protocol execution. Physical
  allocation/launch/command and byte-value refinement, dynamic layouts and
  generations, active byte ownership and coupled Iris/WP remain open. Iris's
  current scalar-buffer heap cannot be relabeled as actual GPU byte ownership;
  ordered overlapping queued reservations still need a separate active-access
  permission interpretation. Full case/instruction audits and Hopper hardware
  evidence remain. All seven required cases stay partial, exact paper 81-form
  parity stays unconfirmed and the original goal remains active.
- Validation: `/tmp/ptx-whole-plan-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six rejection-harness tests, generated-file comparisons, 3724 Lean jobs,
  7143 audited declarations and 7112 environment-resolved public theorem names,
  660 strict assertions individually rejected and 30 PTX fixtures assembled.
  All 53 new public proofs (32 rules and 21 facts) have exact dependency-audit
  entries. All six new files pass proof-escape/trailing-whitespace checks.
  Existing control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 18:52:43 UTC with thirty current
  fixture hashes. GPU evidence remains 2026-11-05 07:46:53 UTC with fifteen
  current hashes; no new GPU execution or performance measurement was added.
- Goal ledger snapshot at 2026-11-06 18:53:12 UTC: 14,471,750 tokens versus
  the preceding published 14,422,965, a difference of 48,785. This is interim
  tool accounting, not final billed usage or a completion report. The original
  goal remains active. Next: an actual-access permission interpretation distinct
  from queued lifetime reservations, followed by the coupled Iris byte-region
  ownership/WP connection and remaining case/instruction acceptance audits.

### Active byte authority and native Iris claim WP

- Previous-turn classification: progress, verified by the unified ten-region
  source/control/protocol client and successful full gate. This turn starts
  the next required permission connection rather than reclassifying queued
  runtime loans as active GPU permissions.
- Optimization instance and missing capability: same-stream read/write lifetime
  reservations can overlap in the queue. Existing Iris buffer snapshots own
  abstract scalar values/loan metadata and do not identify individual GPU
  bytes. Attaching a pure source-use proposition to those snapshots would not
  enforce active per-byte authority or prevent bypassing an access footprint.
- Generic model: `ByteAuthority` keys actual global/shared locations injectively
  by address space, CTA coordinates and byte address, using checked Nat pairing
  and a separate control key. Keys do not distinguish proxies: aliases of the
  same actual location share authority. A claim checks an actual source use,
  actual-node presence, freshness and every control predecessor at the current
  cut, and requires that byte's authority to be available. Retirement requires
  all actual ordinary/async/resource byte uses of its control node to be held;
  it performs the original source advance and returns the matching authority.
  The protocol arm must preserve the cut, so it cannot bypass that requirement.
- Preservation and runtime connection: every finite authority execution projects
  to existing coupled source/control/protocol steps. Claims stay actual, ready
  and pending, including through retirement of other nodes and host/device
  actions. Starting from an available authority pool, a held actual byte in
  a covered region invokes the ten-region public runtime guard and prevents
  host writes/reclamation. Runtime loans are still derived from real public
  preparation; they are not an assumed initial certificate. The joint source
  use type is now generic `Progress.UnifiedUse` in the Hopper layer, with the
  GEMM case exposing a compatible abbreviation rather than defining the core.
- Native Iris interpretation: `Iris.ByteAuthority` uses GenHeap state authority
  and independently owned location fragments for permission metadata. Its
  claim WP consumes the source/control fragment and one actual byte's full
  available authority, checks the real claim interpreter, and returns that
  byte as held while other fragments can be framed. The control/byte lookups
  come from GenHeap validity. Full authority cannot be duplicated; fractional
  splitting concerns the same authority cell and does not grant multiple full
  writes. The first baseline takes exclusive authority even for reads.
- Closed claim adequacy: a concrete GF and native GenHeap initialization allocate
  fragments for the actual supplied authority map. One-step claim adequacy
  proves an ok result from actual source readiness/use and an available map
  entry; it exports no arbitrary GS or unproved heap-realization premise.
  This is stronger than mere NotStuck of a language that returns errors as
  values. It is still only a claim-operation adequacy theorem, not a complete
  kernel/retirement execution theorem.
- Tests: twenty facts use actual zero-K mbarrier bytes and source-matched
  resource/control ranks to construct reachable, ready cuts. They check actual
  claims and native Iris WP/closed adequacy, reject duplicate claims, absent
  authority, wrong resource modes and claims after source completion, distinguish
  identical addresses across spaces/CTAs/control keys, and show that claiming
  only one barrier byte does not permit retirement. Retirement's projection
  and byte return are checked separately; a cut-preserving source shortcut is
  impossible. Native Iris full-authority duplication and fractional splitting
  facts are also checked.
- Boundaries and reuse: these are access-authority cells containing available/
  held ownership metadata, not GPU byte values or physical allocations. Actual
  source/weak-memory value proofs remain separate. Generic authority invariants
  apply to ordinary, TMA/native and resource uses; the public host-protection
  adapter currently instantiates the ten-region Hopper source family. This is
  an engineering permission baseline, not a new research-method or speedup
  claim. Complete source-footprint authority-pool construction, multibyte
  retirement/return WP and whole-kernel Iris execution/adequacy remain open.
  Physical allocation/runtime/command and byte-value refinement, dynamic
  layouts/generations and remaining case/instruction audits are also open.
  All seven required cases remain partial and exact paper 81-form parity stays
  unconfirmed. No new GPU execution, performance or IEEE/logits/token result is
  added. The original unbounded goal remains active.
- Additional open mode obligation: `AllHeld` currently requires exact held-mode
  matching. RMW can request both modes for one byte/control, so the next step
  must add explicit write-implies-read authorization (without weakening the
  source inventory's exact modes). Do not claim complete RMW authority execution
  from the current generic invariant or one-step claim theorem. Finite complete
  footprint construction and local multibyte retirement WP should follow.
- Validation: the first full gate reported two missing audit entries for the
  new attributed simp theorems `store_byte` and `store_control`; both exact
  entries were added without changing the auditor. The rerun of
  `/tmp/ptx-byte-authority-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six rejection-harness tests, generated-file comparisons, 3728 Lean jobs,
  7195 audited declarations and 7164 environment-resolved public theorem names,
  660 strict assertions individually rejected and 30 PTX fixtures assembled.
  All 52 new public proofs (32 rules and 20 facts) have exact audit entries.
  New files pass proof-escape/whitespace checks and no heartbeat limit was
  increased. Existing control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 19:17:47 UTC with thirty current
  fixture hashes. GPU evidence remains 2026-11-05 07:46:53 UTC with fifteen
  current hashes. No new GPU execution or performance measurement was added.
- Goal ledger snapshot at 2026-11-06 19:19:19 UTC: 14,557,978 tokens versus
  the preceding published 14,471,750, a difference of 86,228. This is interim
  tool accounting, not final billed usage or a completion report. The original
  goal remains active. Next: RMW authorization, complete footprint acquisition/
  retirement/return WP, then whole-source Iris execution/adequacy, runtime/value
  correspondence and the remaining case/instruction acceptance audits.

### RMW authorization and native finite-footprint retirement

- Previous-turn classification: progress, verified by active-byte authority,
  native local claim WP and closed single-claim adequacy. The original goal
  remains active; this turn closes the exact-mode RMW obstruction and adds
  actual finite-footprint retirement rather than treating old one-step claim
  adequacy as a whole-kernel theorem.
- Optimization instance and previous limitation: an RMW reads and writes the
  same byte at one source node. Exact held/requested-mode matching could not
  discharge both demands with one authority cell. Separately, global retirement
  cleared every matching owner, so a local Iris update needed a complete finite
  footprint and proof that no unowned cell outside it would change.
- Authorization: write authority now satisfies read and write demands, while
  read authority cannot satisfy a write. `Uses`, claim source checks and joint
  runtime-region coverage retain their exact modes. `AllHeld` requires an
  actual held grant authorizing each actual demand; it does not manufacture
  two full permissions or weaken the source RMW semantics.
- Finite footprints: `ByteFootprint` checks source-sound grants, complete demand
  coverage, distinct location keys, actual held cells and a frame certificate.
  The clear-list interpretation is proved equal to the existing source-node
  retirement map. Raw held keys have source-location support; support and active
  claims are preserved through all finite permission steps. Consequently a
  complete source footprint derives its frame certificate from execution out
  of an available pool instead of assuming an unexplained frame update.
- Source classification and replay: `ByteSourceFootprints` exhaustively
  reconstructs ordinary and opaque resource uses at an actual source event.
  The existing source/control projection remains checked. A successful finite
  footprint finish is a real authority retirement step and hence an actual
  source/control advance; incomplete footprints cannot bypass it.
- Native Iris WP: `Iris.ByteRetirement` updates the listed full GenHeap byte
  fragments and the exclusive controller snapshot, returning available byte
  fragments and the advanced controller. Other byte fragments frame the rule.
  The controller now records the full authority state so native GenHeap
  validity proves the exact current metadata; metadata knowledge does not own
  other byte fragments. Existing local claim WP/closed claim adequacy were
  adapted to update both controller and byte metadata in the same atomic step.
- Closed retirement adequacy initializes the actual supplied authority map
  through native GenHeap. Distinct-list extraction obtains the real controller
  and held byte fragments; the postcondition proves an ok retired result,
  stronger than merely NotStuck in an error-valued language. A wrapper derives
  the frame premise from a finite authority execution starting with available
  cells. No OwnP substitution, assumed realization map or new semantic axiom
  is used for local byte updates.
- Tests: twenty-six facts include a genuine two-instruction RMW run through the
  existing Hopper/WGMMA interpreter and its completed source trace, actual
  read/write event bytes, a complete four-byte write footprint serving both
  demands, rejection of read-only RMW authority, and exact ordinary byte bounds.
  Actual zero-K mbarrier source identities give sound, complete, distinct
  eight-byte footprints, successful retirement and all-byte authority return.
  A seven-byte footprint missing the last byte is rejected. Native local WP
  and closed retirement adequacy cover both barrier slots.
- Remaining and research boundary: these are access-authority metadata proofs,
  not GPU memory-value updates or CUDA allocation/runtime refinement. The source
  projection is one-way; lifting an entire source execution into this authority
  protocol is not yet established. The concrete retirement adequacy theorem
  starts from held authority; complete acquisition scripts from an initially
  available pool and their composition with retirement remain open. Whole-
  kernel Iris execution/adequacy, source value/runtime correspondence, dynamic
  layouts/generations, remaining case/instruction audits and Hopper hardware
  evidence also remain. This is an engineering permission baseline with reuse
  across RMW and resource storage, not a new-method/speedup claim. All seven
  required cases stay partial and exact paper 81-form parity stays unconfirmed.
  No new GPU execution, performance or IEEE/logits/token result is added.
- No race-freedom or GPU byte-value conclusion follows merely from serializing
  authority claims. Existing memory/RF/coherence/race conditions remain separate;
  source lifting and a complete Iris/kernel refinement are still required.
- Validation: `/tmp/ptx-byte-retirement-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six rejection-harness tests, generated-file comparisons, 3732 Lean jobs,
  7249 audited declarations and 7218 environment-resolved public theorem names,
  660 strict assertions individually rejected and 30 PTX fixtures assembled.
  All 54 new public proofs (28 rules and 26 facts) have exact dependency-audit
  entries. Earlier active-byte/claim WP tests also pass with the updated RMW
  authorization and controller snapshot. No heartbeat limit was increased.
  New files pass proof-escape/trailing-whitespace checks; the repository diff
  whitespace check passes. Existing control tests retain SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 19:42:02 UTC with thirty current
  fixture hashes. GPU evidence remains 2026-11-05 07:46:53 UTC with fifteen
  current hashes; no new GPU execution or performance measurement was added.
- Goal ledger snapshot at 2026-11-06 19:43:41 UTC: 14,637,840 tokens versus
  the preceding published 14,557,978, a difference of 79,862. This is interim
  tool accounting, not final billed usage or a completion report. The original
  goal remains active. Next: complete actual-footprint acquisition scripts from
  available authority, compose them with native retirement, lift whole source
  execution, then finish Iris/value/runtime and case/instruction audits.

### Available-byte acquisition composed with native retirement (2026-11-06)

- Optimization instance: the existing Hopper asynchronous pipeline needs actual
  source-byte access authority to be acquired before use and returned before
  storage reuse. This turn also reuses the rules on an unsplit ordinary atomic
  RMW, whose read/write demands share one write grant per byte.
- Previous concrete gap: the local native retirement theorem started from held
  fragments. It did not construct a complete sequence of checked claims from
  initially available byte authority, nor compose that sequence with retirement
  in one native script WP/closed adequacy theorem.
- Mechanism: `Hopper.ByteAcquisition` builds finite pools keyed by actual
  locations, executes every claim, proves initial availability and distinctness
  are necessary for success, and preserves the coupled source cut until finish.
  Sound/complete footprints and supported/active invariants derive the required
  retirement frame. The complete cycle restores the initial byte-authority map
  and projects to real permission/source steps. Generic rules permit unrelated
  active claims; global availability is only a convenient initialization case.
- Native connection: `Iris.ByteAcquisition` proves the real script one physical
  claim at a time using native GenHeap updates and continuation composition.
  It then invokes the checked source retirement, returns the listed fragments
  and preserves arbitrary Iris frames. Closed adequacy initializes a real
  GenHeap over the supplied initial map; it does not assume pre-held fragments
  or substitute a whole-script OwnP relation. No new semantic axiom is added.
- Reuse/tests: 27 facts cover both actual mbarrier slots and an actual completed
  source RMW. Eight- and four-byte available pools yield nine- and five-action
  scripts (claims plus retirement, not GPU instruction counts). Tests cover
  missing final-byte and duplicate request rejection, unchanged source cut
  during claims, source advancement at finish, exact pool restoration, an
  unrelated byte fragment, and native WP/closed adequacy. All 60 new public
  proofs (33 rules, 27 facts) are registered in the exact dependency audit.
- Remaining: these are per-source-node access-authority metadata results. The
  actual source-ready, sound/complete/distinct footprint and availability
  premises are explicit. Whole-source lifting, GPU byte-value correspondence,
  whole-kernel Iris adequacy, physical allocation/runtime, compiler refinement,
  and remaining case/instruction audits stay open. Authority serialization
  alone does not establish GPU race freedom. Existing RF/coherence/race rules
  remain separate. All seven required cases stay partial; exact paper 81-form
  parity remains unconfirmed. No new GPU, IEEE/logits/token, performance or
  method-novelty result is claimed.
- Validation: `/tmp/ptx-byte-acquisition-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six rejection-harness tests, generated-file comparisons, 3735 Lean jobs,
  7309 audited declarations and 7278 environment-resolved public theorem names,
  660 strict assertions individually rejected, and 30 PTX fixtures assembled.
  The 27 new facts and all generic rules pass at the existing limits. New
  files contain no proof escapes or trailing whitespace; repository diff
  whitespace checking passes. The earlier control test retains SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 20:18:09 UTC with thirty current
  hashes. GPU evidence remains 2026-11-05 07:46:53 UTC with fifteen current
  hashes and 25 finite cases; no new GPU execution was performed.
- Goal ledger snapshot at 2026-11-06 20:18:33 UTC: 14,796,731 tokens versus
  the preceding published 14,637,840, a difference of 158,891. This is interim
  tool accounting, not final billed usage or a completion report. The original
  goal remains active. Next: construct source-node footprints across a whole
  execution, lift that execution into the checked authority protocol, then
  complete kernel/value/runtime and case/instruction audits.

### Whole finite source authority execution and native source scripts (2026-11-06)

- Previous goal turn: progress, verified by the available-pool acquisition and
  retirement implementation and terminal full-gate success. It left whole-source
  lifting and native inter-node heap-resource composition open.
- Optimization instance: the existing bounded positive-K Hopper double-buffer
  pipeline reuses physical storage across TMA/native/source operations, then
  drains its prepared public queue and acquires the final event before reuse.
- Previous specific limitation: the per-node cycle required a supplied complete
  footprint. It did not derive all footprints for a whole source, reconstruct
  subsequent availability, or retain the entire native heap between nodes.
- Mechanism: `Hopper.ByteInventory` normalizes a finite location catalog, selects
  only actual source uses and lets write grants discharge both RMW demands.
  Selected footprints are sound, complete under actual-use inventory bounds,
  and distinct even with duplicate catalog entries. Unused locations produce no
  requests. These are noncomputable proof-level selectors, not a CLI extractor.
- `Hopper.ByteExecution` constructs each cycle from one available pool and proves
  it returns that pool. Every finite original source/host/device execution then
  lifts to actual byte-authority steps, with original source cuts and protocol
  transitions retained. The explicit bound is supplied on the actual Hopper
  family by existing exhaustive region coverage; callers do not assume per-node
  availability, initial held claims or arbitrary realization maps. The original
  public completion/loan-return run is reused, with all its completion guards.
- Native mechanism: a GenHeap restoring accessor returns every unselected
  fragment after each cycle. Continuation rules compose the real physical
  claim/finish actions for any ordered source prefix. The source order is
  constructed from its finite reachability proof, has no repeated/already-done
  nodes and gives the exact final cut. Run correctness, arbitrary framed WP and
  closed native adequacy initialize a real heap and retain the entire pool.
  There is no whole-script atomic/OwnP substitute or new semantic axiom.
- Reuse: existing actual RMW and mbarrier fixtures exercise normalized demands
  and omission checks; `HopperDoubleBufferByteExecution` covers the entire
  positive-K source plus host/device completion relation. The companion Iris
  module constructs a complete native source-authority-script witness for the
  existing parameterized data family, with arbitrary finite retry schedules,
  bounded positive tile count, represented inputs and frame memory. It uses
  the original checked source/TMA components. No new kernel-side synchronization
  or waiting is introduced by this logical witness.
- Tests: 26 facts cover read-only selection, write/read merging, duplicate
  catalog normalization, unused bytes, missing RMW/barrier locations, actual
  RMW closed adequacy, all actual Hopper uses/footprints, full coupled lifts and
  projection, final pool return, a one-tile source witness, repeated/done-node
  rejection, exact completion cuts, full-source native witnesses and native
  cross-node reuse while preserving every pool fragment and arbitrary frames.
  All 68 public proofs (42 rules and 26 facts) have exact dependency-audit
  registrations. Existing control/negative tests are retained.
- Remaining/trust boundary: inventory-bounded finite source/control executions
  now have permission lifts and native source-authority adequacy. The public
  host/device drain/acquire is lifted at the authority-relation level; its
  native Iris command composition with GPU memory values remains open. The
  native source script keeps the prepared protocol unchanged. Physical GPU
  allocation/commands, compiler/runtime refinement, dynamic layouts/generations,
  actual byte-value/RF/coherence correspondence and remaining case/instruction
  audits also remain. Serial ghost authority alone does not prove GPU race
  freedom or scheduling fairness. These are reusable engineering baselines,
  not a new-method or speedup claim. All seven required cases stay partial and
  exact paper 81-form parity stays unconfirmed. No new GPU, performance or
  IEEE/logits/token evidence is added.
- Validation: `/tmp/ptx-byte-source-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six rejection-harness tests, generated-file comparisons, 3742 Lean jobs,
  7377 audited declarations and 7346 environment-resolved public theorem names,
  660 strict assertions individually rejected, and 30 PTX fixtures assembled.
  All 68 new public proofs, including the 26 facts, compile with the existing
  limits. Exact audit registration, proof-escape and whitespace checks pass.
  No heartbeat or recursion limit was raised for these proofs. The existing
  control test still has SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 20:39:22 UTC with thirty current
  hashes. GPU evidence remains 2026-11-05 07:46:53 UTC with fifteen current
  hashes and 25 finite cases; no new GPU execution was performed.
- Goal ledger snapshot at 2026-11-06 20:39:41 UTC: 14,922,304 tokens versus
  the preceding published 14,796,731, a difference of 125,573. This is interim
  tool accounting, not final billed usage or a completion report. The original
  goal remains active. Next: compose native host/device commands with the
  source-authority script, connect byte-value/RF/coherence semantics and runtime,
  and finish the original case/instruction/compilation audits.

### Native source/device/acquire composition with fixed plan (2026-11-06)

- Previous goal turn: progress, verified by complete finite-source authority
  lifting, native source-script adequacy and terminal full-gate success.
- Optimization instance: the bounded positive-K Hopper double-buffer client
  completes actual TMA/native/source work, drains its existing prepared FIFO,
  then acquires the final event before releasing loans or reusing storage.
- Previous specific gap: native source scripts stopped with the prepared
  protocol unchanged. Subsequent host/device completion and acquire existed
  only in the separate coupled/authority relation, not in that native script.
- Mechanism: `Hopper.ByteProtocol` executes real original host/device commands.
  Device advancement requires its next ticket's mapped work to be completed
  in the actual source cut, while preserving the original FIFO/dependency
  checks. The check is per ticket, not a new all-work synchronization rule.
  Original protocol errors are retained as `protocolFailure`; absent source
  completion has the distinct `incompleteWork` error. The full plan and cluster
  scope are fixed in the execution context, so actions cannot replace the
  plan per command. Earlier claim/finish behavior remains unchanged.
  The completion guard is a noncomputable Lean semantic predicate; it is not
  runtime instrumentation.
- Native connection: `Iris.ByteProtocol` updates the real GenHeap controller
  cell and frames every byte-authority cell and arbitrary additional resources.
  Actual command scripts have run correspondence, continuation composition,
  framed WP and closed adequacy. The combined source/device/acquire script has
  the same results, retains the complete available pool and projects every
  successful native prefix to the original coupled source/protocol execution.
  Rejected actions have an explicit native WP preserving their current
  controller/frame. This does not roll back earlier successful commands.
- Reuse/application: `HopperDoubleBufferByteProtocol` constructs a native whole
  source/drain/acquire witness for the existing bounded positive-K actual data
  family with finite heterogeneous retries and represented inputs/frame memory.
  It uses the original checked region bounds, source components, public return
  run and per-work completion proof. Native active-byte prefixes now imply
  host write/reclaim rejection through the existing checked public preparation,
  loan provenance, region coverage and source completion rules. Initial held
  bytes, whole-script OwnP updates and new semantic axioms are not introduced.
- Tests: 29 facts cover actual public preparation of a one-work fixture backed
  by the real RMW source, FIFO-ready/source-incomplete rejection, successful
  completion/acquire and closed native adequacy, loan retention until acquire,
  precise early acquire/reclaim/write/invalid event/duplicate record/empty
  queue/invalid stream errors, subsequent legal reuse/reclaim, preserved byte
  authority/source cuts, the parameterized full Hopper native pipeline and
  omitted-final-device-step rejection. A two-stream public fixture checks that
  complete source work cannot bypass a queued dependency and that the native
  wait script succeeds after that dependency. Six strict false success claims
  against the new native interpreter are checked with the existing per-command
  JSON diagnostic rules, retaining all 660 earlier assertions. All 60 new public
  proofs (31 rules and 29 facts) have exact audit registrations. Four earlier
  context fixtures were updated for the fixed-plan context fields; no tests
  were removed or weakened.
- Remaining/trust boundary: combined native source/device/acquire adequacy is
  over permission/protocol metadata and starts at the original publicly
  prepared state. Public preparation still has its separately checked actual
  interpreter run; native queue/loan preparation is not yet part of this
  combined script. Native physical byte contents/RF/coherence, allocation and
  command/runtime/compiler refinement, dynamic layouts/generations and the
  remaining case/instruction audits stay open. Protocol scalar buffer values
  are not physical GPU byte values. This is an engineering baseline with
  reusable rules; no hardware scheduling, fairness, speedup or method-novelty
  claim is added. All seven required cases stay partial and exact paper 81-form
  parity stays unconfirmed. No new GPU, performance or IEEE/logits/token
  evidence is added.
- Validation: `/tmp/ptx-byte-protocol-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six rejection-harness tests, generated-file comparisons, 3746 Lean jobs,
  7437 audited declarations and 7406 environment-resolved public theorem names,
  666 strict assertions individually rejected and 30 PTX fixtures assembled.
  The six new strict assertions also passed an isolated diagnostic check.
  All 60 new public proofs, including 29 facts, compile with existing limits.
  Exact dependency registration, proof-escape and whitespace checks pass; no
  heartbeat or recursion limit was raised for the new proofs. The existing
  control test retains SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 21:00:37 UTC with thirty current
  hashes. GPU evidence remains 2026-11-05 07:46:53 UTC with fifteen current
  hashes and 25 finite cases; no new GPU execution was performed.
- Goal ledger snapshot at 2026-11-06 21:01:28 UTC: 14,998,970 tokens versus
  the preceding published 14,922,304, a difference of 76,666. This is interim
  tool accounting, not final billed usage or a completion report. The original
  goal remains active. Next: connect physical byte-value/RF/coherence semantics
  with the existing kernel specifications and native resources; native public
  preparation, runtime/compilation and original case/instruction audits remain.

### Actual event-local byte values with native GenHeap (2026-11-06)

- Previous goal turn: progress, verified by native source/device/acquire
  composition, real source-completion/error guards and terminal full-gate
  success. Its byte-owner cells contained permission metadata only.
- Optimization instance: safe storage reuse in actual kernels needs the value
  written/read by a source operation as well as its access/lifetime permission.
  The minimal actual RMW source isolates that gap before async value/proxy
  correspondence is attempted. This remains an engineering baseline.
- Previous limitation: claim/finish rules could establish ownership and source
  completion without holding a representation of actual modeled byte contents.
  They did not show that an RMW read the initialized word or wrote its emitted
  result into native byte cells.
- Mechanism: `Hopper.ByteContents` stores owner and optional `Symbolic.Byte` at
  each actual key. Claims update owner while preserving content. Completion
  checks source-linked reads/writes, complete coverage of memory events sharing
  its control identity, the original sound/distinct/complete permission list,
  and every emitted read against the current local value view. It then applies
  actual emitted writes and returns authority in one modeled event transition.
  Erasure of successful value actions/scripts projects to the original checked
  byte-authority relation. No desired postcondition is used as a write payload.
- RF/coherence boundary: a reusable rule derives read checks from admitted
  causal-memory agreement, race-derived eligibility and an explicit realization
  of selected RF source values in the local view. Such realization is not
  generally implied by a source/control order. Arbitrary weak-memory candidates
  are not assumed to have one global SC heap history. For the actual single-RMW
  instance, read-event equality with its existing scalar source and its already
  proved memory-consistency/race-freedom facts establish the initial read values;
  the initialized actual-location pool realizes those values. No new causal,
  coherence, RF or input-oracle axiom is supplied.
- Native connection: `Iris.ByteContents` uses real GenHeap cells containing both
  owner and contents, with a closed concrete GF and actual heap initialization.
  Cell agreement/validity and exclusive ownership cover those actual payloads.
  A claim's local update consumes its actual cell plus controller and frames
  others. General event/script updates currently require the full interpreted
  heap fragments, using native same-domain updates per physical action. The
  source RMW's four claims and final atomic memory-event update remain separate
  physical language steps; there is no whole-script OwnP/atomic substitute.
  Every completed event checks all reads before any of its writes. External
  Iris frames are preserved, and ordinary source events have a reusable proof
  that the selected memory event omits no access sharing its control node.
- Tests/reuse: 36 facts cover actual read/write agreement with the existing
  source, admission-derived read values, initialized pool membership, each real
  claim, unchanged claimed values, complete ownership, successful RMW finish,
  real script run and closed native adequacy. Final bytes/returned counter
  fragments match the actual event and completed observer. Wrong and absent
  old data retain identical permissions yet are rejected with `readMismatch`;
  incomplete atomic footprints and repeated completion are rejected, and an
  unrelated byte retains its value. Projection and arbitrary-frame native WP
  are checked. Two strict finite-value assertions ('counter stayed zero' and
  'counter stayed uninitialized') are individually refuted with the original
  strict diagnostic criteria. All 83 new public proofs (47 rules, 36 facts)
  have exact audit entries; existing tests and rejection assertions are kept.
- Remaining: this is an event-local modeled-value bridge and a concrete RMW
  witness, not an all-candidate native-value proof for atomic dispatch or the
  entire Hopper pipeline. Footprint-local value completion (without full-map
  ownership), RF/proxy-view realization across general weak/async executions,
  native protocol/value composition, public preparation, real allocation,
  compilation/runtime and the original case/instruction audits remain. The
  existing source/device/acquire Iris pipeline still has metadata-only byte
  cells. Symbolic real fragments are not IEEE bytes; no physical GPU/IEEE or
  logits/token/performance result is added. All seven required cases remain
  partial and exact paper 81-form parity stays unconfirmed. No method-novelty
  or speedup claim is made.
- Validation: `/tmp/ptx-byte-contents-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six rejection-harness tests, generated-file comparisons, 3749 Lean jobs,
  7520 audited declarations and 7489 environment-resolved public theorem names,
  668 strict assertions individually rejected, and 30 PTX fixtures assembled.
  The two new strict assertions also pass the isolated diagnostic check.
  All 83 new public proofs, including the 36 facts, compile with existing
  limits. Exact audit registration, proof-escape and whitespace checks pass.
  No heartbeat/recursion limit was raised for these proofs. The existing
  control test retains SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 21:35:32 UTC with thirty current
  hashes. GPU evidence remains 2026-11-05 07:46:53 UTC with fifteen current
  hashes and 25 finite cases; no new GPU execution was performed.
- Goal ledger snapshot at 2026-11-06 21:36:55 UTC: 15,122,585 tokens versus
  the preceding published 14,998,970, a difference of 123,615. This is interim
  tool accounting, not final billed usage or a completion report. The original
  goal remains active. Next: prove footprint-local value completion and
  RF/proxy-view realization for further actual source phases, compose value
  cells with native protocol execution, then continue the original
  preparation/runtime/compilation and case/instruction audits.

### Footprint-local byte-value completion and fractional frames (2026-11-06)

- Previous goal turn: progress, verified by the event-local value/permission
  state, actual RMW value witness, native full-map script adequacy and terminal
  full-gate success. Its event completion still consumed all interpreted heap
  fragments, preventing an independent client from retaining a disjoint
  physical byte fragment across the value update.
- Optimization instance: storage reuse and independent buffer clients need to
  update only the byte cells they own, while other clients retain ownership of
  unrelated contents. The actual RMW remains the minimal source instance; this
  turn extends its native proof with an actual disjoint fractional byte frame.
- Mechanism: `Iris.ByteContentsFootprint` defines complete payload lists, a
  source-derived returned-value function and per-cell native GenHeap updates.
  A checked store equation equates those listed updates plus the controller
  change with the original successful value event. Local completion WP/CPS
  consumes only the held listed fragments and controller, retaining arbitrary
  frames. It checks the same source/read/value/permission/coverage/distinctness
  predicates via the unchanged interpreter success premise. No full-map ownership
  premise, whole-map update or assumed realization map replaces this rule.
- Real acquisition/cycle: generic continuations execute each source-sound claim
  from available payloads, preserving the source cut and prior contents, then
  compose with local value completion. Distinct physical keys separate the
  resources; the actual RMW uses one write grant per byte for both read and
  write demands. Closed cycle adequacy allocates a real heap and extracts just
  the needed cell fragments, rather than assuming initially held permissions.
  The full-map baseline remains available but is not used by these local
  completion/cycle rules.
- Derived frame compatibility: `Hopper.ByteContentsFrames` adds an available
  byte outside the actual complete footprint and proves every original event
  check still succeeds. Actual read-use linkage plus coverage prove it cannot
  alter an emitted read; held/frame conditions are reconstructed for the
  extended state. No 'the extra byte is harmless' premise is assumed. Granting
  commutes with that extra cell and the final contents retain its payload.
- Tests/reuse: 20 facts use the actual RMW and its admitted data witness for
  local finish, complete available-pool cycle, native WP and closed adequacy.
  A real extra cell at global address 4096 contains 99. The framed client's
  contract retains only half of that cell's full fragment while the four RMW
  bytes are claimed, updated and returned. Joint extraction and splitting from
  actual heap initialization, followed by closed adequacy using that fractional
  frame, show the precondition is realizable. The final counter is one and the
  spare remains 99. Invalid old data and incomplete atomic footprints still
  have no successful completion. Two strict finite assertions refute 'framed
  counter stays zero' and 'spare is clobbered', preserving all 668 previous
  strict assertions and their diagnostic requirements. All 46 new public proofs
  (26 rules, 20 facts) have exact audit registrations.
- Remaining/trust boundary: this removes full-map ownership from the new local
  event/cycle interfaces. RF/proxy-view realization across arbitrary weak/async
  source executions and whole-source value/native protocol composition are
  still open. The earlier metadata pipeline is unchanged. Native preparation,
  physical GPU allocation/commands, compilation/runtime, general case coverage
  and the exact paper instruction inventory remain. These are engineering
  compositionality baselines using standard native Iris updates and framing;
  no new-method, scheduling-fairness or speedup claim is added. All seven
  required cases remain partial and exact paper 81-form parity is unconfirmed.
  No new GPU, performance or IEEE/logits/token evidence is added.
- Validation: `/tmp/ptx-local-value-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six rejection-harness tests, generated-file comparisons, 3752 Lean jobs,
  7566 audited declarations and 7535 environment-resolved public theorem names,
  670 strict assertions individually rejected, and 30 PTX fixtures assembled.
  The two new strict assertions also pass an isolated diagnostic check.
  All 46 new public proofs, including the 20 facts, compile with existing
  limits. Exact audit entries, proof-escape and whitespace checks pass; no
  heartbeat or recursion limit was raised for the new proofs. The original
  control test retains SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 21:54:53 UTC with thirty current
  hashes. GPU evidence remains 2026-11-05 07:46:53 UTC with fifteen current
  hashes and 25 finite cases; no new GPU execution was performed.
- Goal ledger snapshot at 2026-11-06 21:55:34 UTC: 15,178,632 tokens versus
  the preceding published 15,122,585, a difference of 56,047. This is interim
  tool accounting, not final billed usage or a completion report. The original
  goal remains active. Next: establish RF/proxy-view realization across further
  actual source phases and compose these local value rules with the native
  protocol pipeline, then continue the original preparation/runtime/compiler
  and case/instruction audits.


## Research record: byte values across checked source phases

- Optimization instance: preserving the actual producer's byte value until a
  consumer reads it while a double-buffer arena is reused. The existing local
  Iris value rules checked one event/cycle; their connection to a later RF view
  was still missing.
- Mechanism: `Hopper.ByteContentsPhases` derives writes from successful checked
  completion and actual emitted write bytes. Claims and events that do not
  write a location preserve its contents. `Iris.ByteContentsPhases` proves
  completion monotonicity and valid source cuts across actual successful
  scripts. A per-byte writer partition, closed cuts and completion freshness
  exclude earlier/repeated/future writers between producer completion and a
  pending reader. The resulting view equals the admitted selected writer's
  value. No arbitrary weak execution is replaced by a global SC heap.
- Reuse/application: `Kernels.HopperDoubleBufferByteContents` obtains the phase
  premise from the existing parameterized double-buffer writer classification
  and byte-order-to-control-path theorem, deriving absence of nonbulk copies
  from the checked actual source. Its reader-view theorem uses the existing
  arbitrary-admitted-RF and actual operand-byte theorems rather than assuming
  the desired data. It requires an actual successful script and valid starting
  cut; it does not prove those premises are realizable for Hopper.
- Tests: ten facts use the actual admitted RMW and real-data three-tile Hopper
  family. They cover claim/nonwriter preservation, a real allocated spare,
  actual emitted counter data, source-cut validity/freshness, both arenas and
  reused physical locations. All 24 new public proofs (14 rules and ten facts)
  have exact dependency-audit entries. No heartbeat/recursion limit was raised.
- Concrete remaining limitation: the value action language has claim and
  memory-event finish actions, but no native arrival/control-only action.
  `Unified.memoryControlNode` does not produce arrival nodes; consequently
  these scripts cannot yet construct the full WGMMA operand-ready prefix from
  the empty cut. A checked extension for actual nonmemory controls, nonvacuous
  cross-event value clients, and full native/source/value composition remain.
  Conditional phase preservation does not close those obligations. Native
  preparation, allocation/runtime/compiler correspondence, all seven original
  cases and the exact instruction inventory also remain. All seven cases stay
  partial and exact paper 81-form parity stays unconfirmed. No new GPU,
  IEEE/logits/token, speedup or research-novelty claim follows.
- Multi-frontend discussion: Rust parsing and serialization are separate and
  generic event/logic infrastructure can be reused, while current candidate,
  control, proxy and Iris context types remain PTX-specific. A TTGIR frontend
  would require typed SSA/regions, tensor-layout/thread-distribution, mask,
  shared-memory and async semantics plus checked correspondence to the shared
  layer. Verifying Triton's supported generated PTX proves a property of that
  PTX; transfer to TTGIR needs a checked compiler correspondence or translation
  validation. This discussion does not add TTGIR to the active goal's scope.
  Primary references checked on this turn:
  https://triton-lang.org/main/dialects/TritonGPUOps.html,
  https://triton-lang.org/main/getting-started/tutorials/gluon/layouts.html,
  https://mlir.llvm.org/docs/LangRef/ and
  https://github.com/triton-lang/triton/blob/main/third_party/nvidia/backend/compiler.py.
- Validation: `/tmp/ptx-byte-phase-full-gate.log` exited zero with `All
  verifier checks passed`: 47 Rust tests, Clippy with warnings denied, six
  rejection-harness tests, generated-file comparisons, 3756 Lean jobs, 7590
  audited declarations and 7559 environment-resolved public theorem names,
  all 670 existing strict assertions individually rejected and 30 PTX fixtures
  assembled. New source whitespace/proof-escape scans and exact audit-entry
  checks pass. No original strict check was removed. The original control test
  retains SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 22:16:03 UTC with thirty current
  source hashes. GPU evidence remains 2026-11-05 07:46:53 UTC; no new GPU
  experiment or performance measurement was performed.
- Goal ledger snapshot at 2026-11-06 22:16:15 UTC: 15,320,177 tokens versus
  the preceding published 15,178,632, a difference of 141,545. This is interim
  tool accounting, not final billed usage or a completion report. The original
  goal remains active. Next: checked actual nonmemory control transitions,
  including native arrivals, and nonvacuous cross-event value clients, then
  full Hopper source/value/protocol composition and the original remaining
  preparation/runtime/compiler and case/instruction obligations.


## Research record: checked native control steps in the byte-value language

- Previous turn classification: progress. The phase-value rules, RMW checks and
  Hopper writer-partition application were added to authoritative sources and
  passed the full gate. The next concrete gap was that value scripts could not
  express native arrival nodes.
- Optimization instance: keeping byte data and permissions while actual native
  arrivals/rendezvous controls advance during double-buffer execution. The
  prior claim/finish-only language could never produce an arrival in its done
  cut, so a WGMMA operand-ready prefix could not be constructed from empty.
- Mechanism: `Hopper.ByteContentsControl` adds `finishControl`. The original
  empty-footprint authority finish checks actual node presence, all control
  predecessors, freshness, absence of all source byte/resource uses, and no
  held fragment belonging to this node. An additional checked `NoMemoryAt`
  guard excludes every actual mapped read/write, including any effect outside
  that source-use relation. The action preserves all cells and values and
  projects to the existing authority retirement relation. Native arrivals
  satisfy no-use/no-memory facts structurally; presence/readiness are not
  invented or assumed. Missing predecessors and repeated completion preserve
  the original unready error.
- Native composition: `Iris.ByteContents` adds the actual physical control
  action to the same script language. Existing script/domain/authority and
  phase-validity/value proofs cover it. `Iris.ByteContentsControl` updates only
  the native GenHeap controller fragment; it has local continuation and WP
  rules retaining arbitrary byte frames. No whole-map update is used by these
  new local rules and no new axiom, scheduling assumption or weakened source
  completion guard is introduced.
- Parameterized source connection: `Kernels.HopperDoubleBufferByteControl`
  constructs actual arrival steps for every lane/native position/tile of the
  bounded positive-K retry family. Starting control cuts have existing reached
  source-prefix witnesses; source-derived ranks and validated histories prove
  readiness. Explicit available payload pools provide realizable local heaps.
- Tests/reuse: eighteen facts instantiate the actual independent-real-data
  three-tile family, both arenas and reuse. Every tile/lane/native position has
  an actual successful arrival script, valid resulting cut and original
  authority projection. The allocated spare byte contains 99; its half Iris
  fragment survives controller-only WP and closed heap initialization/adequacy.
  Negative facts reject real RMW reads and writes, actual opaque mbarrier
  storage use even without a data write, invented native arrivals on an RMW,
  repeated arrivals, the actual fence predecessor missing before an MMA
  arrival, and discarding a held fragment. All 43 new public proofs (25 rules,
  eighteen facts) have exact audit entries; no new recursion/heartbeat limits
  or strict-refutation diagnostic relaxations were added.
- Remaining: the structural inability to represent native arrivals is removed.
  The ranked source-prefix witness still does not construct the preceding
  memory writes as value-script steps. Full value execution from initial
  memory, nonvacuous cross-event read/write clients, and whole native/source/
  value/protocol composition remain. Native preparation, physical allocation/
  CUDA runtime/compiler correspondence and the original case/instruction
  obligations remain. All seven required cases stay partial and exact paper
  81-form parity stays unconfirmed. This is a compositional engineering step,
  without a research-novelty, GPU-execution, speedup or IEEE/logits/token claim.
- Validation: `/tmp/ptx-value-control-full-gate.log` exited zero with `All
  verifier checks passed`: 47 Rust tests, Clippy with warnings denied, six
  rejection-harness tests, generated-file comparisons, 3760 Lean jobs, 7633
  audited declarations and 7602 environment-resolved public theorem names,
  all 670 strict assertions individually rejected and 30 PTX fixtures assembled.
  Source whitespace/proof-escape scans and exact registrations for all 43 new
  proofs pass. No original strict assertion was removed or weakened. The
  original control test retains SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 22:34:06 UTC with thirty current
  source hashes. GPU evidence remains 2026-11-05 07:46:53 UTC; no new GPU
  execution or performance measurement was performed.
- Goal ledger snapshot at 2026-11-06 22:34:44 UTC: 15,414,759 tokens versus
  the preceding published 15,320,177, a difference of 94,582. This is interim
  tool accounting, not final billed usage or a completion report. The original
  goal remains active. Next: construct nonvacuous store-to-load value scripts
  from initial memory and compose source memory/control phases, then full
  Hopper native/value/protocol execution and the original remaining public
  preparation, runtime/compiler and case/instruction obligations.


## Research record: generated store-to-load value execution from the initial pool

- Previous turn classification: progress. Checked native control actions and
  actual arrival clients were added and passed the full gate. The next concrete
  action was a nonvacuous cross-event value script from initial memory.
- Optimization instance: establishing the value passed from an actual producer
  event to a later consumer while byte permissions are returned and reacquired.
  Earlier local RMW and native-arrival witnesses did not construct a complete
  writer-to-reader value script from the initial byte pool. The general phase
  theorem still required the caller to exhibit such a script.
- Actual source: `examples/byte_value_pipeline.ptx` is mechanically translated
  into checked existing integer instruction data, then embedded instruction-
  for-instruction in the existing unified interpreter. The reference binds Ptr
  to model byte address 64. The parameter and independent load reply range over
  Nat with the actual PTX u32 wrapping semantics. Source production, complete
  local execution, one-thread launch coverage, emitted read/write inventory and
  exhaustive four-byte permission footprints/readiness are proved.
- Reusable mechanism: `Hopper.ByteContentsOrdinary` derives ordinary non-return
  event predecessors from actual source lookups and empty resource histories;
  barrier returns are explicitly excluded because they can have CTA edges.
  `Iris.Execution` gains checked append/singleton run laws. Native
  `Iris.ByteContentsSequence` supplies actual acquisition/cycle runs and local
  cycle continuations. Complete returned pools and owner-preservation/frame
  facts let the next event acquire the actual updated bytes. These do not
  consume the earlier whole-map update helper or add SC/weak-memory assumptions.
- Parameterized value proof: `ByteValuePipelineValues/Correct` constructs ten
  physical actions from an available four-byte zero-initialized pool: four
  write claims, actual store completion, four read claims and actual load
  completion. The full stored payload becomes the reader's local view through
  those actual updates. Native local WP composes both cycles with arbitrary
  frames; closed heap adequacy initializes the real supplied map and extracts
  its fragments. Every successful script with any independent reply forces all
  four bytes and therefore the full u32 register value to equal the stored
  parameter. The mismatch proof preserves successful complete permissions and
  derives the original precise `readMismatch` result for both reader and script.
- Phase-rule reuse: actual writer completion and successful read-claim script,
  valid empty source cut, source-derived unique-writer phase partition and
  pending reader instantiate the existing producer-to-reader-view theorem.
  The selected-writer RF view is realized by the actual local state. No
  uninhabited script/readiness hypothesis is used for this helper; this does
  not assert that every admitted weak execution has an SC heap history.
- Tests: sixteen facts cover generated instruction order/length, real completed
  source even with a wrong reply, launch coverage, all ten physical actions,
  word 0x12345678 with all four little-endian bytes, u32 parameter/reply wrapping,
  universal successful register correctness, wrong upper bytes, successful
  permissions followed by value rejection, complete failed script execution,
  incomplete reader footprint rejection, closed native heap adequacy and actual
  selected-writer RF realization. Four strict finite assertions refute erased
  first/last bytes, omitted u32 wrapping and source load/store reordering. All
  83 new public proofs (67 rules/source facts and sixteen tests) have exact
  audit entries. No heartbeat/recursion limit or rejection diagnostic is relaxed.
- Remaining: the helper's explicit value-script/RF view witness closes the
  earlier two-event gap. A separate full `Unified.MemoryConditions` witness is
  not claimed here. Full Hopper source/native/value/protocol composition,
  native preparation, physical allocation/runtime/compiler correspondence,
  all original case/instruction obligations and general weak-view realization
  remain. Its unused load may be eliminated by ptxas, so assembly is not evidence
  of a physical GPU load. All seven required cases stay partial and exact paper
  81-form parity stays unconfirmed. No GPU/performance, IEEE/logits/token or
  research-novelty claim is added.
- Validation: `/tmp/ptx-value-pipeline-full-gate.log` exited zero with `All
  verifier checks passed`: 47 Rust tests, Clippy with warnings denied, six
  rejection-harness tests, all generated-file comparisons, 3768 Lean jobs,
  7716 audited declarations and 7685 environment-resolved public theorem names,
  all 674 strict assertions individually rejected, and 31 PTX fixtures assembled.
  The four new strict assertions also pass an isolated diagnostic check. The
  new helper separately assembles with explicit `-arch=sm_70`. New-source
  whitespace/proof-escape checks and exact audit registrations pass. The
  original control test retains SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 23:03:36 UTC with 31 current
  source hashes. GPU evidence remains 2026-11-05 07:46:53 UTC; no new GPU
  execution or performance measurement was performed.
- Goal ledger snapshot at 2026-11-06 23:04:49 UTC: 15,524,751 tokens versus
  the preceding published 15,414,759, a difference of 109,992. This is interim
  tool accounting, not final billed usage or a completion report. The original
  goal remains active. Next: give the two-event helper a separate full memory-
  conditions witness, then reuse the actual two-cycle/view construction for
  TMA-to-WGMMA phases and full Hopper source/native/value/protocol composition,
  while retaining the original public preparation/runtime/compiler and
  case/instruction obligations.


## Research record: full memory witness and admitted-RF-to-native value execution

- Previous turn classification: progress. The generated store/load source and
  actual ten-action native value script, universal successful-reply correctness
  and strict counterexamples passed the full gate. The next missing component
  was a separate full existing-model memory witness and its native connection.
- Optimization instance: consuming a producer's actual stored bytes while
  permissions are returned/reacquired. Prior value-script success and selected
  RF-view realization did not establish that a full RF/co satisfying all weak
  memory conditions existed, or that arbitrary admitted RF/co supplied those
  native checks.
- Source-derived order: `ByteValuePipelineMemoryOrder` proves exhaustive empty
  resource histories and actual native/control presence. Every actual control
  edge is the store-to-load edge; source-derived control/byte ranks establish
  acyclicity. Actual same-thread equal-sized access footprints derive moral
  strength, race freedom and complete eligibility. No desired eligibility,
  global SC serialization, scheduler order or rank is added to admission.
- Full independent witness: `ByteValuePipelineMemory` constructs causal read
  agreement, initialization/no-stale/no-future, coherence, single-copy atomicity,
  RMW atomicity and SC-per-location in the original `Unified.MemoryConditions`.
  Source/control/communication properties come from actual events. The atomicity
  clauses hold for this ordinary program and do not add atomic instruction
  support. Joint source/TMA/resource/control/memory components exist for every
  represented input parameter. This witness is constructed independently of an
  assumed successful native value run.
- All-admitted-model connection: `ByteValuePipelineMemoryLink` derives the
  unique actual writer RF from admitted causal conditions, proved eligibility
  and actual byte order. The real writer/read-acquisition script supplies that
  RF view, including its native local bytes. Existing `reads_from_agreement`
  then establishes the unchanged read-value check. Full u32 source-register
  correctness, the entire actual value script, native local Iris WP/framing and
  closed GenHeap initialization/adequacy follow for every admitted RF/co and
  independent reply in this source family. Prior native WP/adequacy APIs are
  retained, with reusable variants taking actual successful reader completion.
- Tests/reuse: sixteen facts cover joint complete memory and native witnesses,
  word 0x12345678, wrapping, all-admitted RF source/actual run/register/closed
  adequacy and negative full-memory cases. Initial RF is rejected even when
  writing/reading zero agrees with initial-zero bytes: value agreement alone
  cannot certify RF/co. Reading from the reader itself or a nonexistent writer,
  empty/reflexive coherence, wrong upper word bytes and reverse causality are
  rejected. All 54 new public proofs (38 production facts and sixteen tests)
  have exact audit entries. All existing strict assertions and their diagnostic
  requirements are retained; these new quantified negative checks are Lean
  theorems rather than relabeled strict-decide assertions.
- Remaining: the helper's separate full memory-witness gap is closed in the
  existing model. Full Hopper source/native/value/protocol composition, broader
  arbitrary source-trace canonicalization, native preparation, physical
  allocation/runtime/compiler and original case/instruction obligations remain.
  This is a fixed-pointer one-thread source family, not a general realization
  of arbitrary weak executions as SC heaps or a physical ISA proof. All seven
  original cases stay partial and exact paper 81-form parity stays unconfirmed.
  No GPU, IEEE/logits/token, speedup or research-novelty claim is added.
- Validation: `/tmp/ptx-pipeline-memory-full-gate.log` exited zero with `All
  verifier checks passed`: 47 Rust tests, Clippy with warnings denied, six
  rejection-harness tests, generated-file comparisons, 3772 Lean jobs, 7770
  audited declarations and 7739 environment-resolved public theorem names,
  all 674 strict assertions individually rejected, and 31 PTX fixtures assembled.
  Source whitespace/proof-escape checks and exact registrations for all 54 new
  proofs pass. No original strict assertion or diagnostic requirement changed.
  No heartbeat/recursion limit was raised. The original control test retains
  SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-06 23:22:47 UTC with 31 current
  source hashes. GPU evidence remains 2026-11-05 07:46:53 UTC; no new GPU
  execution or performance measurement was performed.
- Goal ledger snapshot at 2026-11-06 23:23:52 UTC: 15,590,668 tokens versus
  the preceding published 15,524,751, a difference of 65,917. This is interim
  tool accounting, not final billed usage or a completion report. The original
  goal remains active. Next: construct actual TMA-to-WGMMA value-phase scripts
  using the existing admitted Hopper data family and local cycle/view rules,
  then full source/native/value/protocol composition while retaining the
  original preparation/runtime/compiler and case/instruction obligations.


## Research record: complete Hopper source byte-value execution and native matrix cells

- Previous turn classification: progress. The ordinary store/load helper had
  an independent full memory witness and all-admitted RF-to-native connection.
  The remaining Hopper reader-view theorem still required an actual successful
  value script as a premise. Local arrival and cycle witnesses did not construct
  all preceding TMA writes and native reads from initial memory.
- Optimization instance: TMA-to-WGMMA double buffering with both shared arenas,
  buffer reuse, finite heterogeneous retries and independent represented real
  A/B. Permissions and a correct source result alone do not establish that real
  intermediate heap bytes can pass every actual read check during execution.
- Reusable invariant: `Iris.ByteContentsFuture` describes pending readers with
  initial or selected-writer RF. Source-specific frontiers place other writers
  before the selected producer or after the reader, while permitting an RMW's
  own write after its reads. Closed cuts and checked readiness/freshness prove
  preservation under each actual claim, control and completion. Existing causal
  agreement and derived eligibility then supply the unchanged read-value check.
  These extra frontier premises are proved for the source family; they do not
  change PTX memory admission or assert SC realization of arbitrary weak traces.
- Constructed scripts: `ByteContentsNodes/Available/Source` recover the actual
  memory effect at each reached source control, select its complete finite
  actual-use inventory, acquire real available byte cells, check its actual
  reads, apply emitted writes and return the pool. Native arrivals use the
  existing checked control-only action. Nonbulk copies are excluded by an
  explicit source theorem because their two memory ports share one source
  control and need separate treatment. No successful script or desired
  intermediate per-node values are assumed by this construction.
- Hopper application: `HopperDoubleBufferValueFrontier/ValueExecution` prove
  the frontier, eligibility, initial-read invariant and bounded inventory from
  the actual source, admitted data memory witness, TMA publication and existing
  per-byte reuse partition. For arbitrary independent real inputs/frame bytes,
  finite per-lane retries and positive K at most 2^28 tiles, a complete source
  value script exists from the actual initial ten-region pool. All cells return
  available and remain allocated; value erasure projects to the earlier byte
  authority execution, including when the protocol starts publicly prepared.
- Final values: `Iris.ByteContentsWrites` preserves actual unique-writer output
  bytes through every checked action. `HopperDoubleBufferValueOutput` connects
  every final matrix cell to the independent real GEMM specification and gives
  a joint full-source value script, correct matrix and closed native GenHeap
  adequacy witness. Closed whole-source adequacy uses the retained whole-map
  script helper; individual footprint-local cycle rules are reused for the
  actual checked construction, but no new full-source footprint-local WP is
  claimed. Opaque mbarrier storage uses are authority reservations, not physical
  mbarrier data encodings.
- Tests/reuse: twelve facts cover the actual initial read invariant, both
  arenas and reuse, all-read eligibility, complete source execution, closed
  native adequacy, unchanged prepared protocol, projection to prior authority
  and final matrix fragments. A nonzero three-tile instance multiplies 1 by 2
  and yields 96 in every matrix element. A native operand is actually allocated
  and can be prefilled with its correct desired byte, yet claiming it still
  returns `authority.unready` when its actual TMA producer is unfinished. Data
  agreement cannot bypass source synchronization. All 49 new public proofs
  (37 production and twelve test facts) have exact audit registrations. These
  quantified negative proofs do not relabel or replace existing strict tests.
- Remaining: source-prefix byte-value existence and final matrix cells are now
  closed for this bounded positive-K family. The value action language leaves
  the protocol unchanged; public preparation and host/device completion,
  drain/acquire/loan-return are proved separately at the authority level and
  still need full byte-value/native composition. Native public preparation,
  zero-K value scripts, general weak RF/proxy realization, physical allocation,
  command/runtime/compiler correspondence, dynamic layouts/generations and
  original case/instruction/observer audits remain. All seven original cases
  stay partial and exact paper 81-form parity stays unconfirmed. No new Hopper
  GPU, IEEE/logits/token, speedup or research-novelty claim is added.
- Validation: `/tmp/ptx-hopper-values-full-gate.log` exited zero with `All
  verifier checks passed`: 47 Rust tests, Clippy with warnings denied, six
  rejection-harness tests, generated-file comparisons, 3781 Lean jobs, 7819
  audited declarations and 7788 environment-resolved public theorem names,
  all 674 strict assertions individually rejected, and 31 PTX fixtures assembled.
  New-source whitespace/proof-escape checks and exact registrations for all 49
  new proofs pass. No original strict assertion or diagnostic requirement
  changed, and no heartbeat/recursion limit was raised. The original control
  test retains SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-07 00:05:18 UTC with 31 current
  source hashes. GPU evidence remains 2026-11-05 07:46:53 UTC; no new GPU
  execution or performance measurement was performed.
- Goal ledger snapshot at 2026-11-07 00:05:29 UTC: 15,775,915 tokens versus
  the preceding published 15,590,668, a difference of 185,247. This is interim
  tool accounting, not final billed usage or a completion report. The original
  goal remains active. Next: compose the complete actual source byte-value
  execution with the checked prepared host/device completion, drain/acquire
  and loan-return relation, while retaining the native public preparation,
  runtime/compiler and original case/instruction obligations.


## Research record: one Hopper source/value/device/acquire execution

- Previous turn classification: progress. Complete bounded positive-K source
  value scripts and correct final native matrix cells were constructed. Those
  actions preserved the protocol, while device completion/drain/acquire had
  only a separate native authority script. A single value-state execution
  connecting both results was still missing.
- Optimization instance: TMA/WGMMA double-buffer lifetimes through device
  completion and final loan return. A correct matrix and separately returned
  authority do not establish that both facts hold in the same actual state.
  The connection must also reject premature completion and host reuse even if
  the scalar FIFO operation would otherwise succeed.
- Checked protocol lift: `Hopper.ByteContentsProtocol` executes the original
  prepared-plan command on erased authority, retaining FIFO/dependency errors
  and the actual source-matched `NextCompleted` guard. Successful commands
  change the protocol controller and preserve every symbolic byte payload and
  source cut. A checked success projects to the prior authority relation;
  rejection retains its original reason. Protocol scalar buffers remain
  metadata, not physical GPU bytes; physical host writes and reclamation are
  not simulated byte effects of this API.
- One language: `Iris.ByteContentsProtocol` embeds the existing source
  interpreter unchanged and combines it with checked commands. Complete
  source scripts compose with actual device drain and acquire without assuming
  a successful combined script. Every successful mixed prefix projects to the
  original authority/event relation. A unique-writer invariant is preserved
  across both kinds of action, so arbitrary successful source/protocol
  interleavings with the complete source cut have correct final matrix cells.
  These statements concern this checked data family and metadata language;
  they do not equate all weak PTX traces with SC heap histories.
- Native resources: `Iris.ByteContentsMachine` generalizes the existing
  symbolic-byte GenHeap interpretation to a fixed supplied transition whose
  successful actions are proved to preserve the allocated cell domain. It
  retains the whole-map update baseline for complete-script WP and closed
  adequacy. Controller-only protocol update/continuation rules frame all byte
  fragments locally. A checked abort preserves the controller and entire
  arbitrary frame; it does not roll back preceding successful script steps.
- Hopper witness: `HopperDoubleBufferValueProtocol` constructs one actual
  source/value/device/acquire script for independent real inputs, arbitrary
  frame bytes, bounded positive K and finite heterogeneous retries, starting
  from the publicly prepared protocol and initial ten-region byte pool.
  Its final state simultaneously has the exact real GEMM matrix fragments,
  available byte permissions, all ten returned modeled loans, live protocol
  buffers, reuse/reclaim permission, authority projection and closed native
  GenHeap adequacy. Any active actual byte claim in a successful mixed prefix
  still prevents host write/reclaim through the original source/region guard.
- Tests/reuse: twenty facts exercise a real RMW counter, actual FIFO readiness
  without source completion, source-completion rejection, permitted device
  completion, exact counter-byte preservation through drain/acquire, retained
  loans before acquire, and loan return afterward. Early acquire, host reclaim,
  host write and duplicate device completion retain their original errors;
  embedded source finishes still reject incorrect byte values. Successful and
  rejected native command rules frame an actual counter byte with half
  permission. Tests also check a separate actual public preparation run,
  general three-tile source/value/protocol existence, arbitrary successful
  interleaving correctness, and nonzero GEMM result 96 together with all ten
  returned regions and native adequacy. All 56 new public proofs (36 production
  and twenty test facts) have exact audit registrations. Existing source APIs,
  strict assertions and diagnostic requirements are retained.
- Remaining: byte-value composition from the prepared protocol through
  source/device/drain/acquire is now closed in this model. Native public
  preparation is still separate from its checked original interpreter run.
  Physical allocation and value/protocol/runtime/compiler correspondence,
  zero-K value scripts, general weak RF/proxy realization, dynamic layouts and
  original case/instruction/observer audits remain. Full-source native
  adequacy retains whole-map ownership; local protocol rules do not establish
  a footprint-local full-source WP. All seven original cases stay partial and
  exact paper 81-form parity stays unconfirmed. No new GPU, IEEE/logits/token,
  speedup, fairness/physical-progress or research-novelty claim is added.
- Validation: `/tmp/ptx-value-protocol-full-gate.log` exited zero with `All
  verifier checks passed`: 47 Rust tests, Clippy with warnings denied, six
  rejection-harness tests, generated-file comparisons, 3786 Lean jobs, 7875
  audited declarations and 7844 environment-resolved public theorem names,
  all 674 strict assertions individually rejected, and 31 PTX fixtures assembled.
  Exact audit registration, new-source whitespace/proof-escape checks and
  `git diff --check` pass. No new module emits a Lean warning, no original
  strict assertion/diagnostic requirement changes, and no heartbeat/recursion
  limit is raised. The original control test retains SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-07 00:23:28 UTC with 31 current
  source hashes. GPU evidence remains 2026-11-05 07:46:53 UTC, with fifteen
  source hashes and 25 finite cases; no new GPU execution or performance
  measurement was performed.
- Goal ledger snapshot at 2026-11-07 00:23:42 UTC: 15,880,068 tokens versus
  the preceding published 15,775,915, a difference of 104,153. This is interim
  tool accounting, not final billed usage or a completion report. The original
  goal remains active. Next: connect native public preparation to the complete
  value/protocol execution while retaining the original source-matched
  completion and pending-access guards; continue the zero-K, physical runtime/
  compiler and original case/instruction obligations without changing scope.


## Research record: native public preparation from the initial no-loan protocol

- Previous turn classification: progress. The same actual source/value/device/
  acquire execution had correct GEMM fragments and all returned modeled loans,
  but started at the separately checked publicly prepared state. Native public
  preparation was not part of that same GenHeap language or execution witness.
- Optimization instance: preparing the TMA/native/ordinary/resource lifetime
  reservations before executing the double-buffer plan. An initial zero device
  counter does not prove that every loan and queue entry has been submitted.
  Recording an incomplete frontier, changing the access mode at the same ticket
  count or extending the plan after source access begins can invalidate the
  earlier pending-use argument.
- Preparation boundary: `Iris.ByteContentsPreparation` embeds actual public
  borrow/enqueue requests and event recording in the existing symbolic-byte
  state. Requests require an untouched source cut, an available byte pool and
  a fresh reserved event. Sealing checks the exact `Preparation.Ready` command
  queue before recording its frontier. Source/device actions require the
  recorded exact frontier. The original request/record interpreter errors are
  preserved. Three explicit preparation errors distinguish a closed phase,
  incomplete/wrong queue and unprepared execution; earlier source/protocol
  errors retain their original meaning.
- Reusable construction: `PreparationExecution` derives actual request scripts
  from the original ready-request rules, preserving byte cells/source cut and
  projecting to the real public interpreter run. A real seal establishes the
  execution gate. `Async.RecordedEvents` proves that existing frontier records
  survive the original host/device commands and cannot be overwritten. Once
  sealed, further requests and duplicate sealing are rejected, including after
  acquire returns loans. Actual subsequent source/protocol scripts embed and
  project without bypassing their original source-matched completion guards.
- Native resources: controller-only preparation update/continuation rules frame
  arbitrary byte fragments. Checked rejection retains the controller and its
  complete frame. Complete native-script WP and closed adequacy still use the
  existing whole-map heap baseline. The guards and script selectors are
  proof-level definitions; no new CLI CUDA launcher/extractor is supplied.
- Hopper client: `HopperDoubleBufferPublicValues` constructs native preparation
  from the initial protocol with no loans and the actual initial ten-region byte
  pool, then the full actual source/value/device/acquire script. Independent
  represented real A/B, arbitrary frame bytes, bounded positive K and finite
  heterogeneous retries retain the same final matrix, available cells, live
  scalar protocol buffers, all returned modeled loans and closed native GenHeap
  adequacy. No initial prepared-state/loan certificate is assumed. Public
  preparation agrees with its original interpreter run. The native client's
  unique-writer invariant proves matrix correctness for every successful full
  client run with a complete source cut. For a native prepared prefix followed
  by arbitrary embedded execution, active actual byte claims still block host
  writes/reclamation through the original region/loan guard.
- Tests/reuse: 28 facts cover initial no-loan state, actual native preparation,
  ready queue/loan provenance, the real seal, and complete two-step preparation.
  The original interpreter can record an incomplete frontier, while native seal
  rejects it. A matching ticket count with the wrong resource mode is also
  rejected. Source claims/device steps before sealing, requests after sealing,
  duplicate sealing, preparation after source completion or during an actual
  held byte claim are rejected. Invalid-buffer and aliased-copy requests retain
  their original errors. Actual counter bytes are preserved; successful public
  requests and rejected unprepared claims frame real half-permission bytes.
  Tests also instantiate native three-tile preparation and a complete nonzero
  GEMM client starting with no loans, with result 96 and returned modeled loans
  in the same adequate execution. All 70 new public proofs (42 production and
  28 test facts) have exact audit registrations; all previous strict assertions
  and diagnostic requirements remain unchanged.
- Remaining: native public preparation is now connected for this bounded
  positive-K fixed-plan client. Physical allocation and command/value/runtime/
  compiler interpretation remain separate: protocol scalar buffers are not
  GPU bytes, and metadata host-write/reclaim permission does not simulate those
  physical effects. Zero-K value scripts, general weak RF/proxy realization,
  dynamic layouts/generations and original case/instruction/observer audits
  remain. Whole-map closed adequacy does not establish a footprint-local
  full-source WP. All seven original cases stay partial and exact paper 81-form
  parity stays unconfirmed. No new GPU, IEEE/logits/token, speedup,
  fairness/physical-progress or research-novelty claim is added.
- Validation: `/tmp/ptx-public-preparation-full-gate.log` exited zero with
  `All verifier checks passed`: 47 Rust tests, Clippy with warnings denied,
  six rejection-harness tests, generated-file comparisons, 3791 Lean jobs,
  7945 audited declarations and 7914 environment-resolved public theorem
  names, all 674 strict assertions individually rejected, and 31 PTX fixtures
  assembled. After the first successful gate, the started-source regression
  was strengthened to use the existing actual completed RMW cut; the entire
  gate was rerun and passed. All 70 new proofs have exact audit entries.
  New-source whitespace/proof-escape checks and `git diff --check` pass.
  No new module emits a Lean warning, no strict diagnostic requirement changes,
  and no heartbeat/recursion limit is raised. The original control test retains
  SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-07 00:47:45 UTC with 31 verified
  current source hashes. GPU evidence remains 2026-11-05 07:46:53 UTC, with
  fifteen source hashes and 25 finite cases; no new GPU execution or
  performance measurement was performed.
- Goal ledger snapshot at 2026-11-07 00:47:59 UTC: 15,968,283 tokens versus
  the preceding published 15,880,068, a difference of 88,215. This is interim
  tool accounting, not final billed usage or a completion report. The original
  goal remains active. Next: extend the actual source/value/native client to
  the zero-K branch using its existing complete source/control/memory witness,
  while retaining physical runtime/compiler and original case/instruction
  obligations without changing scope.


## Research record: zero-K byte values and one bounded-K native GEMM contract

- Previous turn classification: progress. Native public preparation, actual
  source byte values, source-matched device completion and acquire were joined
  from the initial no-loan protocol for the bounded positive-K data family.
  The zero-K branch still lacked that byte-value/native client construction.
- Optimization instance: a zero-length reduction in the same double-buffer
  kernel. There are no input reads, TMA transfers or native MMA operands, but
  the actual source still initializes/invalidates both barriers and writes the
  complete output. Replacing it by an empty execution would retain arbitrary
  initial output bytes and lose the barrier-storage lifetime obligations.
- Exhaustive source/value construction: `HopperDoubleBufferZeroValues` proves
  that every actual use in any source-well-formed completed zero-K candidate
  is an ordinary/resource kernel use. The existing minimal output and barrier
  regions bound all such uses. Existing no-read and complete memory/control
  witnesses discharge future-read obligations without an input-value premise.
  The common checked inventory/cycle construction then gives an actual full
  value script, available allocated pool and closed native GenHeap adequacy.
  Unique actual output writers give real zero fragments at every matrix cell.
  Candidate oracles and trace order are not assumed canonical; existing source
  reconstruction supplies their actual event correspondence.
- Minimal public client: `ZeroPublicValues` uses exactly two modeled write
  reservations, for output and opaque barrier storage. Native preparation,
  actual source actions, source-matched two-ticket completion and acquire run
  in the same language from the initial no-loan protocol. Correct zero matrix
  fragments, available cells, both returned loans and native closed adequacy
  coexist in one final state. Active actual claims in native prepared prefixes
  retain the original host write/reclaim guard. No descriptor/input reservation
  or dummy transfer is fabricated for zero K.
- Reusable rules: `Iris.ByteContentsImmutable` preserves unwritten values
  across every preparation/source/protocol action and successful client script.
  The zero-K instance preserves opaque barrier payloads in this model; resource
  operations do not encode physical mbarrier data, and the preserved payloads
  must not be interpreted as physical storage contents. Generic
  `Async.Drain.returned_can_write/returned_can_reclaim` derive metadata reuse
  permission from returned loans and live buffers at any valid index, without
  assuming a particular buffer count. Closed-source scripts continue to use
  the existing whole-map native heap baseline.
- One bounded-K API: `HopperDoubleBufferFullValues` selects the minimal two-
  region zero-K client or the existing ten-region positive-K data client.
  For every natural K at most 2^28, independent represented real A/B, arbitrary
  frame bytes and finite heterogeneous positive-K retries, it proves universal
  successful-complete-run matrix correctness and a separate actual full native
  execution witness with returned loans and closed GenHeap adequacy. Both
  branches use the same independent real GEMM specification and generated PTX
  source. This does not assert heap realization of all weak PTX traces.
- Tests/reuse: 23 facts cover actual source validity/completion with initial
  payload 99, no-read behavior for arbitrary completed zero-K candidates, all
  output writes, initially nonzero output cells, both barriers' full eight-byte
  initialization/invalidation spans and exhaustive actual-use pool membership.
  Full native clients exist for arbitrary completed zero-K sources; every
  successful complete client has zero output, and opaque barrier payloads are
  preserved in the model. Missing the barrier reservation prevents sealing.
  The scalar FIFO can advance before source work, but native device completion
  rejects that attempt using an actual pending zero-K initialization event.
  Missing the second completion or final acquire prevents loan return/reclaim.
  Both returned regions permit reuse/reclaim. Common bounded-K tests exercise
  the unified successful-run contract and complete native existence witness.
  All 45 new public proofs (22 production and 23 test facts) have exact audit
  registrations. No heartbeat/recursion limit is raised; the fixed pool list is
  kept irreducible during inference to avoid eagerly evaluating all its cells.
- Remaining: the zero-K byte-value/native gap is now closed in this model,
  including its minimal public preparation and active-use guard. Physical
  allocation, command/value/runtime/compiler interpretation, general weak RF/
  proxy realization, dynamic layouts/generations and original case/instruction/
  observer audits remain. Full-source native adequacy retains whole-map
  ownership. All seven original cases stay partial and exact paper 81-form
  parity stays unconfirmed. No new GPU, IEEE/logits/token, speedup, physical
  fairness/progress or research-novelty claim is added.
- Validation: `/tmp/ptx-zero-full-client-gate.log` exited zero with `All
  verifier checks passed`: 47 Rust tests, Clippy with warnings denied, six
  rejection-harness tests, generated-file comparisons, 3796 Lean jobs, 7990
  audited declarations and 7959 environment-resolved public theorem names,
  all 674 strict assertions individually rejected, and 31 PTX fixtures assembled.
  All 45 new public proofs have exact audit registrations. New-source whitespace/
  proof-escape checks and `git diff --check` pass. No new module emits a Lean
  warning, no strict assertion/diagnostic requirement changes, and no heartbeat/
  recursion limit is raised. The original control test retains SHA-256
  `f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4`.
- Assembly evidence refreshed at 2026-11-07 01:14:02 UTC with 31 verified
  current source hashes. GPU evidence remains 2026-11-05 07:46:53 UTC, with
  fifteen source hashes and 25 finite cases; no new GPU execution or performance
  measurement was performed.
- Goal ledger snapshot at 2026-11-07 01:14:15 UTC: 16,308,529 tokens versus
  the preceding published 15,968,283, a difference of 340,246. This is interim
  tool accounting, not final billed usage or a completion report. The original
  goal remains active. A fresh coverage inspection confirms shuffle frontend/
  participant matching is still absent from the current accepted PTX subset.
  Next: implement that explicit original-goal feature and its source/event
  matching and negative tests, while retaining the original case/instruction,
  runtime/compiler and numerical obligations without changing scope.


## Research record: fixed warp shuffle source execution and agreement

- Previous turn classification: progress. The bounded-K Hopper native client
  milestone remains unchanged. This turn addresses the explicit shuffle gap
  in the original atomics/shuffle goal; it adds no new optimization performance
  or research-novelty claim. All seven original acceptance cases remain partial.
- Limitation: ordinary scalar execution cannot account for values supplied by
  other lanes, dynamic rendezvous, optional result predicates or exited peers.
  Treating shuffle as a local copy or a memory barrier would change its meaning.
- Source semantics: four fixed `shfl.sync.{up,down,bfly,idx}.b32` forms generate
  typed Lean program data. The source machine delegates actual ordinary scalar
  slots and intercepts shuffle slots, recording inputs and value/predicate
  oracle results. Generation is computed per (mode, wrapped membermask), rather
  than supplied as an unproved annotation. Word declarations, operand widths
  and optional predicate types are checked. Shuffle plus async/tensor forms is
  explicitly rejected until a composed source semantics is available.
- Reusable rules: selection follows the packed c and low-five-bit b rules,
  including signed up-underflow, clamp failure returning the caller's input,
  segment behavior and bfly selection into a lower segment. Global matching
  requires named same-warp participants to arrive or already exit; source
  agreement requires the actual selected participating peer in the same dynamic
  group. Different static PCs may match on this sm_70+ fragment. Undefinedness
  remains an independent safety obligation, with unconstrained local oracle
  replies outside defined groups. Neither a conditional Agreement nor a Triple
  alone proves a general kernel Safe theorem.
- Control and memory: a separate control graph includes local return, source
  order, rendezvous, exits and ordinary barrier control. An explicit four-edge
  cycle refutes two incompatible groups mutually claiming each other exited.
  This is a graph counterexample, not a source-produced witness. The shuffle
  graph adds no synchronizes-with edge to the ordinary memory projection.
- Actual source case: the mechanically translated three-slot two-lane bfly
  program has parameterized source runs for arbitrary oracle values/predicates,
  complete source coverage and control admission. Definedness holds for the
  family. Global Agreement is equivalent to the exchanged wrapped u32 values
  and both true predicates; it gives actual final register contents. A correct
  complete source/control/defined/agreement witness exists independently of
  that implication. Wrong values and wrong predicates remain locally executable
  but cannot satisfy global agreement. The fixture exports no memory result and
  can be optimized away; it is not used as GPU output evidence.
- Finite execution evidence: four separate exported probes store both values
  and predicates with output guards. Independent host integer selection checks
  cover all modes, clamp/segment/high-bit behavior, u32 input wrap, 3-D thread
  linearization, two warps and defined partial-warps. Full GPU report is stored
  separately in gpu-evidence.json. These probes have checked typed translations
  and finite execution tests; universal source-to-output kernel contracts for
  the four probes have not been established.
- Sources: semantics were checked against the archived NVIDIA PTX 9.4
  [shuffle specification](https://docs.nvidia.com/cuda/archive/13.4.2/parallel-thread-execution/index.html#data-movement-and-conversion-instructions-shfl-sync).
  The paper's shuffle input/oracle and generation/group approach is a useful
  reference, not an exact instruction inventory or compiler correctness proof:
  [Formalizing PTX](https://sf-tensor.com/papers/formalizing-ptx.pdf).
- Remaining: general source-family safety/completion and output contracts,
  async/tensor/shuffle composition, shuffle-specific Iris lifting and full
  execution/compiler/runtime correspondence. Exact paper 81-form parity remains
  unconfirmed. No floating-point bitcast, IEEE/logits/token, performance,
  physical progress/fairness, TTGIR frontend or TTGIR-to-PTX refinement is added.
- Validation checkpoint (2026-11-07 01:56:41 UTC): full scripts/check.sh
  exited 0 after adding the newly exported CheckedProgram.valid proof field
  to the exact dependency audit. 50 Rust tests, Clippy with -D warnings,
  six rejection-harness tests, 3,809 Lean jobs, 8,057 audited declarations and
  8,026 environment-resolved authored theorem names pass. All 680 negative
  assertions were individually refuted by evaluation with strict diagnostic
  matching. The 66 new authored public proofs and the exported proof field have
  exact audit entries; allowed axioms, rejection diagnostics and proof limits
  were not weakened. The 36 hashed PTX fixtures assembled at
  2026-11-07T01:56:24.950855+00:00. The unchanged Hopper control test hash is
  f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4.
- GPU checkpoint: scripts/check_gpu.sh --report docs/gpu-evidence.json exited 0
  at report timestamp 2026-11-07T01:52:59.349389+00:00 on the existing sm_89
  RTX 4060 Laptop GPU through the version-matched compatibility driver.
  All 19 source hashes match the current fixtures: 45 exact-byte comparisons
  and one completion-only test pass, including 21 shuffle comparisons. This
  gives no Hopper hardware evidence and no general floating-point guarantee.
- Goal accounting at this checkpoint: 16,508,063 tokens, an increase of
  199,534 over the last published 16,308,529-token checkpoint. This includes
  the in-progress shuffle work carried across the preceding continuation and
  is interim tool accounting, not final billed usage. The full original goal
  remains active. Next: source-family shuffle safety/output contracts and
  checked composition with async/tensor execution; keep exact instruction,
  runtime/compiler, physical-byte and original case boundaries explicit.


## Research record: all completed shuffle sources, safety and observation

- Previous turn classification: progress. Four shuffle modes, source semantics,
  matching, control and a generated two-lane constructed family were checked.
  The family result still required the candidate to have that supplied shape;
  it did not establish Safe for every source-valid completed candidate.
- Optimization instance: a register-exchange pattern used in warp cooperation.
  This work closes an engineering-baseline proof gap. No new performance,
  bottleneck, optimization-method reuse or research-novelty result is claimed.
- Source reconstruction: generic Shuffle completion lemmas prove that a done
  run cannot accept further source steps and that two successful completed runs
  with the same context/oracle have identical counts, full states and events.
  Generic unique-thread/source-event lookups retain original emitted indices.
  For the generated three-slot pair program, arbitrary source oracles have a
  complete three-step execution. Comparing it with any actual completed run
  derives the actual count and full trace shape; no count or canonical oracle
  is assumed. Launch validity/coverage gives both lanes' actual arrivals.
- Universal contracts: Pre fixes the actual two-thread launch and parameter
  list, leaving initial bytes, source oracles and trace order arbitrary.
  Source well-formedness plus completion derives Defined and ControlAdmitted.
  The public Safe theorem does not require a Defined premise. Actual global
  Agreement gives every member's final destination equal to the other lane's
  original index and its predicate equal to true. This register specification
  does not inspect oracle answers. The proof covers every completed candidate
  of this fixed kernel, rather than only the prior constructed family.
- Memory and non-vacuity: all such sources have an empty ordinary-memory view.
  Reusable polymorphic Event.Empty rules construct actual generic-memory and
  initial-byte observation witnesses for empty views, and derive the observer
  frame from arbitrary admitted observations. They do not discharge source or
  collective obligations. The pair kernel has a Triple preserving every byte
  in any specified global observation domain, and a separate Nonvacuous theorem
  joining full source coverage, completion, control, definedness, agreement,
  memory consistency and observer conditions. A nonempty two-byte observation
  exercises this witness; memory framing is not an exported shuffle-value test.
- Tests: reversed source trace order, changed unused memory answers and future
  shuffle answers still give a valid complete source and agreed actual final
  registers. Four-step padding faults, a fabricated padded trace is not source
  produced, and omitting one participant violates launch coverage. Completion
  uniqueness and source proofs have no raised recursion/heartbeat limits.
  Four extra strictly evaluated rejection assertions cover padding, premature
  completion, silently reordered witnesses and unissued queries. All 42 new
  public proofs (28 production, 14 tests) have exact dependency-audit entries.
- Remaining: the four exported probes still have typed translations and finite
  GPU checks, without universal source-to-output/safety contracts. General
  warp geometries, async/tensor/shuffle composition and shuffle-specific Iris
  lifting remain open. Safe here quantifies over completed model executions;
  it is not physical progress/fairness or full ISA undefined-behavior freedom.
  Compiler/runtime/physical allocation correspondence, exact paper instruction
  audit and the original case boundaries remain unchanged. All seven original
  acceptance cases stay partial; the full goal remains active.
- Validation checkpoint (2026-11-07 02:11:39 UTC): full scripts/check.sh
  exited 0. 50 Rust tests, Clippy with -D warnings, six rejection-harness tests,
  3,815 Lean jobs, 8,099 audited declarations and 8,068 environment-resolved
  authored public theorem names pass. All 684 negative assertions were
  individually refuted with unchanged strict diagnostic matching. All 36 PTX
  fixtures assembled at 2026-11-07T02:11:11.371984+00:00. Proof-construct and
  whitespace checks pass; no allowed axiom, proof limit or rejection criterion
  was relaxed. The unchanged Hopper control fixture retains SHA256
  f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4.
- Retained finite GPU evidence: the 2026-11-07T01:52:59.349389+00:00 report
  still matches all 19 current source hashes, with 45 exact-byte comparisons
  and one completion-only check. This turn changes proofs/tests and no GPU
  fixture or GPU runner; that report is separate, previously measured evidence.
  It is not a new GPU run or Hopper/IEEE proof.
- Interim goal accounting: 16,577,785 tokens at this checkpoint, an increase
  of 69,722 from 16,508,063. This is tool accounting, not final billed usage.
  The original full goal remains active. Next: universal contracts for the
  exported shuffle probes and checked composition with async/tensor semantics,
  retaining the remaining original case and correspondence obligations.


## Research record: four exported shuffle sources, store values and observer frame

- Previous turn classification: progress. All completed sources of the fixed
  register-only pair had Safe, register/frame contracts and a joined complete
  execution/memory/observer witness. The four exported probes still lacked a
  universal source-to-store connection; their GPU tests alone did not provide it.
- Optimization instance: warp register exchange with an exported integer word
  and predicate flag. This is an engineering baseline for warp cooperation,
  not a measured optimization or a claimed new verification method. No new
  performance/bottleneck or optimization-method reuse result is asserted.
- Mechanical source connection: a common code skeleton is exactly equal to
  each generated up/down/bfly/idx program and inherits checked typing. Local
  scalar delegation rules retain actual PCs and delegate actual instructions;
  shuffle slots are intercepted rather than erased. All five parameter loads,
  3-D thread/dimension reads and arithmetic, shuffle, predicate branch, pointer
  calculation, both integer-byte stores and return are checked against that code.
- Complete local source: for every mode, parameter values, execution context
  and arbitrary local oracle, the actual generated code has a complete 24-step
  local execution when its five parameter bindings are present. Both predicate
  paths have the same count but skip different static PCs. An actual completed
  run has exactly that count, full final state and three emitted events, by
  generic completion uniqueness. Launch-wide reconstruction assumes actual
  source well-formedness/completion, not a supplied oracle or candidate shape.
  This local construction is not a launch-wide consistency/non-vacuity witness.
- Actual values: source shuffle/store indices 0/1/2 are related to ordinary
  memory store indices 0/1 after filtering. Under the separately checked global
  Defined and Agreement obligations, the selected peer's source input and
  predicate are actually exported. The independent integer formula uses base,
  warp start and selected lane, not oracle answers or final registers. Modular
  3-D arithmetic equals mathematical linear indexing modulo 2^32 even for large
  dimensions; the input formula requires no hidden no-overflow premise. The
  expected selection reuses the normative mathematical shuffle selector; finite
  GPU evidence still uses its separate host integer reference. The final stored
  bytes and flag agree with that formula for every admitted completed source.
- Observable frame: polymorphic aligned-four-byte footprint rules derive that
  overlapping accesses have the same footprint. They allow equal-footprint
  races and do not assert unique writers or race freedom. The probes have only
  two four-byte writes per trace and no ordinary reads. Aligned output starts
  therefore rule out mixed-size races. Observer conditions force initial values
  outside the input/geometry-derived union of actual wrapped output spans.
  This supplies a universal frame Triple; it does not prove observed array values.
- Wrap boundary: source u32/u64 truncation is retained throughout. Value and
  flag starts wrap separately, as in the actual operands. A flag address can
  wrap to zero even for aligned output. The computed OutputFootprint includes
  that byte and prevents an unsound claim that every address below Out is a
  preserved guard. Physical allocation and layout/extent bounds remain duties.
- Tests: all modes and both branch predicates have actual source runs with
  arbitrary reply words; 24 steps are derived and a 25th faults. Tests cover 3-D
  numbering, word wrapping, eight-byte output stride, four-byte flag offset,
  exported zero/one flag bytes, one shuffle query versus zero memory queries,
  original/ordinary serials, wrapping output pointers, aligned wrap-to-zero and
  failed alignment. Independent value checks cover all four modes, second-warp
  offset and modular indexing with dimensions beyond one u32. Eleven additional
  strict evaluated rejection assertions cover the corresponding false claims.
- Remaining: derive launch-wide Defined/Safe from input/geometry conditions;
  construct complete consistent shuffle/control/memory/observer witnesses for
  the exported probes; prove distinct-writer final output-array contracts and
  ordinary guard intervals under explicit extent bounds. Async/tensor/shuffle
  composition and shuffle-specific Iris lifting remain open. Existing two-lane
  witnesses are not substituted for these probe obligations. Original case,
  ISA/compiler/runtime/allocation and exact 81-form inventory boundaries remain
  unchanged; all seven original cases stay partial and the full goal is active.
- Validation checkpoint (2026-11-07 02:49:29 UTC): full scripts/check.sh
  exited 0. The new 68 authored public proofs (42 production, 26 tests) and
  five exported parameter proof fields have exact dependency-audit entries.
  50 Rust tests, Clippy with -D warnings, six rejection-harness tests, 3,826
  Lean jobs, 8,172 audited declarations and 8,137 environment-resolved authored
  public theorem names pass. All 695 negative assertions were individually
  refuted with unchanged strict diagnostic matching. All 36 PTX fixtures
  assembled at 2026-11-07T02:47:42.236140+00:00. Construct and whitespace checks
  pass. No allowed axiom, proof limit or rejection criterion was weakened.
  The existing Hopper control test remains byte-for-byte unchanged, SHA256
  f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4.
- GPU evidence: the retained 2026-11-07T01:52:59.349389+00:00 report still
  matches all 19 current source hashes. Its 45 exact-byte comparisons and one
  completion-only check, including 21 shuffle comparisons, are prior finite
  execution evidence. This turn changes Lean proofs/tests and rejection
  coverage, not GPU fixture code or the runner; no new GPU run is claimed.
- Interim goal accounting: 16,712,657 tokens, an increase of 134,872 from the
  last published 16,577,785-token checkpoint. This is tool accounting, not final
  billed usage. The original full goal remains active. Next: derive probe Safe
  from checked launch/mask/selected-lane closure conditions and construct joined
  consistent launch/observation witnesses, then finish final array contracts
  and async/tensor composition without changing the original scope.

### Prototype goal: named auxiliary gaps and independent acceptance (2026-11-07)

- Objective: retain the original paper-capability scope and seven case groups,
  while making an end-to-end prototype separately auditable. A named auxiliary
  lemma may remain open; a top-level functional, safety or non-vacuity VC may
  not be assumed directly or through a wrapper. This changes the acceptance
  policy, not the mathematical statements of existing strict results.
- Instance and original limitation: the previous gate required all authored
  proof dependencies to be closed and had no separate conditional-result
  registry. A prototype could not declare a limited proof gap with an exact,
  automatically checked impact list. Merely broadening its axiom allowlist
  would also blur the status of already proved results.
- Implementation: the strict `Ptx` library and checker remain independent.
  `PtxPrototype`, `prototype.toml` and `scripts/check_prototype.sh` add named
  proposition assumptions in one designated module, exact Lean type hashes,
  purpose/review/discharge tasks, alternative proofs of unchanged VC types,
  transitive axiom audits and actual affected-VC checking. All seven case
  groups retain correctness, complete-execution/non-vacuity and concrete
  instance roots; all twelve capability groups retain explicit checked roots
  and separate implementation gaps. The production registry starts empty.
- Audit boundary: actual Lean proof terms and environments supply declaration
  kinds, proposition types and transitive axiom inventories. Definitional
  equality comparisons reject a renamed auxiliary with the same type as a
  protected top-level VC. Expanding project definitions, opaque definitions
  and structure constructor types detects structural wrappers, including
  aliases in arbitrary namespaces. Anonymous sorry, extra unregistered
  axioms, stale statements/hashes/impact lists, changed VC types and deleted
  acceptance groups fail closed. These checks cannot decide arbitrary
  mathematical equivalence or consistency; each registered statement still
  needs the required scope review. The report never turns conditional proof
  into strict proof or GPU execution into a lemma discharge.
- Reuse evidence: actual Lean fixtures test both direct and transitive use of
  an arithmetic auxiliary, strict and conditional classifications, and the
  rejection paths above. The positive auxiliary quantifies two arbitrary
  addends, while its synthetic client VC specializes one addend; it is not
  merely the same VC under a different name. A separate renamed-VC negative
  test checks precisely that failure mode. All 18 audit tests passed after
  this correction. Fixture assumptions are isolated temporary files and do
  not enter the production registry.
- Strict extension retained: mathematical 3-D linearization bounds/inversion/
  injectivity and finite launch-thread coverage/uniqueness are proved. The
  exported shuffle probes derive source safety from finite launch closure,
  including named active partial warps; complete source/control/value/memory/
  observer witnesses are joined under explicit single-CTA bounded output
  layout conditions. Fifty new authored proof names and four layout proof
  projections have exact strict-audit entries. Their final observed output
  array contract and async/tensor composition remain open.
- Evidence format: the one-command prototype gate runs audit regression,
  unchanged strict regression, prototype compilation and actual dependency/
  type checks. By default it also runs fresh finite exact-byte GPU checks;
  `--gpu off` records hardware evidence as not run. It records theorem scopes,
  statuses, assumptions, capability gaps, source fingerprints and adjacent
  command logs. Its successful verdict explicitly allows declared gaps and
  is not a declaration of complete formal verification.
- Remaining: exact paper 81-form correspondence is unconfirmed. Reinspection
  of the paper's section 5.1 finds counts (66 scalar/control/memory, 5 Ampere,
  10 Hopper), not an enumerated opcode/qualifier artifact. No unknown form is
  fabricated or counted as covered. Broader instruction composition, physical
  allocation/compiler/runtime/value correspondence and Hopper hardware
  execution remain open, as do the recorded model-specific scope limits.
  This is verification-tool engineering; no new optimized inference instance,
  benchmark improvement or research novelty is claimed.
- Validation checkpoint: `scripts/check_prototype.sh` exited 0 with the
  current source fingerprint unchanged. The report started at
  2026-11-07T05:07:01.237609+00:00 and records
  `prototype-passed-with-gaps`: seven groups' listed VC statements are strict
  proofs, zero production auxiliary assumptions, and twelve separately scoped
  capability groups. This does not upgrade their partial paper/ISA coverage.
  Eighteen actual Lean audit regressions pass. The unchanged strict gate passes
  50 Rust tests, Clippy, six rejection-harness tests, 3,835 Lean jobs, 8,226
  audited declarations, 8,188 environment-resolved public proof names and all
  695 individually rejected assertions. All 36 fixtures assembled at
  2026-11-07T05:09:21.079379+00:00. Fresh GPU evidence at
  2026-11-07T05:09:29.645787+00:00 records 45 exact-byte comparisons and one
  completion-only check, with all 19 source hashes current. The immutable
  Hopper control test still hashes to
  f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4.
- Interim new-goal accounting: 164,554 tokens at the queried checkpoint;
  separate from the old goal's 16,712,657-token checkpoint. This is tool usage
  accounting, not billing or a completion claim. The goal remains active:
  acceptance infrastructure and a declared-gap checkpoint are delivered, but
  exact per-form paper correspondence and the explicitly recorded semantic
  composition/physical-correspondence obligations have not been completed.

### Per-spelling frontend evidence and explicit paper inventory gap

- Instance: the prototype report previously exposed only a single
  `exact_instruction_inventory = unconfirmed` flag. That flag did not tell a
  reviewer which fixed forms the local frontend actually accepts, what their
  operand/target limits are, or whether its list had drifted from the parser.
- Change: `instructions.toml` lists every explicit top-level opcode dispatch
  spelling with its canonical name, version/target/declaration profile,
  positive PTX operand probe, semantics source, Rust regression and remaining
  limitations. The actual parser has 61 spellings and 60 canonical local
  forms: the two accepted qualifier orders of relaxed GPU global atomic add
  share one canonical form. This is a frontend inventory, not an inventory
  of already proved universal instruction-correctness theorems.
- Reusable checking: `scripts/instruction_inventory.py` compares the list with
  the parser's explicit dispatch arms, excluding nested operand dispatch and
  string/comment braces. It invokes the actual Cargo-built translator for
  each positive probe and for a same-operands unknown-qualifier mutation.
  Unknown instructions must exit with the unsupported-instruction diagnostic
  and produce no Lean file. All positive generated checked-program values are
  then elaborated together by Lean. Evidence records hashes for both PTX
  probes and generated Lean; the acceptance source fingerprint now includes
  the instruction registry and Cargo manifest.
- Tests: six regressions cover omitted/duplicate opcode entries, nested
  dispatch extraction, fabricated paper correspondence, wrong operand probes,
  absent semantics/regressions and cyclic canonical aliases. The first actual
  full probe run translated and type-checked all 61 spellings and rejected
  all 61 unknown-qualifier mutations. This supplements the existing Rust
  operand/width/shape rejection tests and strict semantic counterexamples;
  it does not replace them.
- Paper scope: the paper's section 5.1 reports 66 scalar/control/memory forms,
  five Ampere forms and ten Hopper forms. An enumerated opcode/qualifier
  source artifact has not been located. Each local spelling is explicitly
  `paper_mapping = unconfirmed`, and the report includes that source gap,
  the three paper group counts, all local probes and all per-entry limits.
  No 81-minus-local subtraction or invented paper opcode is reported. Fixed
  qualifiers, operand shapes and alias conventions make those counts
  incomparable until the paper inventory is available. Full paper parity
  remains unverified, not silently treated as a prototype pass.
- Proof and research boundary: no Lean semantics or theorem statement was
  changed, and no auxiliary assumption was added. This is acceptance tooling
  reused across integer, scalar, shuffle, Ampere and Hopper frontend profiles;
  it is not a new optimization or a novel ownership proof rule. Compiler,
  runtime, physical allocation, IEEE and Hopper hardware boundaries remain.
- Validation checkpoint: the current one-command acceptance exited 0 with
  `prototype-passed-with-gaps`, started at
  2026-11-07T05:16:56.092448+00:00. Its source fingerprint matches the current
  worktree. All 61 positive translations, all 61 generated typing checks and
  all 61 unknown-qualifier rejections pass; the manifest and report retain
  every local form's unconfirmed paper mapping. Six inventory regressions and
  18 actual Lean assumption-audit regressions pass. The unchanged strict gate
  passes all 695 negative assertions, 3,835 Lean jobs and 8,226 audited
  declarations/8,188 public names. All 36 current PTX fixtures assembled at
  2026-11-07T05:19:12.977677+00:00. Fresh GPU evidence at
  2026-11-07T05:19:24.208544+00:00 again passes 46 cases (45 exact-byte,
  one completion-only). Seven registered case VC groups remain strict-proof,
  with zero production auxiliary assumptions. These statuses do not upgrade
  the separate partial implementation scopes.
- Interim new-goal accounting: 213,455 tokens at the queried checkpoint, not
  final billing. Previous goal turn: progress (audit framework, shuffle
  safety/witness integration and full acceptance evidence). This turn:
  progress (per-spelling manifest, actual positive/negative/generated-typing
  checks and fresh complete acceptance evidence). The goal stays active:
  exact 81-form correspondence is still unverified, and the recorded shuffle
  observed-array/async-tensor composition and physical interpretation gaps
  remain. Next semantic unit is a universal observed-output contract for the
  existing exported shuffle probes, using the already proved distinct-byte
  writer layout and independent per-store word/predicate specification.

### Exported shuffle arrays: source values to synchronized final observation

- Instance and original limitation: the four mechanically translated
  up/down/bfly/idx probes already had arbitrary completed-source reconstruction,
  correct emitted store payloads, source Safe and a separate complete legal
  execution witness. A correct store alone did not prove that the final
  synchronized observer obtains that value. The previous six-location test
  domain also could not stand for the full 512-byte array of a 64-thread launch.
- Change: `ShuffleProbeOutput` specifies every thread's mathematical array
  address, selected-lane u32 word and predicate flag independently of its oracle
  answers and final registers. `ArrayCovered` requires all eight output bytes
  per valid launched thread; `arrayDomain` enumerates those bytes. The general
  output contract also accepts extra observation bytes and preserves arbitrary
  initial bytes outside the independent mathematical output interval.
- Proof connection: actual source stores imply integer payload bytes. Uniform
  aligned four-byte footprints establish observer eligibility; bounded
  single-CTA layout establishes unique byte writers. Existing weak-memory
  coherence initialization and observer no-stale/source-agreement rules then
  force the final observed word and flag. No new execution or value-consistency
  predicate, numerical tolerance, assumed output theorem or admitted VC is used.
  The shared `Scalar.observe_u32_write` lemma was generalized from its fixed
  scalar oracle type to arbitrary oracle answers, with its proof unchanged.
  It now supports both the existing scalar clients and shuffle candidates.
- Joined result: separate Safe, universal Triple and Nonvacuous results are
  packaged in `exported_array_verified`. `exported_observed_witness` supplies
  the same complete source/control/definedness/collective/memory/observer
  witness together with the correct observed array and frame, for any covered
  global domain. All four generated source programs are still mechanically
  related by the earlier checked code equalities.
- Tests: all four modes have a real 64-thread (4,4,4) launch and a joined
  correct-array/guard witness. The arbitrary-completed-observer theorem shows
  that initially incorrect byte 99 is actually overwritten. The mathematical
  left/right guard interval is preserved. A named active 16-thread partial
  warp (4,2,2) satisfies the same supported-mode preconditions. The former
  sparse observation domain is proved insufficient, and four additional
  strict negative propositions reject omitted array bytes, a wrong flag-byte
  address and inclusion of either guard in the exact array domain. Twenty-four
  new public proof names have exact strict dependency-audit entries.
- Scope: final array layout requires one CTA, u32-bounded thread linearization,
  aligned output and a non-wrapping u64 extent, together with the existing
  finite active-source/mask closure. Multi-CTA source safety remains broader;
  the current source output index ignores CTA IDs, so final-array writer
  uniqueness must not be inferred for several CTAs. Async/tensor/shuffle
  composition, shuffle-specific Iris lifting, physical allocation/runtime and
  full paper form correspondence remain open. No auxiliary assumption was
  added, and no optimization or new ownership research method is claimed.
- Validation checkpoint: after wiring the new module into the explicit
  negative-test imports, the one-command prototype acceptance exited 0. The
  first attempt correctly rejected an unknown-identifier diagnostic instead
  of counting it as a refuted proposition; the diagnostic matching criteria
  were not loosened. The successful report started at
  2026-11-07T05:34:25.252212+00:00 and has a current source fingerprint and
  verdict `prototype-passed-with-gaps`. All 699 negative assertions (including
  all four new array-domain counterexamples), 3,837 Lean jobs, 8,250 audited
  declarations and 8,212 public proof names pass. Seven original case groups'
  registered VCs and the new shuffle verified/witness roots have no additional
  axioms. The production auxiliary registry stays empty. Six inventory tests,
  18 audit tests and all 61 positive/negative/generated-typing probes pass.
  All 36 PTX fixtures assembled at 2026-11-07T05:36:51.505010+00:00. Fresh GPU
  evidence at 2026-11-07T05:37:05.245932+00:00 has 45 exact-byte comparisons and
  one completion-only check, with all 19 source hashes current. The immutable
  Hopper control file retains SHA256
  f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4.
- Interim new-goal accounting: 483,081 tokens at the queried checkpoint, up
  from the last published 213,455; tool accounting, not final billing. This
  goal turn is progress: final observable array/frame contracts and joined
  witnesses are added and fully checked. The goal remains active. Further
  completion audit must keep the ordinary acquire/release frontend and
  memory-order gap visible: `Event/Consistency.lean` explicitly implements
  weak ordinary accesses and scoped relaxed RMWs, not general acquire/release
  or fences. The paper explicitly discusses acquire/release patterns; current
  barrier/relaxed-atomic results must not be substituted for that capability.
  Next unit: inspect the official scoped ordering rules and extend that
  supported source/model path without redefining existing semantics or
  hiding new assumptions. Exact 81-form correspondence and the recorded
  composition/physical-runtime boundaries remain unverified.

### Scoped ordered-memory source and rule layer (prototype increment)

- Instance and original limitation: ordinary generic-proxy accesses in the
  existing event model were weak, with strong scope retained only for relaxed
  RMWs. That model explicitly did not establish ordinary acquire/release.
  Adding only a synchronization edge would leave morally-strong accesses,
  observation, race/taint eligibility and atomicity using the wrong rules.
- New source path: twelve fixed global u32 forms retain relaxed/acquire read or
  relaxed/release write order and CTA/GPU/system scope in `Ordered.Instr`.
  Generated data includes complete register/parameter declarations and checked
  typing. The fixed ordered interpreter keeps the original PCs and delegates
  local scalar computation, annotating every actual emitted event with the
  original instruction's order/scope. Successful steps, finite runs and full
  source provenance have checked scalar LOCAL projections. These projections
  are not memory-consistency erasures or proof that weak and ordered kernels
  have the same allowed executions. Existing backends and fixtures retain
  their previous semantics. Shuffle/async/tensor mixtures fail closed.
- Model/rule layer: `Ordered.Memory` independently defines scoped moral
  strength, observation through RMWs, direct release/acquire synchronization,
  base causality, non-transitively extended causality, races, taint, eligible
  values, partial coherence, no-future/no-stale, single-copy/RMW atomicity and
  SC-per-location. Mixed-size races relax the constraints, rather than simply
  disappearing. Conditions are Lean predicates, not admitted axioms. The
  direct synchronization rule requires actual observation and mutually
  covering endpoint scopes; a release tag alone supplies no global fence.
  A generic publication rule proves the unique payload writer's value is read
  under those explicit consistency/eligibility/program-order obligations.
- Reference: NVIDIA PTX ISA 9.4 sections 8.8--8.10,
  https://docs.nvidia.com/cuda/archive/13.4.2/parallel-thread-execution/index.html#release-and-acquire-patterns
  and its memory-synchronization, causality and coherence subsections. This
  increment models only direct load/store patterns; fence and extended
  patterns remain unsupported. System scope contains the current device's
  launched threads only, without host or multi-device communication claims.
- Actual source evidence: `release_acquire_message.ptx` mechanically translates
  into fifteen ordered/scalar slots. Two launched threads have complete source
  traces, full launch coverage, retained producer/consumer event orders and
  exactly the actual oracle queries. A second consumer trace first reads zero,
  polls again, then reads the flag/payload; both acquire events and all three
  queries are retained. This is finite-prefix/complete-source evidence, not
  a proof that polling always terminates. Integer ordered loads fault on real
  oracle replies instead of silently converting them to zero. An explicit
  cross-CTA graph proves a CTA release does not mutually cover another CTA;
  that deliberately constructed scope graph claims no source/memory witness.
- Frontend/hardware feedback: initial assembler/JIT rejection exposed a local
  register named `%tid` shadowing the modeled special-register root. The
  fixture now uses `%index`, and the parser rejects declarations shadowing
  `%tid`, `%ntid` or `%ctaid`, with a dedicated regression. Fifty-five Rust
  tests include all new order/scope spellings, actual branch PCs, malformed
  types/operands/qualifiers, and rejected mixed backends. The local instruction
  inventory now has 73 spellings/72 canonical forms, with real translation,
  generated-typing and unknown-qualifier probes. Paper form mapping remains
  unconfirmed; the local count is not a paper coverage percentage.
- New finite GPU instance: the actual two-thread source publishes DATA=42 and
  FLAG=1, polls/acquires, exports OUT=42 and preserves both arena guards. Its
  ptxas sm_70 assembly and exact-byte execution pass. This hardware observation
  is separate from all formal results and does not close the pending VCs.
- Open proof obligations: universal message-kernel output/frame VC; derivation
  of all source read/loop/eligibility premises; a complete memory-consistent
  execution plus synchronized observer witness; ordered observer/Iris lifting;
  complete ISA/model correspondence, physical allocation/runtime and wider
  instruction composition. The registered ordered claims are local source
  correspondence and generic rules only. No top-level message-kernel VC or
  non-vacuity result is claimed. No auxiliary assumption, IEEE tolerance,
  optimized inference instance, performance improvement or new ownership
  research contribution is introduced. All original seven acceptance groups
  keep their existing scopes.
- Validation checkpoint: the complete one-command prototype gate exited 0 with
  `prototype-passed-with-gaps`, started at
  2026-11-07T06:01:00.373631+00:00, and its source fingerprint matches the
  current worktree. Fifty-five Rust tests, Clippy, six rejection-harness
  tests, six inventory regressions and 18 actual Lean audit regressions pass.
  The strict gate checks 3,843 Lean jobs, 8,308 declarations, 8,252 public proof
  names and all 703 individually refuted assertions. Fifty-eight new exact
  audit entries cover the ordered public proofs and proof-field projections.
  All 73 positive/unknown-qualifier/generated-typing probes pass. The five
  registered ordered source/rule claims have zero extra axiom dependencies;
  all seven original case VC groups remain strict-proof and the production
  auxiliary registry remains empty. All 37 fixtures assembled at
  2026-11-07T06:04:11.847331+00:00. Fresh GPU evidence at
  2026-11-07T06:04:27.335751+00:00 has 46 exact-byte comparisons and one
  completion-only check, with 20 current source hashes. The new message case
  compares all 20 arena bytes, including both guards. The immutable Hopper
  control test still hashes to
  f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4.
- Interim goal accounting: 588,971 tokens, up from the last published 483,081;
  tool accounting, not final billing. This turn is progress (new typed source
  path, local provenance proofs, explicit scoped memory rules, counterexamples,
  parser/assembler feedback and complete fresh regression evidence). The goal
  stays active. Next: construct the actual message candidate's ordered-memory
  consistency witness using unique writers and a rank across producer/consumer
  events, then add ordered observation and the universal completed-run output
  VC, preserving arbitrary finite polling prefixes. The completed source runs
  and generic visibility rule alone must not be counted as those missing VCs.

### Ordered message memory and observer witnesses

- Instance and original limitation: the translated release/acquire message
  fixture had complete source traces and a generic visibility rule, but no
  proof that its full ordered-memory constraints admitted that same trace.
  Source completion alone did not rule out a vacuous memory model or supply
  a synchronized final observation.
- Reusable construction: `Ordered.initial_co_conditions` builds a particular
  memory witness from actual byte sources, unique writers, source-value
  agreement and event ranks. Its base-order proof includes release/acquire
  synchronization as well as ordinary/barrier edges, and its observation
  proof uses the scoped moral-strength rules. Coherence, causality, atomicity,
  SC-per-location and barrier/control obligations are all discharged. Ranks
  remain sufficient proof aids for this witness; the general allowed-execution
  and correctness definitions impose no global rank requirement.
- Source/graph connection: production `ReleaseAcquireMessageSource` now owns
  the actual generated source and its finite producer/consumer/retry proofs;
  legacy tests alias that same source rather than maintaining a second kernel.
  The graph module derives all five annotated and ordinary event cases from
  those exact source traces. The memory module proves disjoint byte writers,
  actual reads-from values and their rank constraints. The SAME complete
  source candidate satisfies full `Ordered.MemoryConditions` for every initial
  symbolic-byte map, with the constructed reads-from and initial coherence.
- Ordered observation: new `Ordered.ObserverConditions` and reusable observer
  rules use ordered race/taint eligibility, not the earlier weak predicates.
  The selected observer accounts for every actual unique writer and preserves
  arbitrary initial bytes elsewhere. A domain covering all global bytes
  0..263 includes all three four-byte cells and intervening/prefix/suffix
  guard regions. The independent postcondition requires DATA=42, FLAG=1,
  OUT=42 and unchanged bytes outside those three mathematical intervals.
  Uniform aligned footprints establish absence of mixed-size races for any
  reads-from map; distinct writers establish observer eligibility.
- Joined result: `nonvacuous` supplies complete source, full ordered memory and
  synchronized observer witnesses for any launch with the fixed two-thread
  geometry and parameter bindings, independently of its initial byte map.
  `complete_observed_execution` joins that same execution with the independent
  word/frame postcondition. `all_observers_of_actual_candidate_correct`
  quantifies over all admitted observers/RF/coherence of THIS actual source
  candidate, not over arbitrary completed source candidates.
- Negative and concrete evidence: tests instantiate zero and initially-99
  maps, check the independent output byte and both outer guard intervals,
  retain actual polling-retry source evidence, reject a stale initialization
  source for the payload while preserving the real release/acquire flag
  synchronization, and reject an observer that retains initialization after
  completion. Those are semantic no-stale proofs, not parser failures or
  unexplained rejection diagnostics. Sixty-nine exact new dependency entries
  cover production rules/source/graph/memory/observation proofs, concrete
  regressions and the four observer proof-field projections.
- Scope and next obligation: the new existence precondition `SourcePre` fixes
  only geometry and bindings. It is intentionally too weak for a universal
  OUT=42 theorem: a nonzero initial flag can let a consumer proceed before
  publication. The future universal-client precondition must constrain flag
  initialization (e.g. represented u32 zero), in addition to source/layout
  obligations. Current existence for arbitrary initial bytes instead chooses
  the legal publisher-before-consumer witness. Next: reconstruct arbitrary
  completed source runs, including every finite polling prefix; derive final
  flag observation and payload eligibility; prove the universal output/frame
  VC under its actual initialization precondition. A canonical successful
  candidate must not replace that VC. No VC or auxiliary lemma was admitted,
  and no interpreter, memory constraint, numerical objective or strict
  rejection criterion was weakened. Ordered Iris/runtime interpretation,
  wider instruction composition and exact paper-form inventory remain open.
- Research accounting: this is verification-tool engineering and reuse of a
  witness construction/observer rule across source clients, not an inference
  optimization, new performance claim or asserted ownership-method novelty.
- Validation checkpoint: complete prototype acceptance exited 0, report start
  2026-11-07T06:22:31.332124+00:00, with a current source fingerprint and
  `prototype-passed-with-gaps`. The strict gate passes 3,850 Lean jobs,
  8,377 audited declarations, 8,319 public proof names and all 703 negative
  assertions. Fifty-five Rust tests, Clippy, six rejection-harness tests,
  six inventory tests, 18 actual Lean audit tests and all 73 positive/negative/
  generated-typing probes pass. The new registered memory/observer existence
  and stale-source rejection roots have no extra axiom dependencies. The seven
  original case VC groups stay strict-proof; the production registry is empty.
  All 37 fixtures assembled at 2026-11-07T06:28:14.430808+00:00. Fresh GPU
  evidence at 2026-11-07T06:28:39.298816+00:00 passes 46 exact-byte comparisons
  and one completion-only check, with all 20 source hashes current. The
  immutable Hopper control file retains SHA256
  f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4.
- Interim goal accounting: 652,295 tokens, up from the last published 588,971;
  tool accounting, not final billing. Previous goal turn was progress (ordered
  source and scoped memory rules). This turn is progress (reusable scoped
  memory/observer constructions, exact source-derived graph, a joined legal
  execution with independent outputs/frame, and semantic rejection tests).
  The goal remains active. Next close the universal completed-source output
  VC under represented-zero flag initialization and source/layout preconditions,
  with arbitrary finite polling iterations; do not silently restrict universal
  correctness to the constructed candidate or change the source loop to a
  one-shot read. A generic local loop-decomposition helper may be proved or,
  if needed for the prototype, centrally registered as a named auxiliary gap
  with its exact statement and impacts; the functional/non-vacuity VC itself
  must still be proved. Paper inventory, broader composition and the declared
  physical/runtime boundaries remain unverified.

### Arbitrary finite polling: source reconstruction and initialized read rules

- Instance and original limitation: a canonical legal message execution and
  one retry trace did not characterize other completed runs. Treating a poll
  as a one-shot read, fixing an oracle or bounding the number of iterations
  would change the source/correctness obligation rather than prove it.
- Generic method: `Ordered.Loop` proves run concatenation, successful prefix/
  suffix extraction, complete-run uniqueness and finite chunk decomposition
  by strong induction on the observed finite step count. Local prefix-running
  and exit-completion premises are explicit. The result neither limits the
  number of polls nor asserts that a polling execution eventually completes.
  It uses the checked local scalar projection only to compare successful run
  counts; ordered event equality comes from the original deterministic run.
- Actual source connection: `ReleaseAcquireMessageLoop` proves arbitrary-state
  pointer-preserving stepping for the generated three-instruction poll and
  three-instruction tail. Successful loads require actual integer replies;
  real replies produce the original type fault. Short local prefixes remain
  running. Polls return to PC 9 exactly on a zero wrapped u32 reply and reach
  PC 12 on a nonzero one. Their exact acquire, payload-read and output-store
  events retain qualifiers and values; the float-shadow bookkeeping of the
  scalar interpreter is preserved, not approximated away.
- Universal source result: `completed_consumer_events` reconstructs every
  completed consumer with arbitrary oracle and recorded step count as any
  finite number of zero-flag acquires, one nonzero acquire and the actual
  payload read/output store. `completed_producer_events` derives its nine
  steps and exact stores for every oracle. `UniversalSource` lifts these to
  ALL well-formed completed candidates, using actual geometry/parameter
  preconditions, full launch coverage and unique member lookup. Trace order
  is arbitrary; no canonical candidate or replies are substituted.
- Scoped read rules: generic new lemmas establish eligibility for strong or
  causal reads with a unique writer. Under explicit eligible value agreement,
  u32 bounds/nonzero value, represented-zero initialization and writer
  uniqueness, `nonzero_u32_read_observes_writer` proves that some byte actually
  observes the writer. It does not assume reads-from. With the actual endpoint
  qualifiers and mutual scope strength, that observation yields direct
  release/acquire synchronization. The key contradiction uses checked u32
  byte injectivity: reading only initialization would yield zero. All rules
  are proved; no named or anonymous auxiliary gap is introduced.
- Tests and reuse: tests apply the universal source theorem to arbitrary
  successful completed runs and full launch members, check the actual retry
  decomposition, exclude premature completion within a local chunk, reject
  wrong oracle types, and derive a flag observation from the actual legal
  memory witness with its zero initial representation. These exercise the
  same production loop/read rules; no altered test kernel replaces the PTX.
  Sixty-two exact new audit entries include the three pointer proof fields.
- Remaining: connect arbitrary candidate event indices/layouts and byte-writer
  uniqueness to those generic read rules; derive final flag synchronization
  and payload eligibility; close the universal output/frame VC with represented
  zero flag initialization. Source shape and a conditional local read rule
  are not that final VC. Existing constructed source/memory/observer witnesses
  and scopes remain intact. Ordered Iris/runtime interpretation, broader
  composition and exact paper instruction correspondence remain open. This
  is proof infrastructure engineering, with no inference optimization,
  numerical weakening, performance or novel ownership-method claim.
- Validation checkpoint: full prototype acceptance exited 0, start
  2026-11-07T06:54:19.949386+00:00, with a current source fingerprint and
  `prototype-passed-with-gaps`. The strict gate passes 3,857 Lean jobs,
  8,439 audited declarations, 8,378 public proof names and all 703 negative
  assertions. Fifty-five Rust tests, Clippy, six rejection-harness tests,
  six inventory tests, 18 actual Lean audit tests and all 73 positive/negative/
  generated-typing probes pass. Registered arbitrary-source/read roots have
  zero extra axiom dependencies; seven original case VC groups stay strict
  and the production auxiliary registry is empty. All 37 fixtures assembled
  at 2026-11-07T06:56:57.565580+00:00; fresh GPU evidence at
  2026-11-07T06:57:12.604617+00:00 passes 46 exact-byte comparisons and one
  completion-only check. The immutable Hopper control SHA256 remains
  f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4.
- Interim goal accounting: 734,007 tokens, up from the last published 652,295;
  tool accounting, not final billing. Previous goal turn was progress (joined
  ordered execution/observer witness). This turn is progress (unbounded finite
  source reconstruction, initialized read/eligibility rules and complete
  current regression evidence). The goal remains active; next assemble the
  arbitrary-candidate memory/observer proof, keeping the actual source loop
  and final VC intact rather than weakening them to the canonical witness.

### Universal initialized release/acquire message contract

- Instance and original limitation: the generated two-thread message fixture
  had a complete legal witness and arbitrary finite source-loop reconstruction,
  but its final functional VC was not connected to arbitrary candidates' byte
  layout, eligibility or synchronized observation. A canonical successful run
  cannot establish that universal result. `SourcePre` alone is too weak because
  a nonzero initial flag can allow a consumer to proceed without publication.
- Source-derived graph: `ReleaseAcquireMessageUniversalGraph` derives
  `CompletedShape` from full launch well-formedness and completion. Its producer
  and consumer lookups preserve arbitrary trace order and all finite zero-poll
  prefixes; no oracle/count/order is selected. Exact dynamic read/store serials
  and all event cases come from the actual translated source, not an assumed
  source-shape lemma or replacement test program.
- Memory connection: `UniversalMemory` derives unique byte writers, aligned
  four-byte footprints, absence of mixed-size races, scoped flag strength,
  observer eligibility and the unwritten frame. These facts hold for every
  reads-from choice. The final acquire's strong-read eligibility plus represented
  zero initialization and its source-derived nonzero word force an actual byte
  observation of the flag writer. Actual release/acquire tags then derive
  synchronization; source program order carries publication to the payload read.
  Unique causal-writer eligibility and memory agreement/no-stale force all four
  payload bytes, and u32 byte injectivity yields the word 42.
- Universal VC: `ReleaseAcquireMessageUniversal.correct` quantifies over ALL
  source-well-formed completed executions, oracles, finite polling counts, trace
  orders, RF/coherence choices and admitted observers under `Pre`. That Pre adds
  represented-zero flag initialization to the actual geometry/bindings; it does
  not assume synchronization, payload eligibility, desired results, a successful
  value script or a canonical candidate. Final DATA=42, FLAG=1, OUT=42 and all
  unwritten observed bytes follow from independent `Post`. The earlier independent
  complete source/memory/observer witness is reused to prove
  `initialized_nonvacuous` under the SAME Pre. `correct_and_nonvacuous` joins the
  two obligations without using the universal VC to construct its witness.
- Negative and concrete checks: `OrderedUniversalTests` verifies the concrete
  initialized precondition and complete legal execution. A different integer
  oracle produces the wrong payload 99 on the SAME generated PTX, and its
  consumer trace is deliberately listed before its producer. Actual source
  execution and complete launch coverage still hold. The new theorem rejects
  this source-complete candidate for EVERY RF/coherence choice, rather than
  rejecting only a preselected bad source graph. Forty-three exact audit entries
  cover the new production/test theorems and four source-shape proof projections;
  the universal VC, nonvacuity and rejection roots are registered for prototype
  dependency audit. No auxiliary or anonymous assumption is introduced.
- Reuse and limits: this instantiates the existing generic initialized-u32
  observation, scoped unique-writer eligibility and observer rules with a new
  all-candidate source graph. It is verification-tool engineering, not a new
  inference optimization, measured speedup or asserted ownership-method novelty.
  The geometry/bindings and three logical word locations remain fixed. No
  polling termination/fairness, physical allocation/runtime/ISA correspondence,
  ordered Iris lifting, fence/extended-pattern/ordered-atomic support or composed
  ordered/shuffle/async/tensor interpreter is claimed. Exact paper instruction
  parity and the broader declared capability gaps remain open. Tests and finite
  GPU executions are evidence separate from the universal formal VC.
- Targeted validation: all three new production modules, the new actual-source
  rejection tests and the complete exact dependency-print module build with
  Lean 4.35.0. TOML parsing and whitespace checks pass. Full one-command prototype
  acceptance is running; its final result will be recorded below. The previous
  goal turn only restated the goal and was no progress; this turn has concrete
  production proofs, semantic rejection evidence and integrated audit roots.
- Full acceptance checkpoint: `scripts/check_prototype.sh` exited 0 with report
  start 2026-11-07T07:13:02.412235+00:00 and verdict
  `prototype-passed-with-gaps`. Its source fingerprint is current (1,033 files).
  The unchanged strict gate passes 3,861 Lean jobs, 8,482 audited declarations,
  8,417 environment-resolved public proof names and all 703 independently false
  assertions. Fifty-five Rust tests, Clippy, six rejection-harness tests, six
  inventory tests, 18 real Lean assumption-audit tests and all 73 positive/
  unknown-qualifier/generated-typing probes pass. The new universal VC,
  nonvacuity, joined result and wrong-source rejection depend only on the
  foundation allowlist; the production auxiliary registry remains empty. The
  seven original groups' registered VC statements remain strict-proof within
  their declared model scopes; this does not close their implementation gaps.
  All 37 PTX fixtures assembled at 2026-11-07T07:15:18.813380+00:00. Fresh GPU
  evidence at 2026-11-07T07:15:31.880540+00:00 passes all 47 cases (46 exact-byte
  comparisons and one completion check). The immutable Hopper control SHA256
  remains f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4.
- Interim goal accounting: 875,297 tokens at the latest goal-tool checkpoint,
  up from the last published 734,007; tool accounting rather than final billing.
  This turn is progress. The full goal remains active: broader instruction
  composition, ordered semantic/Iris lifting and the exact paper inventory
  remain unverified. Next connect a scoped ordered-memory publication rule to
  the existing permission/borrow interface, preserving actual source and memory
  premises; a successful pure-model VC must not be presented as physical GPU
  ownership/runtime interpretation or full paper equivalence.

### Ordered source/protocol client and exclusive native Iris baseline

- Instance and original limitation: the actual release/acquire message translation
  had universal model-relative output/frame correctness and independent legal
  source/memory/observer witnesses. It did not yet have a joint native client
  interleaving the same one-instruction ordered interpreter with the existing
  async loan protocol. Treating a PTX acquire as host completion would incorrectly
  allow return/reclamation of still-pending borrowed resources.
- Executable connection: `Ordered.Client` contains the actual ordered candidate
  prefixes and Async state. A source action selects one recorded thread, invokes
  the SAME `Ordered.step`, increments its actual step count and appends its actual
  qualified events. A protocol action invokes the SAME `Async.step`; modeled
  device progress additionally checks all tracked source threads are done. No
  new source interpreter, fake successful read or weakened memory admission is
  substituted. IDs, source production, duplicate-free/full launch coverage and
  the existing async invariant are preserved by every successful action/run.
  Full source coverage makes the device-completion check about all launch
  threads, not just a selected consumer or an empty listed subset.
- Reusable source rules: `source_actions_run` proves an arbitrary finite repeat
  of one source action equals that thread's actual `Ordered.run`, including
  accumulated events and prior step count. This avoids expanding a multi-thread
  client into a giant definitional evaluation; no heartbeat/recursion limit was
  increased. `reset_well_formed` initializes the same IDs/oracles at the actual
  empty local states. Source execution is independent of the initial byte map;
  scoped memory/observer admission remains an explicit final obligation.
- Borrow boundary: all source steps, including acquire loads, preserve the
  protocol state/buffers/loans exactly. An outstanding loan therefore still
  rejects reclaim after the source step. A successful host acquire can remove
  only a loan whose actual protocol ticket was already complete, reusing
  `Async.await_removed_loan_complete`. Source exit alone and device completion
  alone do not return loans. The original acquire and reclamation checks remain.
- Native Iris baseline: `Iris.OrderedClient` lifts this exact one-action-per-step
  language using exclusive whole-client OwnP. Source WP preserves source/protocol
  invariants and source-borrow guards. The generic contract WP/closed adequacy
  combines any independent `Ordered.Triple` with actual client execution, full
  source completion and the original scoped memory/observer predicates. It does
  not erase qualifiers to the old weak memory model. Error-valued execution is
  not silently accepted as the successful-result postcondition. Arbitrary
  independent Iris frames are retained, without claiming per-byte ownership.
- Message client: the actual nine producer and twelve consumer instructions,
  followed by real device completion, host acquire and reclaim, form a complete
  native execution. The client theorem holds for every launch satisfying the
  original initialized `Pre`, arbitrary initial other bytes and arbitrary protocol
  scalar value. Its final source has the independently proved DATA/FLAG/OUT and
  observed frame, all source/protocol invariants, and the real returned/reclaimed
  modeled buffer. The protocol scalar is not identified with any PTX byte value.
- Semantic negative evidence: actual generated-source acquire tags are retained
  while the loan remains pending; device completion is rejected at the acquire.
  A complete consumer cannot hide a producer whose return instruction is still
  pending, and that producer prefix is an actual successful source run. Reclaim
  fails after acquire and again after all source exits. Completing the device
  without a host acquire still rejects reclaim; acquiring the event before the
  device completes rejects. Closed native Iris negative-adequacy theorems rule
  out successful results for incomplete-source completion and the missing-host-
  acquire script. Fifty-three exact audit entries and registered capability roots
  cover the production, client and negative proofs. No auxiliary assumption,
  source-code change, numerical weakening or strict diagnostic relaxation occurs.
- Scope and reuse: this is an exclusive engineering baseline that reuses actual
  source execution, source reconstruction, scoped global contracts, the existing
  completion/loan rules and the generic native OwnP language. It is not a new
  inference optimization, performance experiment or ownership-method novelty.
  Buffer/byte-region reservation coverage, fractional ordered byte ownership,
  source-matched per-command frontiers for overlapping kernels and physical
  runtime/value/compiler interpretation remain open. The conservative all-source
  completion gate is not a claim to preserve an asynchronous optimization's
  speedup. General ordered/shuffle/async/tensor instruction composition and exact
  paper instruction parity also remain open; the original goal is not narrowed.
- Targeted validation: all four new production/test modules and the complete
  exact audit module build with Lean 4.35.0. TOML parsing and whitespace checks
  pass. Full one-command prototype acceptance is running; final evidence follows.
  The previous goal turn was progress (universal initialized message VC); this
  turn is progress (actual joint stepping, invariant preservation, closed native
  client adequacy and semantic completion/borrow rejection evidence).
- Full acceptance checkpoint: `scripts/check_prototype.sh` exited 0, report start
  2026-11-07T07:38:40.088075+00:00, verdict `prototype-passed-with-gaps`, and current
  source fingerprint over 1,037 files. The unchanged strict gate passes 3,865 Lean
  jobs, 8,535 audited declarations, 8,470 environment-resolved public proof names
  and all 703 false assertions. Fifty-five Rust tests, Clippy, six rejection-
  harness tests, six inventory tests, 18 real Lean audit tests and all 73 positive/
  unknown-qualifier/generated-typing probes pass. All 53 new proof roots use only
  foundation axioms; there are zero registered production auxiliary assumptions.
  The seven original case groups' registered VCs remain strict-proof. All 37 PTX
  fixtures assembled at 2026-11-07T07:40:56.155835+00:00. Fresh finite GPU evidence
  at 2026-11-07T07:41:09.701728+00:00 passes 47 cases, comprising 46 exact-byte
  comparisons and one completion-only check, with all 20 source hashes current.
  Immutable Hopper control SHA256 remains
  f6ffe7057630c38610a2b8ed4d51992d234dd17d5ba889453065d3838524d9d4.
- Interim goal accounting: 1,001,759 tokens at the latest goal-tool checkpoint,
  up from the last published 875,297; tool accounting rather than final billing.

### Prototype delivery audit against the active goal

- Acceptance scope: this audit checks the requested reproducible PTX-to-Lean
  prototype, with explicit unsupported features and trust boundaries. It does
  not convert the existing `partial` implementation-coverage labels into full
  paper/ISA/physical verification. All seven originally named case groups and
  twelve capability groups remain present in `prototype.toml`, `coverage.toml`
  and the fresh source-hashed report; the regression that rejects dropping an
  original group passes. The registered mathematical statements and their exact
  proof dependencies are available in `docs/prototype-evidence.json`.
- Translation/fixed semantics/independent contracts: current Rust typed AST and
  parser emit Lean program DATA. `check_generated` retranslates every registered
  fixture and compares exact generated bytes; acceptance then elaborates checked
  programs and all authored proof modules. Kernel contracts reference generated
  data and independently written mathematical specifications. The actual current
  correctness statements were inspected in CopyEventOutput, SharedEventOutput,
  ScalarMatmulOutput, AtomicDispatchOutput, ScalarAttentionOutput, MoePipeline,
  AmpereTiledCorrect and HopperDoubleBufferFullValues. They are theorems, with
  explicit operational/memory/observer premises and model restrictions, rather
  than propositions accepted by the translator. Compilation/parser/runtime
  conformance remains an explicit external boundary.
- Required semantic families: checked claim roots and production sources cover
  typed launch geometry and enumeration, multi-CTA byte/event memory, actual
  source execution, scoped release/acquire and generic-proxy weak constraints,
  the supported atomic add and four shuffle modes, Ampere copy/group/MMA,
  Hopper TMA/mbarrier/WGMMA and sequential stream composition. Inventory probes
  establish accepted forms/operands and generated typing only; per-family
  semantic theorems and negative tests are separate. Unsupported forms and
  combinations fail closed. Each capability retains its implementation gaps
  in the report instead of inheriting the strict-proof status of a sample root.
- Seven case obligations: Copy/SharedSwap have output/frame theorems and separate
  full legal witnesses; scalar matmul and scalar attention quantify over their
  configured represented matrices and dimensions; atomic dispatch handles both
  admitted ticket orders for its declared two-CTA case; three-kernel MoE composes
  route/experts/combine and constructs a complete pipeline; Ampere tiled matmul
  has correctness and independent CheckedNonvacuous results including zero K
  and inactive outputs. Their current Pre/Post and witness statements were
  inspected, not inferred from a green metadata label. Hopper provides the
  declared fixed-geometry, bounded-K symbolic-byte source/value/protocol family,
  successful full-cut output correctness, full preparation/drain/acquire/return
  witness and closed native adequacy, including zero K. Its fixed source-family/
  weak-proxy/runtime limits remain in its case scope. Each group retains a
  registered concrete instance and fresh checked type/dependency evidence.
- Semantic/Iris/borrow connection: the byte-value pipeline's closed GenHeap
  adequacy and the Hopper full-value native witness connect actual source values
  to modeled byte authority and completion/loan protocols. The inspected Hopper
  witness explicitly includes returned/live loans, available bytes, independent
  GEMM fragments and actual reclaim/write enablement. The additional ordered
  client now connects exact source stepping, complete launch coverage, explicit
  memory admission and the existing protocol under closed exclusive OwnP
  adequacy. Fractional ordered byte transfer and physical resource interpretation
  are recorded as unsupported extensions, not assumed ownership theorems.
- Controlled auxiliary gaps: the independent prototype entry point, centralized
  named-proposition registry, exact statement/type fingerprints, purpose/review/
  impact/discharge metadata and transitive Lean `collectAxioms` checks are in
  place. Current production assumptions are empty. Eighteen REAL Lean audit
  regressions check conditional classification, exact VC types/impact lists,
  unregistered/anonymous assumptions, direct/renamed/definition/structure VC
  wrappers, False and fixed-program assumptions. Required manual statement
  review and the structural audit's inability to decide arbitrary semantic
  equivalence/consistency are documented. Strict sources cannot import prototype
  assumptions, and the foundation allowlist is unchanged.
- Reproducible tests: the fresh one-command acceptance includes the original
  strict gate, frontend positive/negative probes, generated-file freshness,
  semantic weak-memory/synchronization/lifetime negatives, exact proof audit,
  actual conditional-audit regressions, assembler checks and available-GPU exact
  differential checks. The rejection harness has real regressions ensuring an
  elaboration/parse failure or another false assertion cannot hide a true one.
  The source fingerprint was checked again after completion. CPU-only mode
  explicitly reports missing GPU evidence rather than recycling hardware results.
- Paper/numerical/hardware boundaries: `instructions.toml` records every accepted
  local spelling, operand probe, source, regression, limits and unconfirmed paper
  mapping. The report preserves the paper's 81-form group counts and the missing
  enumerated opcode/qualifier artifact as an explicit correspondence gap. The
  local 73/72 counts are not subtracted from 81 to invent missing forms. Exact
  paper parity is not established. Real-valued formal arithmetic, finite exact
  GPU bytes, IEEE/logits/token equivalence and physical runtime/progress remain
  distinct claims. No float tolerance or numerical target was weakened. Hopper
  hardware execution is unavailable on the checked sm_89 device and is reported
  separately from its successful assembly and model proofs.
- Delivery verdict: the prototype's requested audit/acceptance machinery, seven
  scoped case groups and twelve semantic capability groups have reproducible,
  current results; temporary assumptions and unsupported boundaries are visible.
  This satisfies the goal's PROTOTYPE ACCEPTANCE completion criterion with the
  declared gaps. It does not assert complete formal verification or complete
  paper coverage. Future coverage/physical/fractional extensions remain recorded
  work rather than silently changing the delivered theorem statements or this
  prototype verdict. No commit, deployment or unrelated C-engine edit is made.
- Goal state: marked `complete` after this requirement-by-requirement prototype
  delivery audit. The goal tool returned final cumulative usage of 1,035,018
  tokens and 12,428 seconds (3 h 27 min 8 s). This is tool accounting, not a
  billing statement. The completion claim is prototype acceptance with the
  published model scopes/unsupported boundaries, not full formal or paper parity.
