# Implementation notes and milestones

This preserves the detailed development notes formerly kept in the README.
Entries include earlier milestones and limitations; use the [current README](../README.md),
[coverage inventory](../coverage.toml) and [latest acceptance report](prototype-evidence.json)
for the delivered prototype status. The chronological research and validation record
is in [coverage.md](coverage.md).

---

# PTX Verify

Translate PTX into Lean program data and verify kernels with separate Lean contracts.

## Prototype acceptance

The independent prototype entry point preserves the strict checker:

```sh
bash scripts/check_prototype.sh
# CPU-only hosts: explicitly record hardware checks as not run.
bash scripts/check_prototype.sh --gpu off
```

`LEAN_TOOLCHAIN_DIR` and `PTXAS` work as for the strict gate below. By default
the command runs the unchanged strict gate, audit-tool regression tests, the
prototype build, actual Lean dependency/type audits, and fresh finite GPU checks.
It writes `docs/prototype-evidence.json` and adjacent logs/GPU evidence. Failures
write a failed report and return nonzero. `--gpu off` never claims new hardware
evidence. Source fingerprints before/after acceptance detect a changing worktree.

`prototype.toml` retains all seven original acceptance groups and twelve
capability groups. Cases list exact correctness, non-vacuity and instance
theorems. Capabilities list checked claims alongside the separate implementation
gaps from `coverage.toml`. The initial assumption registry is empty: permission
to leave auxiliary lemmas open does not weaken already proved facts. Statuses
are `strict-proof`, `conditional-proof`, or explicitly `unsupported`, within
the printed theorem statements and model scopes. Existing partial coverage and
ISA/compiler/runtime/allocation/IEEE boundaries remain visible. Success means
prototype acceptance with declared gaps, not complete formal verification.

`instructions.toml` records each accepted opcode spelling, canonical alias,
operand probe, fixed profile, semantics source, regression and limitations.
Acceptance checks every entry against the parser dispatch, runs actual positive
translations and unknown-qualifier rejections, and elaborates all generated
checked programs with Lean. These checks establish frontend acceptance and
generated typing only. The report records 73 spellings / 72 canonical local
forms; this count is not comparable to the paper's 81-form convention. Each
local form's paper correspondence remains explicitly unconfirmed until an
enumerated opcode/qualifier artifact is available. Neither a group count nor
the difference between counts is treated as an implemented or missing form.

Temporary gaps must be named proposition axioms in
`lean/PtxPrototype/Assumptions.lean`, under `PtxPrototype.Assumptions`. Strict
`Ptx` sources cannot import this library. Alternative proofs belong in
`PtxPrototype` modules imported by `lean/PtxPrototype.lean`. Use the manifest's
`overrides` map from each original reference theorem to its alternative proof;
Lean checks that their VC types match. Top-level VCs must remain theorems.

After declaring an auxiliary statement, obtain its checked registration data:

```sh
python3 scripts/check_prototype.py --describe-assumption PtxPrototype.Assumptions.example
```

Replace the empty `assumptions = []` with `[[assumptions]]` entries before
`[capability_claims]`. Each entry needs `name`, `role`, `statement`, `type_sha256`,
`purpose`, `review`, `affected_vcs`, and `discharge_task`. Roles cover arithmetic,
indexing, collections, encoding and local semantic interfaces. Copy the exact
checked statement/fingerprint. Impact lists use original reference VC names and
must match actual transitive dependencies, including capability claims. An
unused registered assumption has an empty impact list. The description command
supplies metadata only, not an acceptance verdict.

Anonymous `sorry`/`admit`, unregistered extra axioms, changed statements, stale
impact lists, and direct or definition/structure wrappers around protected VCs
are rejected. Auxiliary types cannot assume fixed generated programs or the
registered correctness/safety/non-vacuity obligations. These are structural
guards: arbitrary semantic equivalence and axiom consistency are not decided
automatically. The required `review` must explain why each statement is a local
auxiliary lemma rather than a disguised VC. Conditional results stay conditional
until assumptions are discharged; GPU tests do not discharge them. Prototype
configuration never expands the strict axiom allowlist.

Shuffle extension: all four fixed `shfl.sync.*.b32` modes have checked program
data and source execution, separate participation/source/value/predicate rules,
and a control graph that rejects cyclic exit exemptions. The generated two-lane
register exchange derives definedness and control admission for every completed
source-valid candidate, with arbitrary oracles and trace order. Shuffle agreement
implies the final-register specification; admitted observations preserve the
global-memory frame. A separate complete source/control/memory/observation
witness rules out vacuity.
Four exported probes provide finite GPU evidence and bounded single-CTA output-array
contracts. Composition with async/tensor instructions remains open. Unsupported
combinations fail closed. Shuffle rendezvous adds no memory fence.

All four exported probes now share an exact generated-code connection and a
24-step source proof, including both predicate paths and both integer-byte
stores. Arbitrary completed source traces reconstruct those events. Checked
shuffle definedness/agreement imply the independent selected-lane word and flag
at the actual stores. An observer frame contract preserves bytes outside the
computed wrapped output spans for aligned word outputs. Static finite launch
closure now derives source safety, including named active partial warps. Complete
collective source candidates and single-CTA bounded-layout memory/observer
witnesses are joined. `ShuffleProbeOutput` now proves every output word and flag
for all admitted completed executions of all four modes, with independent
mathematical array addresses and selected-lane values. Explicit domain coverage
prevents an observer from omitting output bytes. Guard bytes outside the array
retain their arbitrary initial values. Safety, correctness and complete legal
execution existence are separately proved and joined. Full and active partial
warps are covered under `KernelPre`; the final-array layout currently requires
one CTA, aligned output and non-wrapping bounded extents. Source safety alone
also supports multiple CTAs; it does not imply distinct final output writers.

Current Hopper milestone: the bounded positive-K double-buffer data family has
a constructed complete byte-value source script from its initial ten-region
pool, followed by checked source-matched device drain and final acquire in one
value state. Correct final exact-real GEMM matrix fragments, available cells,
all ten returned modeled loans and closed native GenHeap adequacy coexist.
Native public preparation now starts in the initial no-loan protocol and joins
that same byte-value execution. Exact queue sealing gates source/device actions
and prevents further preparation after execution starts. Physical value/protocol/
runtime correspondence remains open. Full-source
closed adequacy uses the existing whole-map helper; footprint-local cycle rules
are checked separately. All seven required cases remain partial and exact paper
81-form parity remains unconfirmed. See the latest research record in
[coverage and evidence](coverage.md).

The native client now also covers zero K with only output/barrier reservations.
`HopperDoubleBufferFullValues` provides one contract for every K up to 2^28:
universal successful-run matrix correctness and a constructed complete native
client from the initial no-loan protocol. Zero K uses two modeled regions and
positive K uses ten. This does not close physical runtime/compiler or broader
instruction coverage; general shuffle/async/tensor composition remains open.

## Scoped ordered memory (partial)

The frontend retains fixed `ld.{relaxed,acquire}.{cta,gpu,sys}.global.u32`
and `st.{relaxed,release}.{cta,gpu,sys}.global.u32` forms in `Ordered.Instr`.
The ordered/scalar interpreter delegates only the local register/control
computation and preserves each source slot's order/scope on emitted events.
Its checked projection to scalar traces is a local correspondence, not a
memory-consistency erasure certificate. Ordinary scalar float operations and
relaxed u32 atomics keep their prior local meanings. Mixing this layer with
shuffle, asynchronous copy or tensor instructions fails closed.

`Ordered.Memory` defines scope-aware morally-strong accesses, observation order,
direct release/acquire synchronization, causality, race/taint eligibility,
coherence and atomicity predicates. The generic message-publication lemma
requires actual observation, scope inclusion, source program order, no-race
eligibility and memory consistency. A release qualifier alone is not a fence.
System scope currently ranges over one device's launched threads; host and
multi-device communication, fences and extended release/acquire patterns remain
unsupported. Full ISA correspondence is not proved.

`release_acquire_message.ptx` has typed generated data and checked real producer,
consumer and polling-retry source traces, including full launch coverage and
complete local exits. Scope and oracle-type counterexamples are checked.
The same complete source candidate now has a constructed ordered-memory and
synchronized-observer witness for every initial byte map at the fixed two-thread
geometry and bindings. Its DATA/FLAG/OUT words and unwritten frame satisfy an
independent postcondition. Stale payload and observer initialization sources are
formally rejected. `Ordered.initial_co_conditions` and the ordered observer
rules are reusable; they do not replace scoped races with weak races. Source
reconstruction covers arbitrary finite polling prefixes: completed
consumers emit zero-flag acquires, one nonzero acquire, then the actual payload
read/output store. Generic chunk decomposition proves this without a polling
bound or termination assumption. Scoped read rules derive observation from a
nonzero represented-u32 flag with zero initialization and explicit eligibility;
they do not assume a fixed reads-from map. `ReleaseAcquireMessageUniversal.correct`
now connects the actual source layout, unique byte writers, flag synchronization,
payload eligibility and final observation into a universal output/frame VC.
Its `Pre` fixes geometry/bindings and requires FLAG to represent zero initially;
all oracles, trace orders, finite polling counts, RF/coherence choices and
admitted observers remain arbitrary. DATA=42, FLAG=1, OUT=42 and preservation
of unwritten domain bytes follow. `initialized_nonvacuous` separately proves a
complete legal execution exists under the same precondition. A source-complete
wrong-payload execution in reversed trace order is rejected for every RF/coherence
choice. These proofs add no auxiliary assumption. Termination/fairness, fractional
ordered byte ownership and physical correspondence remain open. Finite exact-byte GPU
execution is reported separately.

`Ordered.Client` now interleaves the actual one-instruction `Ordered.step` with
the existing `Async.step`, retaining source events and both source/protocol
invariants. Advancing a modeled device completion requires all tracked source
threads to exit; source well-formedness proves the launch has no omitted threads.
A PTX acquire keeps protocol clocks and loans unchanged. Source exit alone and
device completion alone do not return loans: the existing host acquire is still
required. Native Iris `OwnP` rules and closed adequacy use this same joint
language. `ReleaseAcquireMessageClient.native_client_adequate` combines actual
source execution, explicit scoped memory/observer admission, output/frame
correctness and the real completion/acquire/reclaim script for every supported
initialized launch and arbitrary protocol scalar value. Error executions cannot
establish its successful-result postcondition. This is an exclusive whole-client
baseline. Protocol scalars are not PTX bytes; byte/region reservation coverage,
fractional transfer, per-command completion frontiers for overlapping kernels
and physical runtime correspondence remain open. The global completion gate
is not a performance result for asynchronous execution.

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

Run finite hardware checks on an available CUDA GPU, separately or after the
verification gate:

```sh
bash scripts/check_gpu.sh --report docs/gpu-evidence.json
PTX_VERIFY_GPU=1 bash scripts/check.sh
```

The standard-library Python runner uses the CUDA driver API and JITs the actual
PTX fixtures. It compares output bytes exactly, without float tolerances, against
integer or exact-rational references on selected inputs. A whole-run watchdog
records failures. The loop fixture checks completion only; publication exports
only its producer write, so its unused consumer load may be optimized away.
The launcher can use this workspace's existing matching driver libraries in its
child environment; it does not change system drivers. Current reports are
[GPU execution](gpu-evidence.json) on an RTX 4060 Laptop (sm_89) and
[assembly](assembly-evidence.json) with ptxas 12.8.93. These finite checks do
not prove universal IEEE/approximation behavior, Hopper hardware execution or
performance. When PTXAS is supplied, the verification gate updates the assembly
report only after all current fixtures assemble, recording each actual target
and source hash; this is separate from the GPU execution report.

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
lake build Ptx.Kernels.StreamPipeline
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

Input uses 64-bit addresses. PTX 7.0 supports `sm_70` for the prior baseline
and `sm_80` for explicit Ampere asynchronous-copy forms; PTX 8.0 with `sm_90a`
selects the initial Hopper backend described below. The one-CTA integer verification
baseline includes scalar `u32` global/shared loads and stores, `u32/u64` arithmetic,
branches, loops and full-CTA `bar.sync`. Fixed `shr.u32` and `shr.u64` forms
use unsigned values and a u32 shift count; counts at or beyond the value width
produce zero. Signed and other shift forms remain unsupported. The frontend also translates thirteen fixed
f32 forms to the exact-real scalar model: `mov.f32`, `add.rn.f32`, `sub.rn.f32`,
`mul.rn.f32`, `div.rn.f32`, `max.f32`, `ex2.approx.f32`, `fma.rn.f32`,
`ld.global.f32`, `ld.shared.f32`, `st.global.f32`, `st.shared.f32`, `setp.gt.f32`.
The ordered comparison writes a `.pred` register; NaNs and IEEE behavior remain
outside the finite exact-real semantics.
Float literals use exact finite `0fXXXXXXXX`/`0FXXXXXXXX` notation. Native `.f32`
and compatible `.b32` registers are retained. Other rounding/ftz/sat modifiers,
decimal/nonfinite literals, f16/f64 frontend forms and predicated float operations
remain rejected. The float-literal/shared-memory fixture has an all-candidate
memory/observer contract and a separate complete-execution witness; FMA remains
at local trace proofs. Scalar matmul has a universal model-relative contract; its
separate complete consistent execution/observation witness is also proved.

`examples/scalar_flash_attention.ptx` adds a 76-instruction scalar online attention
baseline with masked 2-D output indices, nested runtime loops, first-score
initialization, rescaling and normalization. `Scalar/OnlineSoftmax.lean` proves
the exact-real prefix invariant and equivalence to the independent natural-exp
attention specification. Its base-2 scale is related by `alpha = log(2)*scale`;
no rounded `log2(e)` literal is idealized. `ScalarAttentionUpdate.lean` proves the
actual initialization, nine-instruction update and normalization/store/return
blocks, deriving a positive divisor from the invariant. `Tests/OnlineSoftmax.lean`
checks rescaling with a new maximum, zero-divisor rejection, and full-source
empty-key and both edge-mask paths. `ScalarAttentionDot.lean` proves the actual
inner dot loop for arbitrary bounded D, query offsets, input functions and
unrelated register bindings: `9*D+2` steps to PC 52 and `9*D+3` through the scale
multiply. It preserves outer-loop registers and retains wrapping of unused
one-past pointers. `Scalar/RegisterFrame.lean` supplies register-frame rules
including cross-bank invalidation, reused by both dot and softmax blocks.
`ex2` is abstracted by `exp(log(2)*x)`, not the hardware approximation. Division
by zero faults as outside this finite-real fragment; it is not PTX's IEEE result.
`ScalarAttentionOuter/OuterUpdate.lean` now compose the actual nested loops
from PC 37 through store/return, preserving first-item initialization without
requiring preinitialized softmax registers. For N>0 the derived suffix count is
`N*(9*D+26)-2`; output matches the independent natural-exp attention spec under
explicit local reply hypotheses. A concrete PC=0 source execution takes 105
steps for N=2/D=1, changes the maximum and outputs 8.
`ScalarAttentionInput/Init/Guards/Address/Entry/Thread.lean` now connect general
PC=0 runtime parameters, 2-D indexing, both masks, output/loop addresses and scale
load to that invariant. A constructed typed oracle supplies arbitrary real
Q/K/V data; active N>0 source runs take `35+N*(9*D+26)` steps. Row/column masks
take 21/23 steps; N=0 takes 32, reads no inputs/scale and requires only the output
start bound. The shared `Scalar/Indexing.lean` bounds are reused by matmul.
Tests cover non-unit CTAs, extra parameters, arbitrary real matrices, and empty
keys whose unused input pointers cannot satisfy the nonempty read bounds.
`ScalarAttentionDotTrace/Trace/SourceTrace.lean` now reconstruct EVERY successful
completed PC=0 execution, including nonempty runs, without selecting its oracle
or count. Actual load success forces exact f32 reply tags for scale/Q/K/V. The
reconstructed result is online attention over those candidate-local replies;
repeated Q answers remain independent until memory reasoning identifies inputs.
A positive regression preserves a locally complete nonuniform-Q trace (output 8
versus the uniform-input spec's 7), while integer scale/f64 final-V replies cannot
complete.
`ScalarAttentionConfig/ReadEvents/Events/Memory/Inputs/Output.lean` now derive
complete four-byte bounds/alignment, actual event regions, unique output writers
and race freedom from launch coverage and region layout. Immutable-load rules
force every actual scale/Q/K/V read to its represented initial value, including
agreement of repeated Q reads. The all-candidate contract proves the independent
natural-exp attention output and preserves observed bytes outside O.
`ScalarAttentionCandidate/Witness.lean` separately enumerate every valid thread,
construct actual complete PC=0 runs, and establish initial reads-from/coherence
and permitted observations for every admissible launch. Read-only inputs may
alias if their initial representations agree. N=0 imposes no unused-read layout
or initialization conditions: tests admit Q=K=V=O and an unaligned scale at
2^64-1, with a complete legal global witness writing zero.
Multi-CTA 3x3 output tests cover non-unit blocks, both masks, correct output/frame,
and rejection of repeated-Q disagreement, wrong scale, output and frame.
Assembly and finite exact-byte GPU comparisons cover the same 3x3 case plus
changed maxima, equal scores and empty keys. Physical allocation/UB, full PTX/
observer correspondence, general IEEE/approximation behavior and arbitrary-input
GPU bit equality remain separate duties.

The first scoped atomic form, `atom.global.relaxed.gpu.add.u32`, now translates
to typed scalar data and one scope-carrying RMW event, with equal-size before/after
payloads. Its old value comes from an unconstrained integer oracle; the u32 result
and increment wrap exactly. `Event/AtomicRules.lean` derives self-read rejection
and exclusion of two mutually scoped RMWs both reading initialization. The common
memory predicates include scoped moral strength, RMW observation chains and RMW
atomicity. A separate completed single-RMW consistency regression prevents vacuity.
The actual 15-instruction `atomic_dispatch.ptx` now has arbitrary-ticket full-source
completion and reconstruction of EVERY completed run, retaining both job branches
and the no-job branch. Source counts are 11 for normalized ticket 1 and 10 otherwise.
`AtomicDispatchConfig/Events/Layout/Tickets.lean` derive exact event shapes, complete
four-byte bounds/alignment, mixed-size exclusion and counter eligibility from runtime
layout and actual source provenance. Bytewise SC/coherence/RMW reasoning forces
the two tickets to be {0,1} in either order. No ticket assignment, uniform source or
global no-race hypothesis is in the precondition. Complete local candidates exist
for arbitrary replies; ALL equal assignments are rejected by memory consistency.
`AtomicDispatchOutput.correct` now proves counter=2, x=1, y=2 and preservation
of observed bytes outside the three cells for EVERY complete consistent candidate
and permitted observer. It derives job ownership and bytewise latest counter
modification. `Event/RankedWitness` and `RankedObservation` provide checked
construction rules for repeated writes/RMWs and observations selected from actual
emitted writes. `AtomicDispatchWitness.lean` independently constructs complete
consistent source executions and permitted observations for EVERY admissible launch
and for either CTA receiving ticket 0. The same race-exclusion and ranked witness
rules are reused without assuming consistency or the final postcondition. Concrete
regressions admit both CTA orders, observe 2/1/2 and preserve the nonzero frame.
Physical allocation/UB and full PTX/observer correspondence remain separate.
A finite two-CTA GPU comparison passes. Local reply 17 remains possible but
cannot satisfy consistency in the
zero-initialized two-CTA case.
Other atomic forms, acquire/release and shuffle are not yet supported.

Scalar programs additionally accept `mov.u32` reads of `%tid.{y,z}`,
`%ctaid.{x,y,z}` and `%ntid.{x,y,z}`. Legacy `%tid.x` retains its existing integer
data. `Scalar.Context` carries CTA dimensions, and launch-wide scalar provenance
supplies the actual launch block rather than a load oracle or an implicit unit
block. Other special registers and special-register arithmetic operands remain
unsupported. Physical launch limits are separate proof obligations.

## Event-model extension

The frontend parses into structured Rust nodes retaining integer widths and
ALL register declarations, then serializes the original Lean program data plus
a `CheckedProgram` whose type proof Lean checks with `decide`. `ISA/Typing.lean`
checks register classes/widths, parameters, addresses, binary forms, branch bounds
and declaration uniqueness. The typed instruction list erases to the identical
raw program; `ISA/TypedSemantics.lean` connects both interpreters and proves that
successful event executions preserve bounded register values from typed initial
register files. Typing does not initialize registers, establish memory safety or
prove termination; the regression suite includes typed counterexamples to each
such conflation. This is checked emitted data, not a verified Rust parser.
The original operational verifier remains the regression baseline. The new
`Ptx.ISA` and `Ptx.Event` modules share its program data and add byte payloads,
launch identities and deterministic oracle-driven trace generation. They do not
yet establish full PTX-model correspondence or allocation safety. `Event/Consistency.lean`
adds ordinary weak generic-memory predicates, bytewise reads-from and race taint;
tests construct read-only execution witnesses and reject inconsistent oracles and
circular barrier-exit exemptions. The float frontend uses its separate scalar
instruction data while preserving the original integer-only data format.

Hardware testing exposed an additional model boundary: `bar.sync` has aligned
instruction requirements that resource-ID/generation matching alone does not
express. Publication now joins both branches at one static barrier instruction.
`Event/SourceRun/Origins.lean` now record PCs from actual integer-interpreter
steps and prove exact event erasure. `Event/Checked.lean` combines provenance,
graph-memory conditions and matching source PCs for every same-generation
arrival/return. Source PCs are computed from actual runs, not supplied by an
oracle or caller annotation. `Scalar/Origins/Checked.lean` applies the same
mechanism to the actual mixed interpreter, retaining the full float bank and
using the actual launch block. Barrier events are proved to originate from the
original `.integer (.barrier ...)` instruction at that PC; floating operations,
special-register reads and atomic RMWs cannot manufacture them.
`Kernels/SourceChecked.lean` supplies checked
contracts AND independent checked nonvacuity for Copy, SharedSwap and publication
without adding source-alignment premises to their callers.
`Kernels/ScalarSourceChecked.lean` supplies the corresponding checked contracts
and independent witnesses for scalar matmul, atomic dispatch, attention and the
float-literal/shared helper, preserving their original preconditions and output/
frame specifications. Source-aware instances retain matrix output/frame, both
atomic ticket orders and empty-key attention with unused invalid scale memory.
The archived `examples/divergent_barrier.ptx` completes locally with the same
abstract events as positive publication, but its PCs 9/5 fail checked admission.
A separate two-site/two-generation program has a complete checked memory and
observation witness: one static site per resource is only a sufficient rule,
not a restriction imposed on all programs. The original graph-only contract API
remains available. A typed mixed semantic regression reads `%ntid.x`, branches
using the actual non-unit block, executes float instructions and two barrier
generations at different PCs, and has a complete checked memory/observation
witness. Substituting a unit block invalidates that source run. The scalar path
also rejects the archived divergent source. These are Lean semantic regressions,
not additional PTX/GPU fixtures. Broader SIMT/ISA legality and full PTX
correspondence remain separate; see [the model boundary](memory-model.md).

The staged real-float backend is in `Scalar/`: exact-real arithmetic and symbolic
f16/f32/f64 storage fragments, typed float load oracles and mixed integer/float
register updates. `Scalar.run_integer` proves that its integer-only executions
agree with the existing interpreter, including errors and emitted events. A local
load/FMA/store trace is proved for arbitrary real inputs. The actual translated
`float_fma.ptx` and `float_literals.ptx` now have type certificates and parameterized
local execution proofs, including flexible parameter bindings and independent
shared-load answers. `Scalar/Execution.lean` checks launch-wide scalar provenance,
including the final float bank, and uses the same polymorphic memory/observer
definitions as the integer model. `FloatLiteralsUniversal.lean` proves that EVERY
complete candidate of the translated literal/shared-memory fixture outputs 9,
with a separate legal execution/observation witness for each permitted pointer,
parameter environment and initial symbolic memory. Returning 17 at the shared
load is locally possible but rejected by memory consistency for every reads-from
and coherence witness. This helper does not replace scalar matmul or establish
allocation/UB freedom, full PTX correspondence or CUDA synchronization correctness.
This backend is not IEEE rounding verification or GPU bit-equality evidence.

`examples/scalar_matmul.ptx` is the first required matrix fixture: row-major f32
inputs/output, a two-dimensional grid and CTA shape, masked edge threads and a
runtime inner-dimension FMA loop including K=0. Its 43 generated instructions have
a Lean type certificate. `Scalar/Geometry.lean` proves mathematical index coverage
and uniqueness; `Scalar/Memory.lean` provides immutable real-load and observed
real-write rules, reused by the existing float-literal contract. The independent
matrix specification is in `ScalarMatmulSpec.lean`. Concrete K=0 and K=2 local
traces are checked in `Tests/ScalarMatmul.lean`. `ScalarMatmulLoop.lean` now proves
the actual inner loop for every u32-bounded K from an explicit loop invariant,
with arbitrary unrelated bindings and real matrix data. The derived suffix has
9*K+4 steps and includes the final store/return; K=0 reads nothing. Pointer updates
retain their 64-bit wrap semantics, including an unused one-past pointer wrapping.
`ScalarMatmulLoopTrace.lean` reconstructs every successful complete suffix without
preselecting its oracle or instruction count, proving that each load reply is f32.
`ScalarMatmulInput/Init/Guards/Address/Thread.lean` now connect the actual PC=0
parameter reads, 2-D index instructions, both bounds guards and modular address
initialization to that invariant for arbitrary runtime dimensions and threads
satisfying explicit width/address bounds. Active executions take 36+9*K steps;
masked row/column threads take 19/21 steps and emit no memory events. Arbitrary
completed source runs have one of those three trace shapes. Tests cover arbitrary
K/real data/extra parameters and reject coordinate-product overflow, including an
actual source trace whose mathematical column 2^32 wraps to 0.
`ScalarMatmulConfig/Events/Memory/Inputs/Output.lean` now derive full four-byte
footprint bounds/alignment and race freedom from launch coverage and matrix-region
bounds/separation. Every complete well-formed candidate allowed by the current
memory/observer projection reads the initial matrices and produces their exact-real
product, preserving observed bytes outside C. Read-only A/B aliasing and empty K=0
input regions are allowed. The contract does not select load replies or execution
counts. `ScalarMatmulCandidate/Witness.lean` separately enumerate all valid threads,
construct actual completed source runs and prove initial reads-from/coherence and
permitted observation witnesses for each admissible launch. Regressions include
K=0 with A=B=C and nonzero initial output bytes. Assembly and finite exact-byte
GPU comparisons pass for K>0 and K=0/aliasing. Physical allocation/UB and full PTX
correspondence remain pending.

The `barrier_publish.ptx` fixture adds a checked two-thread publication witness
for arbitrary scalar inputs. A universal model-relative contract now covers every
complete candidate, with arbitrary oracles, trace lengths and trace-list order,
and has a separate non-vacuity proof. Observer
conditions are an explicit ordinary-memory projection, with full augmented-graph
correspondence and allocation coverage remaining separate obligations.

`CopyEvent.lean` reconstructs Copy's complete traces and proves its event accesses
race-free under the original arbitrary-length configuration/layout.
`CopyEventOutput.lean` proves exact destination bytes and unchanged allocated
frame bytes for every permitted complete candidate and observation.
`CopyEventWitness.lean` constructs a consistent complete execution and observation
for each positive launch satisfying that contract. The byte/cell representation
preserves arbitrary initial bytes of uninitialized frame cells.
`CopyCompletion.lean` constructs a completed operational execution for every
original configuration; `CopyEventRefinement.lean` establishes event-to-operational
output inclusion on every allocated global byte. Zero threads take an explicit
host skip/no-launch path with unchanged memory.

`SharedEvent.lean` reconstructs the original two-thread SharedSwap traces with
independent source/shared-load oracles. `SharedEventMemory.lean` proves barrier
publication and race freedom. `SharedEventOutput.lean` gives a universal exchanged-
byte and allocated-global-frame contract; `SharedEventWitness.lean` constructs
consistent complete executions and observations for every original configuration.
`SharedCompletion.lean` constructs completed operational executions including the
original collective release. `SharedEventRefinement.lean` proves general allocated-
byte output inclusion, using the same `Event/Region.lean` encoding rules as Copy.
Tests also compare arbitrary candidate outputs with the original round-robin run.
Full PTX-model correspondence, allocation/UB duties and GPU execution remain separate.

`Event/Publication.lean` and `Scalar/Stream.lean` now model completed launches on
one ordered stream. A boundary observer must cover every actual global write.
Its observed bytes are published and unobserved bytes retain their initial values;
this normalized map is proved observable on any finite global domain. Each launch
gets its own shared initialization. Stream append/consequence rules prove
all-execution postconditions, and separate rules construct complete pipeline
witnesses from component nonvacuity and proved intermediate preconditions.
`Kernels/StreamEffects.lean` derives publication coverage from actual matmul,
attention and literal/shared writes. `StreamPipeline.lean` composes the generated
literal/shared kernel producing A=9 with generated matmul, proving C=9*B for any
represented real B and preserving a frame byte. The example has an independent
complete checked execution witness; it does not assume A was initialized to 9.
Tests reject a stale successor input, missing write publication, publishing an
unconstrained observer payload and carrying shared state between launches.
The GPU suite queues the same two entries on one default stream with no host
synchronization between them, then compares the intermediate/output/input/guard
arena exactly. This is a composition baseline; the routing/expert/combine MoE
now has typed source, finite GPU tests and the current-model composition proofs
described below.
These rules specify a completed ordinary-memory API
boundary; full runtime, proxy and augmented PTX graph correspondence remain open.

See [coverage and proof boundaries](coverage.md) and the machine-readable
[capability inventory](../coverage.toml) for the implementation sequence, evidence
and outstanding obligations toward the SF Tensor paper's supported scope.


## Three-stage MoE progress

`moe_route.ptx`, `moe_experts.ptx` and `moe_combine.ptx` implement two-expert,
normalized top-1 routing (ties choose expert 0), dense linear experts and unit-
weight gather from separate expert planes. Their typed source lengths are
23/57/41 instructions. `Kernels/MoeSpec.lean` defines an independent specification,
including sparse expert layout uniqueness and bounds. `Scalar/Compare.lean`
proves ordered comparison and register-frame rules; `MoeRouteSelect.lean` proves
both actual route branches, the selection store and return for arbitrary ready
states and read-oracle tails. `MoeRouteThread.lean` proves complete PC=0 active/masked local traces and
reconstructs the exact count, typed replies and events of arbitrary successful
completed route executions under explicit index/address bounds. The route event/output modules now derive these replies from represented
initial gates and prove the universal u32 route result and observed frame.
`MoeRouteWitness.lean` independently constructs complete source/consistency/
observation witnesses. `MoeRouteStream.lean` proves that the actual stage publishes
u32 routes into the successor initial heap and preserves all other heap bytes.

The GPU runner preloads all three modules, queues the three stages on one default
stream, waits once, and compares the entire arena, including inputs, routes,
unselected expert planes and guards. Five cases cover mixed/tie routing,
negative/subnormal gates, K=0, N=0 and M=0 with unused pointer aliases. The current
report now has nineteen exact-byte comparisons and one completion-only check
overall, including the Ampere copy helper; eighteen fixtures pass assembly. This is finite execution evidence. The expert stage now has universal
source/memory/output/frame proofs, independent complete legal witnesses and its
own stream publication contract. Combine source/memory proofs and a full
three-stage current-model MoE composition are now present as described below. This stage
is marked partial in `coverage.toml`; it does not establish arbitrary GPU/IEEE
equivalence, packing/capacity behavior or top-k>1 support.


The route global precondition uses one-dimensional launch ownership, complete
four-byte gate/route bounds and separation of their live regions. Every launched
thread, including masked threads, is enumerated for the existence proof. Empty
routing admits unaligned G=R and uninitialized gates. Regressions include a
locally complete wrong-gate candidate that global consistency rejects, mixed and
tied routing, a preserved nonzero frame, stale successor routing and a published
word missing its last byte. A payload-independent immutable-read/unique-writer
rule is reused by route and existing scalar matmul, preserving their contracts.
The route component is used by the full current-model composition described
below; its success alone does not complete the original goal.


The expert FMA loop now uses `Scalar/FmaLoop.lean` and `FmaLoopTrace.lean`, with
entry PC and prior query count as parameters. An eleven-slot `Fragment` proof
checks the actual guard, branches, two loads, FMA, pointer/index advances, output
store and return; code outside that fragment remains unconstrained. Existing
matmul iteration/finish theorems reuse these rules at PC=32/query=0, while
`MoeExpertsLoop.lean` certifies actual expert PC=46/query=1 and relates its loop
to the independent dense-expert recurrence for arbitrary K. Expert loop register
names were normalized to the common fragment; native source and types remain
mechanically generated, with assembly and GPU reports rerun after that change.

Actual PC=0 tests connect both expert branches to the generic loop at fixed
M=N=3/K=2 with non-unit CTA/block coordinates and arbitrary real matrix data.
A K=0 test permits X=W=H and emits only the route read and zero output store.
Regressions reject a wrong branch target, omitted store certificate, reset query
origin and wrong float-reply types. A changed-prefix counterexample explicitly
shows that a loop certificate alone does not establish full-entry correctness.
The local layout bounds read starts; complete four-byte/alignment, all-dimension
entry/selection and global input/routing/memory proofs are supplied by the
full-entry and global modules described below.
These loop lemmas are reused by the full expert and pipeline proofs below.


`MoeExpertsInput/Init/Guards/Route/Select/Address/Thread.lean` now connect the
expert source from PC=0 for arbitrary admissible dimensions, parameters and
runtime CTA/block/thread indices. Integer route values are normalized to u32;
source reconstruction first derives that query zero was an integer reply.
Every successful complete source execution is classified as row mask (20 steps),
column mask (22), invalid route (27, only the route read), or expert 0/1
(44/50+9*K steps). The valid branches execute actual sparse-plane arithmetic and
establish the common FMA invariant with query origin 1. Read-start and output
bounds are explicit and conditional on live accesses; K=0 needs no X/W read
bounds, and masked launches need no data-address bounds. This proves local
entry/loop correspondence; the global modules below discharge initial-memory,
full-byte/alignment/separation, race and legal global-execution obligations. Regressions
cover arbitrary completed oracles, modulo-normalized routes, invalid routes and
M=0/N=0 with unaligned aliased unused pointers and maximum u32 K.


`MoeExpertsConfig/Events/Memory/Inputs/Output/Candidate/Witness/Stream.lean`
now close the expert stage under the current exact-real/event model. Every actual
R/X/W/H access has an aligned four-byte footprint below 2^64. Immutable inputs
and unique H writers imply race freedom even before route agreement is known.
All four R bytes identify the bounded u32 route; X/W memory agreement then fixes
the actual dot-product replies and independent selected-expert result. The frame
contract preserves every byte outside selected H words, including unselected
expert planes. Complete checked source, consistency and observation witnesses
are constructed independently; completed stream publication covers every write
and retains all nonselected global bytes.

Regressions use 3x3x2 data across 2x2 CTAs and 2x2 threads, routes [0,1,0],
outputs [12,20,12] and nonzero unselected-plane sentinels. A typed wrong-route
candidate completes locally and is rejected globally. K=0 permits X=W=H without
float initialization; M=0 or N=0 permits all bases=1 and maximum u32 K without
input initialization. Stale successor heaps, missing output bytes, live-region
overlap, full-word overflow and a wrong high u32 byte are rejected. The combine and pipeline
modules below now complete the three-stage ordinary-memory mathematical contract. Physical allocation,
full ISA/runtime correspondence and arbitrary IEEE/bit equivalence remain
external obligations; the exact logits/token requirement is unchanged.


`MoeCombineInput/Init/Guards/Route/Select/Address/Body/Thread.lean` certify the
actual gather source, including both expert branches, masks and invalid-route
return. Global `Config/Events/Memory/Inputs/Output/Candidate/Witness/Stream`
modules derive four-byte bounds/alignment, race freedom, u32 route agreement,
selected-H read agreement, Y output and frame preservation. Only selected H
values need initialization. Complete checked consistency/observation witnesses
and stream publication are proved independently. Active branches take 38/41
steps, masks 18/20, and invalid routes 25 after only the R read.

`MoePipeline.lean` now composes route, expert and combine for arbitrary
admissible dimensions and real matrices. Its entry requires represented G/X/W;
R/H/Y start unconstrained. Stage outputs and byte frames establish actual
successor initialization. Final Y satisfies the independent `Moe.Post`, with a
whole-heap frame outside R words, selected H words and Y words. A separate
nonvacuity theorem constructs complete legal stream boundaries in sequence.
Per-stage geometry, parameters, shared initialization and finite observer
domains remain explicit. Live X/W must survive route writes; separation is
conditional on active dimensions, allowing unused aliases in empty cases.

Pipeline regressions poison R/H/Y at entry, prove mixed outputs [12,20,12] and
preserved unselected planes, exercise K=0/X=W=H and N=0 aliases, and prove all
bytes unchanged for M=0 with all pointers=1 and maximum u32 K. Standalone gather
regressions reject locally complete typed-but-wrong R/H replies. These are
current-model exact-real proofs. Physical allocation, full ISA/runtime/proxy
correspondence, arbitrary hardware bit equivalence, Ampere/Hopper support and
the remaining goal obligations still require work; existing finite GPU reports
remain separately identified by source hashes. No speedup is claimed.


## Ampere asynchronous-copy foundation

The frontend now emits `Ampere.Instr` data and checked typing for explicit
non-bulk `cp.async.ca.shared.global` (4/8/16 bytes), `.cg` (16 bytes),
`cp.async.commit_group`, `cp.async.wait_group` (supported constants 0..7) and
`cp.async.wait_all`. Other copy qualifiers/optional operands remain rejected.
Shared declarations support 4/8/16-byte alignment with checked padding/overflow.
Existing scalar/integer programs retain their backend and generated data.

`Ampere/Thread.lean` records a copy's bytes, group and identity without writing a
heap or pretending that commit performs the copy. Normal scalar slots delegate
to the existing interpreter at the same PC. `Rules/Source.lean` prove source
steps preserve the copy ledger and that every copy corresponds to an emitted
source issue, and conversely. `Graph.lean` puts copy reads/writes on separate
nodes outside issuer program order. Its completion edges use the issuing
thread's actual wait frontier; later CTA barriers can propagate that ordering.

Generated-source regressions distinguish committed, recent and uncommitted
groups, show that bar.sync alone gives no copy-write publication path, and
reject malformed payloads. GPU/assembly reports include an actual sixteen-byte
waited copy with exact output/guard comparison. Missing-wait source is translated
and assembled but never executed on GPU. `MemoryGraph` now supplies graph-generic
rf/co, race/taint, observer and unique-writer witness rules. An iff adapter proves
ordinary candidates retain exactly their old memory and observation meaning.
`Ampere/Memory.lean` applies that memory fragment to the actual copy nodes, using
logical copy agents distinct from the issuer. Its conditional waited-copy rule
requires derived eligibility and unique writes. A small independent graph test
constructs complete memory/observer witnesses and shows unordered accesses race.
`Ampere/Origins.lean` now instruments actual pre-step PCs; `Checked.lean` adds
same-PC barrier matching, full-CTA participation/exited-peer checks and acyclic
control order including async base edges. The actual helper discharges its
barrier/ordering obligations. Regressions reject divergent same-generation sites
and circular exited-peer exemptions, and accept different sites in separate
generations. The actual helper now has a parameterized all-candidate byte-copy
and global-frame proof against `CpAsyncCopySpec` on a finite arena. Arbitrary
complete source traces are reconstructed; payload/read values and eligibility
are derived through the augmented memory model. Wrong payload and load-answer
candidates complete locally but fail memory admission for every rf/co.
`CpAsyncCopyWitness` independently constructs complete checked source/rf/co/observer
witnesses from every admissible represented initial map under the same preconditions.
The concrete sample derives copied bytes and preserved guards from that witness.
Full async ISA/storage/runtime correspondence remains required.

The frontend now accepts the fixed
`mma.sync.aligned.m16n8k16.row.col.f32.f16.f16.f32` form and global/shared
`ld.b32` through the Ampere backend. Four A and two B packed registers feed four
f32 accumulators; input capture precedes destination writes, including D/C
aliasing. Register overwrites invalidate stale representations. Checked admission
requires actual source events for all 32 lanes at the same PC/warp/call ordinal
and derives outputs from their fragments. MMA rendezvous constrains control
acyclicity without adding a memory-publication edge. `MmaProtocolRules` connects
matched source inputs to the independent exact-real matrix step.

The generated 25-instruction `mma_probe.ptx` has a checked complete 32-lane
source/warp-arithmetic smoke witness. A separate represented initial map now has
complete checked source/rf/co/observer witnesses, actual output-byte values and
preserved guards. The earlier placeholder input is rejected for every rf/co. It also has
finite full-warp GPU evidence:
128 output floats and four guard floats match an independent rational reference
byte-for-byte on sm_89. This is a layout/execution test with exact small inputs.
Parameterized tiled correctness/nonvacuity and shared-buffer reuse proofs are
established below. Physical ISA/runtime correspondence and the original goal
remain open.


`ampere_tiled_matmul.ptx` now provides an actual 83-instruction implementation:
one warp per 16x8 tile, three 8-byte cooperative async copies per lane, explicit
wait/publication, packed shared loads, MMA accumulation and a post-read barrier
before reusing the same 768-byte shared tile in the K loop. The supported layout
is A row-major f16, B column-major f16 and C row-major f32, with M/N/K multiples
of 16/8/16 and block=(4,8,1). Four finite GPU cases cover multi-CTA three-step
reuse, zero-K unused-input aliasing and extra inactive CTAs as well as one tile.
A separate two-iteration local source trace checks counters, source PCs and old-C
capture. Full parameterized source/memory/observer correctness and independent
legal execution witnesses for the tiled kernel are established below.

`MemoryGraph/RankedWitness` and `RankedObservation` generalize ordinary repeated-
write constructions to the augmented graph with independent async agents. A rank
certifies a particular witness, without restricting allowed executions. Read
values, all causal/order edges, race freedom, from-read bounds and a complete
actual writer inventory remain proof obligations. A model-level write/read/
overwrite test checks the last-writer observer and rejects a stale observer;
it is distinct from a PTX source witness.

`Ampere/TiledLayout` supplies parameterized byte ownership and copy-to-fragment
address equations for that shared tile. These facts now connect to arbitrary
actual source executions through the producer/input/fragment rules below.
Independent complete K-loop memory witnesses are constructed below.

`Kernels/AmpereTiledSpec` now states independent exact-real input/output/frame
conditions, including vacuous unused inputs for zero K or inactive outputs.
`AmpereTiledLoop` composes the actual copy/wait/barrier/load/MMA/advance fragments
for arbitrary K-loop counts, from PC 57 through four stores and return:
21*t+7 steps and 17*t+4 events for t remaining iterations. It preserves prior
history and wrapped pointers. Reply size/tag conditions assume no desired matrix
values and are not added to the kernel precondition. Tests include nonzero prior history,
near-wrap pointers, zero/three iterations and rejection of premature completion.
Independent complete legal tiled witnesses, including dynamic barrier-source
matching and inactive execution, are constructed below. The global frame and
actual final accumulator encodings are also proved below.

`AmpereTiledInit/Addresses/Entry/Geometry/Source` now prove the actual PC-zero
parameter/index/guard/address/zero-accumulator initialization and derive the
loop invariant from the existing Layout and canonical geometry. Active complete
source runs take 64+21*(K/16) slots. The constructor takes a reply certificate;
`AmpereTiledReconstruct` now derives it from every arbitrary completed candidate.
Zero-K
runs emit four zero stores for every oracle; inactive M/N paths return with no
events for every oracle. Tests include unused unaligned A/B/C aliases and
near-limit inactive dimensions/pointers. Source pointer formulas, copy
destinations and packed read events connect to the independent layout rules.
`AmpereTiledBounds` derives all eight copy-source bytes' bounds in active
iterations, retaining wrapping for unused final pointers. These source/address
proofs do not supply memory-value agreement or a legal full-launch witness.

`Ampere/Inversion`, `CopyInversion` and `RawLoads` derive copy lengths and packed
tags from actual success. Raw loads retain both word variants and invalidate old
packed bindings on integer writes; actual later MMA success forces all six
loaded words to be packed. `AmpereTiledReplies` repeats this argument over any
remaining K-loop count. `AmpereTiledTrace` reconstructs the exact final state and
event list for every completed active PC-zero source run, with no new caller
reply/value premise. It derives copy/group/MMA/barrier/query counts and old C
capture. `AmpereTiledEvents` exposes all seventeen per-phase event tags, copy
identities/addresses/bytes, MMA metadata and event indices. Tests reject late
bad copy/A/B replies for every fuel count, including stale packed state, and
accept integer word replies at unused matrix-query positions. Actual candidate
inventories, race freedom, phase/input byte visibility, output ownership/coverage
and the global frame are now derived below. Dynamic barrier-source matching and independent complete legal witnesses are established below.

`AmpereTiledInventory/Graph` now exhaustively derive actual source/candidate
reads, writes and copies, including independent async nodes, and rule out RMWs.
`AmpereTiledPhaseOrder` proves waited publication, peer read protection before
later reuse, and earlier/later copy order from actual events. Shared-copy byte
ownership is unique within one K phase; repeated writers across phases remain
allowed. `AmpereTiledPhaseVisibility` classifies all competing shared writers and
forces the current rf source/value for every admitted rf/co under explicit read
eligibility. `AmpereTiledOutputLayout/GlobalAccesses/Race` now derive global
input/output separation, unique output byte ownership across CTAs, full output
coverage and complete race freedom for arbitrary rf. Zero-K unused inputs retain
their alias/alignment freedom. `AmpereTiledMemory` derives eligibility, forces
global reads to initialization, constrains every actual copy payload byte to
that input byte, and supplies current-phase shared visibility without a caller
eligibility premise. `AmpereTiledObservation/OutputAccesses` prove the global
frame and observation of actual final f32 accumulator encodings for every
output element. The full enumerated source-only constructor proves provenance/
completion; four-CTA tests exercise order and actual bytes.
The inconsistent oracle is proved memory-inadmissible for every rf/co and is not
a legal witness. Full-CTA participation and acyclic actual control are proved
below, with dynamic barrier-source matching and complete legal tiled witnesses also established below.

`AmpereTiledProducer/InputRead/FragmentInputs` now connect every packed shared
read to its actual current-phase copy owner, global source and represented A/B
matrix halves. Actual MMA entries have source-derived lane/A/B/old-C fragments.
`AmpereTiledAccumulation` proves the matrix-product invariant by induction over
all source threads and arbitrary K phases, using the existing mandatory full-warp
MMA arithmetic. `AmpereTiledCorrect.correct` proves the universal checked
output/frame contract under the original Pre, including zero K and inactive
outputs. It adds no reply, eligibility, fragment-value or desired output premise.
A nonuniform represented four-CTA input satisfies Pre and exercises upper-row,
column-major and cross-thread producer mappings. This universal theorem is
separate from independent complete legal source/rf/co/observer existence; the
latter is constructed below, including dynamic barrier matching and inactive
source execution under the identical full Pre. These symbolic-real proofs
are not a GPU IEEE bit-equivalence or performance claim.

`AmpereTiledControl` now proves full-CTA barrier participation and acyclic actual
control order for every complete active source candidate, including independent
copy nodes and MMA rendezvous. It excludes exited-peer shortcuts. Its rank is a
proved certificate, not an added execution premise or a publication edge.
`AmpereTiledWitnessOracle` independently constructs complete source candidates
from the fixed initial bytes and matrix tiles. It does not use the universal
correctness theorem to choose or justify answers. `Ampere/Origins.mma_source_pc`
checks MMA entry/return PCs from actual interpreter steps. `AmpereTiledWitnessMma`
constructs all 32 actual full-warp participants and proves their source PC/lane/
CTA/ordinal metadata and mandatory matrix arithmetic. The nonuniform four-CTA,
three-phase instance checks actual PC 71, packed upper-A/B halves, truthful copy
bytes and final exact-real answer 3534768920. Zero K retains unused input aliases.
These source/control/MMA components now have rf/co/observer witnesses below.
Actual dynamic barrier-site matching and inactive witnesses complete checked
nonvacuity below.

`AmpereTiledWitnessAccesses/Memory/Observation/Components` now construct actual
rf/co and final global observations for every active Pre, including zero K.
All four packed bytes are tied to the represented initial input without using
memory consistency as a premise. The explicit rf selects initialization for
copy reads and the actual current-phase producer for shared reads. Proved base/
control and read-from ranks, race freedom, overlapping-writer rank injectivity
and from-read bounds establish every generic RankedCo memory condition. A finite
inventory covers all actual copy/output writers; its rank-maximal selector gives
an admitted observer independently of a desired output. The nonuniform instance
derives actual shared value 2322, old/current/future coherence, observed result
3534768920 and padding preservation after constructing these witnesses. These
are source/control/MMA/memory/observer components, assembled into the full
checked witness below.

`SourceRun.at_boundary` and `Ampere.source_pc_of_prefix` recover source PCs
from actual interpreter prefixes and the emitting pre-step state.
`AmpereTiledBarrierSources` uses these rules for repeated pre/post barriers:
generation parity matches actual PC 64 or 72 without requiring a unique static
site. `AmpereTiledWitnessInactive` independently constructs both real guard-return
paths, with no events/copies and an unchanged global observer. Finally,
`AmpereTiledNonvacuous.nonvacuous` establishes independent complete checked
source/rf/co/observer existence under the identical full Pre, including zero K
and inactive M/N. The universal output/frame theorem, this independent existence
theorem and a complete nonuniform four-CTA/three-phase instance now meet the
three formal tiled-case criteria relative to the current model. Tests also
check every actual barrier site, reject cross-site/wrong-generation matching,
and cover unaligned unused aliases for zero-K/inactive paths. Full PTX/ISA,
runtime/compiler and IEEE correspondence remain separate; native overlaunch is
outside the canonical formal grid. Hopper and the other original goal duties
remain open, with exact logits/token requirements unchanged.

`MemoryGraph/Rules` provides `phase_writer_source` and `phase_writer_visible`,
which derive the current write's source/value for
every admitted rf/co when all other actual writers are earlier than that write
or later than the read. `Ampere/Memory.published_phase_copy_source/value` connect
them to waited CTA publication. Actual phase ordering and eligibility remain
proof duties. Local successful traces can still contain inconsistent replies.


`Hopper/Syntax` adds an explicit PTX 8.0 / sm_90a target and embeds prior Ampere
instructions without changing branch PCs. Five fixed CTA-local layout-v0 forms
are retained: mbarrier init/inval, release `arrive.expect_tx` with sink destination,
relaxed `complete_tx`, and acquiring `try_wait.parity`. Every qualifier belongs
to the selected instruction form. Returned state tokens, cluster variants,
layout-v1, optional wait hints and other qualifiers remain rejected. The lexer
retains `::` qualifiers while ordinary labels still delimit real source PCs.
`Hopper/Thread` emits resource operations at actual CTA-local addresses and uses
a separate oracle bit for each wait, incrementing the real query counter. It
performs no shared barrier-state update or data transfer. Source-location
instrumentation erases exactly to the same interpreter, and local execution
rules retain actual operands, source PCs and predicate writes.

`Hopper/Mbarrier` separately checks one ordered resource history. It preserves
signed transaction counts, arrival counts and the layout-v0 bounds. Both counts
must vanish before a phase advances and resets its pending arrivals. A successful
wait must observe the preceding completed parity before a subsequent phase's
arrival; failed waits provide no such permission. False answers remain deliberately
overapproximated even after completion. Universal rules prove count invariant
preservation, completion conditions and arbitrary-phase/positive-count single-
and two-phase cycles. Notification units remain opaque here; matching them to
actual TMA bytes is a later obligation. An explicit relaxed `complete_tx` is a
notification, with no data-memory release/transfer claim.

The actual 12-instruction `hopper_mbarrier.ptx` has a complete two-phase source
and admitted resource history, and a timeout/retry execution taking 14 slots.
Actual event PCs, query counts and CTA/address separation are checked. The
four-instruction `hopper_mbarrier_no_complete.ptx` can return locally under a
lying successful oracle; the independent protocol rejects that history because
transactions remain pending. Neither helper is a Hopper GEMM acceptance case.
Both assemble for sm_90a, and neither has new Hopper GPU execution evidence.
Actual multi-thread source/resource/control matching is established below.
Opaque-object allocation/UB, TMA descriptors/copy bytes/proxies,
WGMMA groups/register arithmetic and complete
single-stage/double-buffered GEMM correctness and legal witnesses remain open.
The full original goal and exact logits/token requirement are unchanged.


`Hopper/Source` now checks launch-wide actual trace provenance, full thread
coverage and completion. `source_event` recovers the actual emitting step and
pre-step PC from the same interpreter. `Hopper/Inventory` enumerates the actual
mbarrier event identities, operations and CTA-qualified locations.
`ResourceHistory` requires each proposed resource history to be an exact
permutation of that inventory, with unique identities, preserved issuer order
and an admitted protocol. It proves soundness, coverage and resource identity,
then derives the real prefix state/phase for every successful wait and arrival.
These obligations prevent hiding a peer wait or adding a fictitious complete_tx
to make counts balance.

`ResourceControl` separately combines source program order, actual CTA barrier
tags and resource-history order. A finite rank certificate establishes acyclic
control for a proposed witness; these resource edges do not publish memory.
The 15-instruction `hopper_mbarrier_peers.ptx` has complete actual runs for all
four threads in a two-CTA launch, exact per-resource histories and an acyclic
control certificate. Equal shared offset zero in different CTAs remains two
resources. Wait PCs and both CTA-barrier sites are checked against actual source.

The 18-instruction `hopper_mbarrier_cycle.ptx` is an actual circular waiting
counterexample. Two successful-oracle source runs terminate locally, and each
resource separately has a valid source-matching history. An exhaustive check
of the finite resource permutations proves their only possible protocol orders;
every matching family then has a cycle through source and resource order.
The model-relative theorem rejects all resource/control witnesses for that
candidate, beyond rejecting just one proposed schedule. This is not a GPU
termination/deadlock theorem, and the fixture is not GPU-launched. Both new
fixtures assemble for sm_90a. Full Hopper memory/proxy/CTA/async admission, actual
TMA operation identities/bytes and WGMMA/GEMM still require the remaining bridges.
The original goal, independent legal-witness criteria and exact logits/token
requirements are unchanged.


`Hopper/TmaDescriptor` describes the unswizzled, non-interleaved, unit-stride,
whole-byte 2-D tile profile with default byte-zero fill. Signed 32-bit coordinate
interpretation, per-byte strided source addressing, out-of-bounds fill and a
parameterized global span bound are checked in Lean. `.s32` declarations retain
their 32-bit word representation; the fixed TMA coordinates receive signed
interpretation. Signed arithmetic opcodes and float bit reinterpretation remain
outside this extension.

The frontend now retains the fixed PTX 8.0
`cp.async.bulk.tensor.2d.shared::cluster.global.mbarrier::complete_tx::bytes`
form and `fence.proxy.async.shared::cta`. Negative coordinate literals preserve
all 32 bits. Source TMA issue consumes two real query indices for descriptor and
payload and checks payload length. `TmaSource` derives the opcode, reply shape
and query metadata from any actual successful emission. Raw descriptor, cluster
destination and barrier addresses are retained in the issue record. `TmaGraph`
derives one independent operation identity from that actual source event;
descriptor, byte reads/writes and notification have separate nodes outside
issuer program order. Descriptor nodes use tensormap proxy, data nodes async
proxy and the notification uses generic proxy. An explicit resolver handles
raw cluster addresses; issuer-local resolution is one chosen layout.

`TmaResources` matches all actual source barrier operations plus actual implicit
TMA notifications. Each notification has its own transfer identity, actual
barrier address and source-derived byte count, with uniqueness and exact inventory
checks. Existing signed-phase rules derive successful waits' real prefix states.
`TmaControl` combines source/CTA order, per-byte transfer dependencies and resource
order using a proved acyclic rank. These are control edges; proxy-preserved
memory visibility still needs the combined memory adapter.

The actual 13-instruction `hopper_tma_copy.ptx` has source, immutable descriptor/
payload agreement, resource and control components for a padded 32-byte tile.
Byte zero reads global address 196, byte 16 starts the next row at 260 and the
last destination byte is shared 47. There is no source access outside the tile.
A short payload faults in the interpreter. Duplicate notifications fail identity
coverage even when their counter protocol alone passes. A wrong payload can
return locally and pass resource counts but fails byte agreement. A descriptor
that notifies 16 bytes against the source's expectation of 32 admits no matching
resource history in any permutation. These proofs do not establish an all-
candidate copy contract: descriptor/payload agreement is independently checked
for constructed components, not yet derived from combined weak-memory admission.
The opaque tensor-map encoding, address-space/runtime/profile bridge, full proxy
and ordinary/Ampere/TMA rf/co/race/observer integration, complete construct/UB
checks and Hopper WGMMA/GEMM remain required. Raw byte-zero fill is not a new
numerical f16/IEEE reinterpretation result. Assembly passes for sm_90a; no new
Hopper GPU execution is claimed. The full original goal remains active.


`ISA/TensorMapStorage` now gives the mathematical descriptor a tagged opaque
128-byte storage representation. These tags are model objects, like the existing
symbolic real fragments; they are not CUDA's binary encoder. `Hopper/AccessGraph`
retains source ordinary/RMW accesses, source-issued non-bulk copy reads/writes,
and descriptor/per-byte TMA accesses in one inventory. Its implicit operations
remain outside issuer program order and use distinct agents. This inventory
supplies no generic-only moral-strength or cross-proxy publication rule.

`Hopper/InputValues` derives immutable descriptor and payload agreement for any
source-formed candidate satisfying explicit read-fragment obligations. It uses
separate initial views for generic, async and tensormap proxies, reads-from
agreement at eligible sites, and immutability against **every** combined-graph
writer. Descriptor fields are recovered from stored typed objects rather than
assumed equal to oracle replies. In-bounds payload bytes follow initial async
memory; a separate primitive zero-fill rule constrains out-of-bounds writes,
which have no read event. A source oracle may return locally yet fail these rules.

`Tests/TmaInputValues` independently constructs this input-fragment evidence for
the existing padded tile and instantiates both parameterized rules. It checks
ordinary/RMW/non-bulk overwrite preservation, equal-size descriptor substitution,
wrong payload rejection, separate proxy views, and actual negative-coordinate
source steps with legal/illegal OOB fills. This closes an input-value component,
not full Hopper execution admission or the required GEMM case. Proxy-aware
rf/co/races/observer rules must still derive eligibility and publication; CUDA
opaque encoding, initialization, allocation/ISA UB and WGMMA remain open. The
full original goal and exact logits/token requirement remain active.


`Hopper/TmaObservation` computes a completion observation from actual resource-
history prefixes. Each stamp contains the phase and the number of preceding
initializations, so reinitializing the same address creates a different lifetime.
The sufficient observation rule matches a real transfer notification with a true
wait for the immediately completed phase in the same lifetime. It does not equate
resource order, an old parity value, or explicit `complete_tx` with publication.
Its checked observations recover actual copy/target/wait events and prefix
states, and imply the corresponding resource/control edge.

`Hopper/ProxyPublication` publishes only a transfer's own byte writes to generic
accesses after an observed completion. Cluster membership and the wait's CTA-
local resource are explicit. A separate same-thread shared proxy-fence rule
protects a prior generic access against a subsequent TMA overwrite. It introduces
no blanket release of prior issuer writes. Generic CTA propagation still needs
full participation admission. The rf/co visibility fragment separates gated read
agreement, initialization, no-stale publication and no-future protection. Unique-
writer and repeated-phase source/value rules quantify over arbitrary rf/co;
complete proxy/race/coherence/observer admission is still pending.

The actual 16-instruction `hopper_tma_publish.ptx` waits for TMA, reads a shared
u32 and emits a global u32 store. `Tests/TmaPublication` checks source production
and completion for every local read reply, derives each consumer byte and the
emitted store under the explicit visibility fragment, and rejects the zero reply
for every rf/co when that consumer site is eligible. An independently constructed
four-byte read-fragment witness uses the word decoded from initial input bytes
196..199. It is not a full allowed-execution/observer witness or Hopper GEMM
acceptance case. `Tests/TmaPhases` covers multiple phases, parity reuse, object
reinitialization, false waits, explicit-completion non-publication, and actual
source prefixes with/without a shared proxy fence. Refusing an observation or a
protection edge does not itself prove that the entire PTX execution is forbidden.
No Hopper hardware result, performance improvement or new-method claim is made.


`Hopper/ByteOrder` adds byte-indexed order, explicit same-proxy moral strength,
RMW observation chains, mixed-size races, taint and derived read eligibility.
A proxy edge cannot change the byte location midway through a path: the
currently supported shared fence cannot order an unrelated global location
through a TMA write. Resource serialization is still not blanket memory order.
`AccessInversion` recovers actual kinds and byte locations from the combined
inventory. `ByteVisibility` projects guarded causal constraints into the
previous visibility rules using this derived eligibility; it has no caller-
supplied eligibility predicate. Full coherence/atomicity/observer and ISA
admission remain separate. `ByteWitness` constructs the causal component using
actual read values, causality ranks and maximal preceding writers.

`Tests/TmaEligibility` classifies all actual writers and overlaps in the
publication source family, independent of replies and rf/co. For every local
reply and rf, its actual conflicting bytes are ordered or are the same writer;
race freedom and eligibility follow. The consumer/store constraint now follows
from the causal component without a separate eligibility premise.
`Tests/TmaInputCausal` independently constructs that causal component for the
original completed padded-copy helper and covers all its descriptor/data reads.
The subsequent consumer closure below now supplies the current memory and observer witness; full ISA/runtime admission remains separate.

`Tests/TmaRaces` proves a mixed-size race for the actual no-fence local source
prefix and shows that all reads lose eligibility; the fenced prefix orders the
corresponding pair. These are memory-component probes, not complete ISA-valid
kernel runs or a claim that adding one fence closes all resource/launch/lifetime
requirements. The full original goal and exact-output requirement remain active.


`Hopper/Memory` now bundles the current proxy/byte-aware causal constraints,
strict partial coherence, single-copy/RMW atomicity, SC-per-location and byte-
order acyclicity. `Hopper/Observation` separately checks completed generic global
observations and requires coverage of every emitted global write. Its selector
uses actual write values; output correctness is not a witness premise.

`Tests/TmaConsumerWitness` constructs agreement for every descriptor, TMA input
and generic consumer read. `TmaConsumerMemory` independently supplies all current
memory-component conditions, and `TmaConsumerObserver` constructs an observer
covering the four output bytes in a 16-byte guarded arena. For the parameterized
source family, arbitrary admitted rf/co/observer choices yield the initial-input
word's bytes and preserve non-output bytes in the observed domain. Initial or
incomplete output selections are rejected. These are checked proofs rather than
new GPU execution results.

`Tests/TmaConsumerChecked` joins the actual completed source, every matched
resource history, acyclic source/data/resource control, memory and observer
witness, with explicit generic/async initial-view correspondence. A zero reply
still passes the source/resource/control components but fails every current
memory witness. This closes the helper's current abstract memory/observer gap;
arbitrary-source extraction, complete ISA/launch/cluster/in-flight lifetime and
allocation checks, descriptor encoding/runtime correspondence, WGMMA and the
required Hopper GEMM cases remain. The full original goal remains active.

The four fixed shared/shared WGMMA forms now have typed program data:
`fence.sync.aligned`, `mma_async.sync.aligned.m64n8k16.f32.f16.f16`,
`commit_group.sync.aligned` and `wait_group.sync.aligned`. The MMA profile fixes
input scales to +1/+1 and transposes to 0/0; unsupported shapes, register-A,
types, qualifiers and optional operands fail closed. `Hopper/WgmmaThread` uses
the same Hopper AST and delegates ordinary/TMA steps at their actual PCs to the
existing interpreter. The old entry explicitly refuses WGMMA instructions.

The local ledger tracks pending results, register fence obligations, empty
committed-group identity and the acknowledged completion prefix. Ordinary reads
or writes of pending accumulators fault; unrelated arithmetic and TMA may
overlap. Consecutive same-shape MMA reads the pending accumulator value, and a
wait writes back only newly completed calls in issue order. Waiting does not
implicitly commit. Wait replies may acknowledge extra recent committed groups;
they cannot complete uncommitted work or reopen completed groups. A register
fence neither completes work nor replaces an async proxy memory fence.

`Tests/WgmmaProtocol` checks these local guarantees and their counterexamples.
`Tests/WgmmaSource` checks all 128 local executions of the generated
`wgmma_probe.ptx`, including actual source PCs, lane identities, query numbering
and identical WGMMA schedules. This assembled sm_90a probe has uninitialized
shared inputs and arbitrary matrix replies. It is a source/protocol component,
not an admitted shared-memory/arithmetic witness, verified GEMM or Hopper GPU
execution test. Descriptor/read/tensor components are described below; collective
control, combined memory admission, in-flight lifetimes and the required
single-stage and double-buffer GEMM proofs remain to be completed.

The next tensor component is now present in `Hopper/WgmmaLayout`,
`WgmmaDescriptor`, `WgmmaInputs`, `WgmmaStorage` and `WgmmaTensor`. Accumulator
ownership covers all 64x8 entries reversibly. The descriptor profile decodes
actual bit fields and selects packed no-swizzle core layouts with leading=128
and stride=256 bytes. Every A/B byte has a unique bounded address; the two
operand arenas are disjoint. This is a supported profile, not all legal PTX
descriptors. The previous probe's unvalidated strides overlapped elements;
the probe now uses packed descriptors and the old values have rejection tests.

MMA issue captures all 2304 logical operand byte replies at its actual query.
Their shared locations derive from the descriptor; reads use an async warpgroup
operation identity. Tensor conditions check input byte agreement, f16 encoding,
cohort metadata and exact-real arithmetic. Independent witnesses cover arbitrary
real A/B and accumulators; a wrong arithmetic reply fails despite correct cohort
and read data. The nonuniform test checks result 64479. The generated-source
prefix and MMA event are connected to these components for arbitrary A/B.
The constructed packed shared view still needs to follow from real producers
and admitted RF/proxy/lifetime rules; it does not initialize shared memory.

`hopper_gemm_stage.ptx` is a new single-stage 64x8x16 proof target, with a
(4,8,4) CTA, leader initialization, two TMA transfers, mbarrier wait, WGMMA
fence/commit/wait, four stores per lane and final barrier retirement. Its global
inputs use packed core layouts, described by explicit 2-D tensor views. All 47
instructions translate with checked typing and assemble for sm_90a. Mathematical
geometry rules map the intended launch and four store offsets to the accumulator
layout, covering all output elements uniquely and within bounds. The source
execution and tensor connections described below are now checked. Full resource,
combined memory/observer admission, single-stage and double-buffer GEMM
correctness/nonvacuity and Hopper hardware execution remain open.


`Hopper/UnifiedSource` admits the rich WGMMA execution directly. Its component
view retains every native event slot as an opaque tag, so existing TMA/resource
lookups retain actual event identities and PCs. Tags grant no memory access,
barrier operation or CTA rendezvous. The legacy interpreter still rejects native
WGMMA; no legacy source predicate is asserted for the mixed program. TMA payload
length and query facts follow from actual delegated steps. Unified completion
requires both a returned thread and no pending WGMMA operations.

`Hopper/UnifiedAccess` inventories ordinary, RMW, non-bulk and TMA accesses plus
2304 shared operand bytes per representative WGMMA operation. Its async agent is
distinct from the TMA agent and its implicit reads are outside issuer program
order. `UnifiedCollective` matches all 128 actual MMA source events, lane and
uniform operation metadata. This inventory and membership record do not yet
supply the full collective schedule or combined weak-memory admission rules.

`Kernels/HopperStageSource` constructs complete executions of the actual stage
for arbitrary real A/B and every physical thread. Checked state checkpoints
compose with the fixed interpreter: the leader executes 47 steps and peers 41.
The source-matched collective, actual TMA copies and tensor component share one
abstract post-transfer byte view. Actual source address arithmetic places all
512 emitted matrix-valued stores within the 2048-byte output; the nonuniform
last store writes 1472 at global address 10236. These are exact-real symbolic
source events. Independent initial-input, resource and control witnesses are
now checked as described below. Combined RF/coherence/proxy/lifetime/allocation,
native collective-control and an admitted global observer remain open. It is
not yet universal correctness for arbitrary admitted executions or a completed
witness under a full kernel Pre.


`Hopper/UnifiedSchedules` checks the full aligned fence/MMA/commit/wait sequence
against every physical lane of each participating warpgroup. Raw signatures
retain the evaluated per-thread D predicate; that local value is not added as a
collective uniformity requirement. `WgmmaSignatureRules` proves signature PCs,
sequence numbers and warpgroup IDs come from actual source steps and that raw
trace schedules agree with checked located replay. A complete 128-thread source
litmus is rejected when only tid.x=0 threads commit an empty group, even though
all threads have returned with no pending matrix operations.

`HopperStageInputs` independently constructs global packed A/B bytes at
65536/69632 and two opaque 128-byte tensor-map objects at 4096/4224, preserving
an arbitrary frame elsewhere. A reusable contiguous-row address lemma derives
TMA source locations for arbitrary base/height/offset; both actual transfer
payloads agree with these global inputs. All actual TMA copies are classified,
so the agreement covers the whole candidate. Symbolic tensor-map tags represent
a mathematical host object, not CUDA's native binary encoding. A source-complete
candidate with incompatible integer input bytes fails payload agreement.

`TmaResourceErasure` is a proved metadata projection for efficient checking.
It preserves event identities, presence, mbarrier operations, CTA tags, TMA
notifications/internal edges, resource inventories and control consistency.
Payloads, oracles and final states are discarded only in this resource view;
source production and memory agreement are never asserted for the erased data.
`HopperStageResources` uses it to check the actual 133-entry history: initialize,
arrive with 2304 expected bytes, notify 2048 and 256 bytes separately, wait in
all 128 threads, then invalidate. Histories for all other locations are empty.
A strict rank proves source program order, both CTA rendezvous, TMA internal
edges and resource serialization are acyclic. Every source wait observes both
transfers in the same object lifetime and completed phase.

`HopperStageTmaComponents.stage_checked_components` bundles the independent
source/input/resource/control witness with full aligned schedules and the
source-matched tensor component for arbitrary real A/B and an arbitrary initial
frame. Missing either TMA notification and invalidating after only the first
wait are rejected; early invalidation preserves the complete event inventory
and per-thread source order, demonstrating why those checks alone are not
enough. The actual one-phase source family now has separate independent
combined native memory, completed-observer and construct-control witnesses,
with observed matrix/frame contracts. Arbitrary-source correctness and full
allocation/lifetime admission remain open. The required double-buffered K-loop
case is partially implemented, with the remaining proof boundaries below.


`Hopper/UnifiedNativeOrder` connects actual transfer completion to native operand
reads. TMA publication names its own copied byte and requires completion
observation plus source order to every member of the source-matched collective.
Generic shared accesses require an actual async proxy fence. Native completion
requires a later matching source wait with a committed group below the observed
completion cut; reuse additionally orders that wait before the actual new TMA
issue. Source launch/control order alone grants no byte publication.

`UnifiedOrder`, `UnifiedCausal` and `UnifiedMemory` supply the proxy/byte-aware
race, eligibility, RF/coherence, atomicity and SC-per-location components over
the complete ordinary/non-bulk/TMA/native inventory. Implicit native reads stay
outside issuer program order and keep their own async operation agent. The
original base predicates and interfaces remain intact. Checked global-byte
paths between base nodes are exactly the old ByteOrder; native shared-memory
rules cannot silently publish an unrelated global byte. `UnifiedVisibility`
provides unique- and phase-writer rules for arbitrary compatible RF/co, keeping
derived eligibility explicit and allowing multiple writes during buffer reuse.

`HopperStageNativePublication` proves actual publication for all 2304 operand
bytes. `HopperStageMemoryInventory` classifies all shared writers as the two
actual TMA operations. The whole-candidate footprint proof separates one-byte
shared accesses, aligned global output words, descriptor reads and packed input
reads; this derives absence of mixed-size races. Publication and unique shared
writers then exclude native taint, so `native_rf_forced` requires no caller
eligibility or additional no-race premise: every causal-memory-compatible RF/co
selects the exact producer. `native_input_agreement_derived` connects those
reads to the represented matrix view. This is conditional visibility under the
stated memory constraints. `HopperStageMemoryWitness`,
`HopperStageObserverWitness` and `HopperStageObservedOutput` additionally
construct independent memory/observer witnesses and prove matrix/frame contracts
on the actual source family. `HopperStageNativeControl` supplies an independent
construct-control rank with warp-local sync endpoints and full aligned
participation. Universal correctness over arbitrary source candidates remains
separate; the generated native/CTA cycle fixture passes the old checks but is
rejected by the new construct graph.

`HopperStageNativePrefix` checks real generated-source prefixes for every lane,
stopping after commit at PC 31. All 128 actual MMA events form a matched
collective, each lane has one pending operation, and no native wait has occurred.
These prefixes cannot justify shared-memory reuse. The complete source waits
are separately matched to actual group completion. Tests reject an initial-only
RF map even if its values could match the copied input, and check native byte
identity, proxy, footprint, source-prefix state and completion metadata. These
are formal source/memory results; no new Hopper GPU or IEEE result is claimed.


The actual `examples/hopper_double_buffer_gemm.ptx` now supplies a two-stage
64x8 output-tile loop with K=16*TILES. It issues the next TMA copies before the
current WGMMA, waits on committed groups and uses a per-iteration CTA rendezvous
before later reuse. Both mbarrier parity counters toggle independently. Its
101 instructions include runtime descriptor encoding from actual shared symbol
addresses; fixed descriptor start addresses are not embedded in the PTX.
`ISA/Shift` and `Hopper/WgmmaDescriptorEncoding` prove the unsigned-shift model
and packed descriptor construction for arbitrary aligned supported shared bases.
Hopper generated typing proofs use an explicit recursion-depth allowance and
are still checked by the Lean kernel.

`HopperDoubleBufferSpec`/`Matmul` relate arbitrary-length tiled accumulation to
an ordinary K=16*T matrix product. `TmaPackedTiles` proves packed input address
mapping; `HopperDoubleBufferPhases` and `Protocol` prove stage counters, parity
and arbitrary-length resource-local protocols. Actual source probes cover
T=0..5 in the producer and last-consumer lanes, including reuse of both stages
and parity wrap. These are finite source checks with chosen successful waits
and zero matrix inputs, not all-thread launch consistency or nonuniform source
execution tests. Concrete nonuniform numerical examples test the independent
mathematical specification separately.

`HopperDoubleBufferHeader.header_execute` now proves execution of the actual
PC 45-to-61 loop header for every tile number and thread context, allowing any
finite failed-wait prefix before success. It derives stage/descriptor/parity
selection, the retry back edge, query consumption and independent phase updates,
and preserves unrelated integer registers and arbitrary real accumulators.
The entry assumptions explicitly include the loop registers and no pending
WGMMA call; they are not yet reconstructed from the initial state for every
iteration. The rule prescribes only this header's wait replies and does not
assert those replies are admitted by the resource/memory graph.

`HopperDoubleBufferPrefetchGuard` proves the actual next-tile and producer
branches. `HopperDoubleBufferCompute.compute_and_advance_execute` now connects
the actual fence/MMA/commit/wait at PCs 76..79 to the CTA rendezvous and loop
advance at PCs 80..84, for bounded tile counters and arbitrary retained call
history. Wait-zero completion leaves no pending calls and writes the four
captured oracle results; historical calls are retained and do not write again.
The separate CTA-barrier rule explicitly preserves pending WGMMA calls. These
source rules do not yet constrain matrix replies to the GEMM specification or
admit repeated shared-memory reads/writes.

`HopperDoubleBufferPrefetch` now proves actual producer PCs 65..75, including
opposite-buffer addressing, A/B coordinates and two TMA issues at the actual
query indices. `HopperDoubleBufferIteration.iteration_execute` composes a full
actual PC 45-to-loop/output iteration for bounded tile counts, arbitrary thread
contexts, retained history and available accumulator values, including finite
unsuccessful waits. Next-iteration register and accumulator invariants, native
group completion and empty pending calls are proved. Accumulator readability is
derived from register availability; execution success is not assumed. Payload
length premises constrain only the producer paths that actually issue copies.
Descriptors, copied bytes and arithmetic replies remain subject to independent
resource/tensor/memory admission.

`HopperDoubleBufferLoop.loop_execute` composes any bounded number of actual
iterations with per-tile finite retries and independently indexed reply
conditions. It preserves the loop invariants, retained call history and control
registers; `LoopSchedule` proves query accounting and disjoint wait intervals.
`HopperDoubleBufferEntry`/`Initialization` reconstruct actual parameter loads,
runtime descriptors, producer election, both barrier initializations and initial
copies. `KernelLoop.kernel_loop_source` now constructs a represented-zero-input
run from empty state to output entry PC 85 for every lane and positive supported
tile count. Zero tiles take a separately proved source path. The chosen replies
have checked source payload shapes; a completed, memory-admitted launch is not
implied. Launch context/reply data moved into `HopperDoubleBufferContext`, shared
by parameterized proofs and finite probes.

`HopperDoubleBufferOutput` now proves actual address arithmetic, four f32
stores, the final CTA barrier, producer invalidations and return for arbitrary
available typed accumulators. `KernelSource` constructs the complete 128-thread
represented-zero-input source candidate for every supported tile count,
including T=0, with source production, source-PC correspondence, thread coverage
and local completion (`done`, no pending WGMMA). `WriteInventory` derives exactly
four ordinary global writes per lane, disjoint output-byte ownership and complete
coverage of the 2048-byte C region. These are typed symbolic real bytes; source
well-formedness/completion does not admit a resource/tensor/memory graph or prove
an observable final heap.

`HopperDoubleBufferDataSource` now constructs complete source witnesses for
arbitrary real A/B tile families. Query inversion identifies the actual native
and TMA reply tile; matrix replies use the fixed WGMMA arithmetic on prior
accumulators. Source-captured inputs and symbolic output writes are proved to
match the independent tiled/matmul specification. `DataCalls` connects the
actual emitted calls to lane/group/ordinal cohorts and arithmetic, while
`DataTensor` supplies their tensor component over a logical shared-tile view.
That view still needs TMA/memory admission. Nonuniform three-tile examples
connect actual source writes to 20 and 29440; wrong zero/reset final arithmetic
is rejected. The new data family places B after A as a function of tile count,
with alignment/profile/address-bound proofs, so arbitrary nonzero inputs can
have disjoint regions even beyond 32 tiles.

`HopperDoubleBufferEventIndices` now identifies each tile's actual MMA and
successful wait by exact source-event index. `DataCollective` matches all 128
lanes with actual PC 77, synchronization sequence `4*tile+1`, group/ordinal and
descriptors, including distinct identities across rounds. `TmaSources` links
initial and prefetched A/B copies, expectations and implicit notifications to
actual source events, retaining identities when a shared slot is reused. Every
captured MMA operand byte has the same address/value as its tile's implicit TMA
write. `TmaInputs` independently represents packed global tiles and tensor-map
storage and proves the copies' source locations and payload values for every
supported tile. These are source/access components: they do not prove that a
write has completed or become visible before use, or that reuse is safe.

`HopperDoubleBufferResourceHistory` now constructs both stage histories from
actual initialization/expectation/wait/invalidation source IDs and implicit TMA
notification IDs. Every entry belongs to the actual resource inventory, and the
arbitrary-length protocol runs to invalidation, including zero tiles.
`ResourcePrefixes` and `ResourceObservations` prove per-phase prefix states and
match each of the 128 successful waits to its own A/B completion notices.
Different-phase notices are rejected even after parity wraps; buffer reuse
preserves one object lifetime and advances the absolute phase.
`ResourceSerials` proves closed source-index formulas; `ResourceRanks` and
`ResourceUnique` recover every history index from its actual origin and prove
origin uniqueness for all tile counts. `ResourceSourceOrder` proves thread-local
program order and the local notification-before-wait relations.
`ResourceCases`/`ResourceTraceCases` exhaustively classify actual indexed source
resources through initialization, every loop iteration and return.
`ResourceMembership` and `ResourceAdmission` prove reverse inventory inclusion,
exact inventory permutations, empty inventories outside the two gates, and
`Tma.HistoryValid` for every resource location and supported tile count.
`TmaInventoryUnique` supplies the generic inventory uniqueness argument.
`TmaAgreement` also proves that all actual copies use the stored tensor maps and
payload bytes of the independently represented packed inputs.
`ControlClock` embeds producer/peer serials into one virtual order, including the
missing final prefetch. `ControlGenerations` and `ControlCtaCases`/`Trace` classify
actual generation-indexed CTA endpoints. `ControlResources` and `ControlCtaRanks`
prove that source PO, CTA, implicit TMA steps and resource serialization all
increase the same rank. `ControlAdmission` now proves `Tma.ControlAcyclic` and
constructs the full `Unified.TmaComponents` record for supported arbitrary tile
counts and real inputs in this chosen source witness. This is source/resource/
control/input component admission; native eligibility, combined memory and
observable output remain separate. Checked omission and ghost-notification
examples show why local protocol checks alone are
insufficient: a virtual zero-byte completion can pass the protocol while having
no actual source issue and is rejected by `HistoryValid`.

`NativePublication` now derives byte-specific TMA publication to each actual
128-lane WGMMA collective from valid histories, observed completion and source
order. `NativeCompletion` identifies the actual `wait_group 0` event and completed
group for every tile/lane. `NativeReuse` connects each completed operand read
through the actual generation-indexed CTA rendezvous to every later TMA write
of that physical byte in the same slot. These arbitrary-real, parameterized
component proofs do not construct RF/co, establish read eligibility or admit the
full native-control/memory/observer graph. CTA and mbarrier waits are formally
rejected as substitutes for native completion; parity wrap cannot publish an
older phase. New checks also cover omitted final prefetches, repeated group
frontiers, distinct producer identities on reused slots and both operand-byte
boundaries.

`NativeSchedules` and `NativeInventory` now prove the full source-indexed
fence/MMA/commit/wait sequence for every tile and all 128 lanes, including
checked replay and actual-PC links. `NativeControl` proves combined native,
TMA/resource and CTA control acyclicity and `Unified.ControlAdmitted` for the
supported arbitrary-real witness. Native arrival ranks precede every matching
warp return, while preserving lane offsets in the resource histories. Native
completion edges retain the actual issue group and later wait frontier. This
closes native construct control, independently of byte-memory admission.

`MemoryInventory` exhaustively excludes ordinary shared writes and non-bulk
copies in the actual source. `MemoryGeometry` identifies every shared writer
at a native operand byte as an actual TMA producer of a specific same-slot
round; it does not assume one writer across rounds. `MemoryPhases` orders all
these writers around each read through checked publication/completion/reuse.
`MemoryInputs` excludes local native-byte taint for arbitrary RF, and derives
current-round RF plus stale/future rejection under explicit full-memory and
no-mixed-size-race premises. It also rejects the old initialization-only
coherence relation for a reused byte. These conditional rules do not supply
a coupled memory witness.

`SourceFootprints` and `AccessRegions` now exhaustively classify ordinary,
TMA, tensor-map and native footprints. `NativeEligibility` excludes global
mixed-size races for arbitrary RF and derives native eligibility without a
caller-supplied race premise. The generic footprint-conflict rule is also used
by the one-stage baseline. `ReadWitness` constructs actual-round native RF and
initial-memory RF for global input/descriptor reads, and proves value agreement
for arbitrary represented inputs and frame, without assuming a memory
execution. The following modules separately establish causal/coherence,
atomicity/SC and observer admission of this chosen RF.

`UnifiedMemoryControl` proves a one-way refinement from justified byte edges
to control paths when actual non-bulk copies are absent. `MemoryRank` uses the
checked native-control rank to exclude byte/observation/causality cycles.
`ReadConflicts` derives immutable global reads; `CausalWitness` constructs RF/co
causal constraints. Actual shared and output writer ordering then establishes
all coherence fields, single-copy/RMW atomicity and per-location SC.
`MemoryWitness` now constructs the full model-relative `Unified.MemoryConditions`
record for arbitrary represented inputs/frame, compatible with the same
source/TMA and native-control witness. No full-memory execution or rank is
assumed as an admission premise.

`StoreInventory` recovers actual source-indexed output stores and proves unique
global writers, while retaining repeated TMA writers for reused shared bytes.
`ObserverWitness` constructs a completed generic-proxy observation compatible
with the same RF/co, source/TMA and native-control witnesses. `ObservedOutput`
proves its output bytes equal the independent real matrix-product specification
and preserves the adjacent frame bytes. It also proves the matrix result for
any compatible RF/co/observer of this fixed source family, and rejects omitted
outputs or observation of initial memory instead of an emitted output write.
The witness covers arbitrary represented real inputs/frame and supported tile
counts, including zero tiles. This is a model-relative observed-output result;
it does not reconstruct every admitted source execution from the full Pre.

`UnifiedTensorMemory` supplies a generic bridge for any source-matched
collective: admitted representative byte reads, selected actual producers and
represented storage identify the matrices used by separately checked arithmetic.
It propagates that agreement to all lanes using the collective cohort and
derives the accumulator result. `HopperStageTensorMemory` and
`HopperDoubleBufferTensorMemory` instantiate the same rule for the one-stage
and reused-slot sources. The repeated case derives selected RF from its proved
writer-phase rules and gets producer values directly from actual TMA transfers.
Tests reject stale/future tile inputs and incorrect accumulated values. The
generic theorem quantifies over arbitrary candidates; these two instantiations
still use their constructed source families. Arithmetic admission and complete
source reconstruction remain explicit obligations.

`WgmmaTrace` proves finite prefix/suffix decomposition and unique completed
execution counts, states and events for a fixed interpreter/oracle. A done
thread cannot accept padding steps. `WaitReconstruction` derives the first
successful wait and all preceding failed retries from an actually completed
arbitrary-oracle run at the wait loop. `HeaderReconstruction` extends this to
the loop head: actual selection, waits and phase updates determine a unique
retry count and preserve the exact remaining state/event suffix. No retry
schedule or eventual readiness is a premise; these rules are conditional on
finite completion. Tests use an actual generated-source suffix with three
failed waits before success, and reject truncation, padding and a never-ready
completion claim. The following modules extend this header reconstruction.

`WgmmaTmaInversion` derives payload length from successful actual TMA steps,
including steps reached after a prefix of a completed run.
`TransferReconstruction` and `PreludeReconstruction` derive both producer
payload-size conditions and preserve the exact prefetch state/events. Skipped
prefetch paths leave unused replies unrestricted. `IterationReconstruction`
then extracts `LoopReplies` and reconstructs one full iteration from any
completed arbitrary-oracle run satisfying the loop-entry register/accumulator
invariant. Retries and required payload sizes are conclusions, rather than
caller premises. Tests execute a producer with three failed waits followed by
full A/B prefetches, reject short A or B payloads, and check that unused short
replies on consumer/last-tile paths do not prevent completion.

`LoopLocality` proves that query IDs, fuel, complete checkpoints and events of
a prefix depend only on retry entries in that prefix. `LoopReconstruction`
uses those equalities to extract a finite retry schedule one iteration at a
time from an actually completed arbitrary-oracle run satisfying the loop-entry
invariant. The existing loop executor then reconstructs the whole loop, its
output-entry state at PC 85 with no pending WGMMA calls, and the exact remaining
state/event suffix. Compatible schedules agree on executed entries; future
entries may differ. This is conditional source reconstruction, with no caller
retry schedule, eventual-completion or desired arithmetic-result premise.
An additional generic corollary re-expresses the extracted execution at any
independently proved compatible schedule using prefix locality. Tests keep
the complete state/event result for actual producer and consumer suffixes,
reject wrong executed retry entries, and show both future-prefix preservation
and the freedom to change unexecuted entries.
`InitialReconstruction` now derives the first producer TMA sizes from finite
completion and executes initialization with arbitrary captured replies.
`OutputReconstruction` preserves output registers through the arbitrary-retry
loop, fixes the exact output/return suffix, and proves the complete zero-tile
path for every lane and oracle without constraining unused replies.
`KernelReconstruction` composes these with the loop theorem: a finite completed
run from the initial state has exactly the reconstructed count, final state
and events at canonical parameters/geometry. This also classifies every thread
of an arbitrary well-formed completed candidate, using checked thread coverage
to recover its lane. It does not restrict candidates to the constructed data
witness or assume desired matrix replies. Source reconstruction preserves those
arbitrary captured replies; full-Pre functional refinement still requires the
resource/memory/tensor links, including histories for nonzero retries.

`ReplyInventory` and `CandidateMemory` now lift that reconstruction to exhaustive
ordinary-access inventories for any well-formed completed candidate at the
canonical launch. Ordinary source events have no reads, shared writes or
non-bulk copies; their only memory footprints are four aligned global output
words per lane. Shared byte writers have TMA origin, and global bytes outside
the output interval `[8192,10240)` are immutable. Output payloads retain their
arbitrary captured accumulator values. `ReplyCandidate` supplies complete
source-only candidates with independent per-lane replies and retry schedules;
tests use heterogeneous retries and arbitrary real replies without granting
memory, resource, collective or tensor admission. This isolates source memory
structure from the remaining proof that admitted arithmetic matches the spec.

`CopyGeometry` additionally classifies every actual TMA issue by its K tile,
A/B descriptor address, coordinates, shared destination and barrier, for
arbitrary completed candidates and retries. `UnifiedImmutable` retains the
model's global mixed-size-race exclusion when deriving immutable-byte
eligibility. Under that exclusion and existing causal memory agreement with
independently represented initial tensor maps/input bytes, `CandidateInputs`
derives descriptor and full TMA payload agreement for any well-formed completed
candidate. All copied source bytes are in bounds and outside the output region;
there is no caller zero-fill premise. Tests use source-complete heterogeneous
retries with hostile A/B bases and real payloads, reject their memory admission
and fabricated input RF, and integrate the rules with the independent
arbitrary-data memory witness. These input-value rules retain global mixed-size
exclusion until descriptor admission is established. Resource/native operand
publication and tensor arithmetic remain obligations; the rules do not imply
full-Pre correctness or hardware encoding.

`CandidateRegions` now derives mixed-size-race exclusion for every well-formed
completed candidate under the existing TMA descriptor agreement. It classifies
ordinary output, TMA data/descriptor and native operand footprints for arbitrary
RF, histories and cluster scope. `HopperStageRegionRules` supplies the same
overlapping-region rule to the one-stage, constructed repeated and arbitrary
candidate proofs. `CandidateAdmission` removes a separate no-mixed-size premise
from input RF/value and payload closure, and constructs TMA components from
source/completion, descriptor agreement, causal memory and actual valid/acyclic
resource histories. It assumes neither payload agreement nor desired matrix
replies. Tests cover heterogeneous retries, wrong payload/fabricated RF without
caller race premises, independent data-memory components and an actual
source-complete alias: a one-byte TMA input read and four-byte output word
overlap when descriptor admission is omitted. That alias fails descriptor
admission; an overlapping footprint alone is not asserted to be a data race.
The descriptor premise is retained, same-size race freedom is not inferred,
and resource/native publication, reuse, tensor/observer and full-Pre refinement
remain open for arbitrary candidates.

`ReplyIndices` now locates failed/successful parity waits and MMA events through
arbitrary per-lane retry prefixes. `ReplyCollective` proves the call/mark shape
independently of captured values and retry schedules. `CandidateCollective`
extracts actual oracle/retry/trace witnesses from every well-formed completed
positive launch, and reconstructs a source-indexed 128-lane collective for
each executed tile. Lane event indices may differ while collective marks
agree. Successful waits precede their MMA by actual source program order;
failed waits cannot observe any copy's completion. The TMA-ready rule derives
the collective and post-wait source order, retaining actual valid-history
completion observations and byte/operand location matching as obligations.
Tests include heterogeneous retries with arbitrary real outputs, all lane
coverage, failed-wait rejection, independent data candidates and a complete
two-tile producer whose three failures move success/MMA events to 11/16.
This is source collective reconstruction, not native-control/tensor admission
or proof of resource observations for arbitrary histories. Shared publication,
reuse, arithmetic, observer and full-Pre refinement remain to be connected.

`MbarrierRetries` and `TmaRetryErasure` prove failed-wait stuttering and
retained-entry protocol-prefix, phase/lifetime and completion-observation
correspondence for arbitrary admitted resource histories. Erasure is not an
unconditional admission equivalence: false waits before initialization or
after invalidation reject, and removing actual waits destroys original
inventory exhaustiveness. `RetryResourceView` proves a compact resource/control
projection of the one-tile source for arbitrary arithmetic/payload replies and
failed waits at the specified descriptor profile. Finite metadata checks then
validate both actual gate histories of the 128-lane 0/1/2-retry source, including
127 failed and 128 successful waits. Completion observations for A/B at every
lane are restored from the erased skeleton and establish native publication
byte order without caller observation premises. Reinitialization tests keep
old-lifetime notifications rejected and current ones observed. These are
resource/publication components for a one-tile witness; arbitrary multi-tile
history/control construction, native reuse, memory/tensor/observer and full-Pre
refinement remain open. No actual CUDA tensor-map encoding or hardware
conformance is inferred from the compact symbolic resource view.

The repeated pipeline still needs full functional/refinement proofs over
arbitrary admitted source executions,
full-Pre correctness/nonvacuity, and allocation/lifetime/runtime/Iris
correspondence. It is a partial acceptance case. No Hopper GPU
execution or speedup is claimed; the added CTA rendezvous cost and actual
prefetch overlap need measurement. The latest [coverage ledger](coverage.md)
and [inventory](../coverage.toml) distinguish these obligations from the completed
one-phase components and keep exact paper instruction parity unconfirmed.

Arbitrary-retry TMA source identities now extend beyond the one-tile witness.
`HopperDoubleBufferReplyPrefetch` locates each initial/prefetched expectation
and A/B issue, retaining its actual descriptor, payload and query counter. Its
source-order rules place expectation before A before B, and B before the
producer's successful wait for that tile. The rules apply through the existing
source-family reconstruction to completed well-formed positive candidates.
`HopperRetryPrefetch` exercises a source-complete three-tile candidate with
heterogeneous nonzero retries, both arenas and first reuse, and rejects a stale
zero-retry issue index. Source order does not establish memory visibility or
completion. Multi-tile resource histories, native reuse/RF, tensor/observer and
full-Pre correctness remain open; this adds no TTGIR frontend or GPU evidence.

`HopperDoubleBufferRetryPhases`, `RetryPhasePrefixes` and `RetryObservations`
now construct multi-phase resource histories retaining all actual failed waits.
For arbitrary completed positive source candidates, existing descriptor
admission supplies actual notification counts; every constructed entry has an
actual resource origin, and protocol execution and current A/B observations
are proved for every lane and phase. Full phase/lifetime stamps reject old
notifications even when parity repeats. The three-tile heterogeneous-retry
fixture checks both arenas and first reuse with 1030/516-entry histories.
These are constructed-history observation rules: unique origins, inventory
exhaustiveness/permutation, source ordering and control admission remain open.
The new histories are not yet HistoryValid/CompletionObserved witnesses or
full-Pre/memory/tensor/observer correctness results.

The constructed arbitrary-retry histories now have full `HistoryValid`
proofs. `RetryResourceCases`/`RetryResourceTraceCases` classify every actual
resource event, including failed waits. `RetryResourceMembership`,
`RetryResourceIdentities` and `RetryResourceUnique` prove both membership
directions, distinct source/transfer identities, origin uniqueness and actual
inventory permutations. `RetryResourceOrder` uses source-index intervals and
the reusable `TmaSourceOrder` pairwise rule to establish source order.
`RetryResourceAdmission` then derives actual A/B `CompletionObserved` for every
executed tile and lane under the existing source/descriptor premises. The
three-tile nonzero-retry admission fixture proves its own descriptor agreement
and all history fields, and rejects missing waits, duplicate origins and
reversed source order. These resource witnesses do not yet establish combined
control acyclicity, native memory/RF and reuse, tensor arithmetic, final output
refinement or fully admitted completed-launch existence.

`RetryNativeLocations` and `RetryNativePublication` now connect each actual
A/B copy to source-indexed native operand locations for arbitrary finite
retries and repeated tiles. Admitted completion observations derive TmaReady,
native publication and ByteOrder for every operand byte. The generic
`UnifiedNativeWriter` rule also derives an actual source-produced writer byte;
it does not assume captured operand values agree with that byte.
`RetryNativeCompletion` identifies actual native wait-group events, marks and
completion counts for every lane. `RetryNativeReuse` uses the producer lane's
existing native wait and subsequent source program order to prove reused-byte
order for every later tile using the same slot, without adding a kernel wait.
The three-tile nonzero-retry tests cover publication, writer existence, native
completion, first reuse and wrong-wait/out-of-bounds rejections. Causal RF/co,
all-lane native/CTA/control legality, arithmetic and final output refinement
still require their separate proofs; these are model byte-order components.

`RetryMemoryGeometry` and `RetryMemoryPhases` now classify every actual writer
of a native operand byte in completed retry candidates, recover its A/B slot,
source tile and offset, and order all old/current/future writers.
`RetryMemoryInputs` derives mixed-size exclusion and native eligibility, then
forces RF to the current actual producer under the existing MemoryConditions;
actual written bytes must agree with the captured operand. Old/future RF and
initialization-only coherence are rejected. `RetryTensorInputs` connects this
RF to actual TMA payload/source bytes and independently represented arbitrary
real inputs, deriving native InputAgreement and MatrixStorage. These theorems
retain full memory conditions for the constructed histories. They do not yet
construct such a memory witness or close native/control/arithmetic admission.
`HopperRetryMemory` explicitly rejects the prior three-tile fixture as a memory
witness: its bits payload and realPart operands are distinct symbolic byte
representations. That fixture remains a resource/publication witness and a
memory rejection case; no floating bit-reinterpretation equivalence is assumed.

`RetryArithmetic` connects actual source call inputs/outputs to consecutive
loop checkpoints, then proves accumulation for arbitrary finite per-lane,
per-tile retry schedules. Under the existing full MemoryConditions for the
constructed histories and per-collective TensorConditions, independent global
input matrices determine the final GEMM accumulator and all actual source
output-store payloads. The instruction's arithmetic component remains explicit;
the desired GEMM output is derived by induction. All-lane control legality
and a positive fully admitted execution witness remain separate obligations.
`HopperRetryArithmetic` checks arbitrary-real source
accumulation, a nonzero three-tile result, heterogeneous-retry tensor and
accumulator components, and rejection of a fabricated first matrix reply.
Its zero-valued retry fixture remains memory-negative as described above;
component checks do not turn it into a full execution witness. TTGIR support
has been discussed as a future frontend/semantic connection; none is added.

`RetryStoreInventory` now identifies the actual output event serials in retry
traces and derives unique global writers from source execution and output
ownership. It does not impose uniqueness on the reused shared buffers.
`RetryObservedOutput` derives global observer eligibility, constructs a
compatible observer component using existing coherence irreflexivity, and
connects admitted final observations to captured source output bytes. Under
the existing memory and tensor components for the constructed retry histories,
it derives every observed GEMM specification byte; observed global bytes
outside the output region retain their initial generic-proxy values. These
are model-relative conditional refinement results, not full control/ISA,
allocation/lifetime, physical observer correspondence or admitted-execution
existence. Ten `HopperRetryObservedOutput` facts check actual nonzero-retry
store indices/bytes, unique writers, eligibility, positive observer components,
adjacent frame preservation and omitted/stale/fabricated observation rejection.
The positive observer-component fixture remains a negative full-memory case.

`RetryNativeSchedules` now derives `SchedulesAdmitted` for every well-formed
completed canonical source candidate with the existing tile-count bound,
including zero K and arbitrary finite heterogeneous retries. Source coverage
supplies all 128 actual lanes, and failed mbarrier waits/prefetch work preserve
their native fence/MMA/commit/wait sequence. `RetryNativeCases` reconstructs
every actual native signature's tile/lane/instruction and retry-dependent source
serial, with the reverse actual-event proof, exact source MMA calls and native
wait completion metadata. Matching native synchronization must refer to the
same tile/instruction; warp-local rendezvous and full aligned participation
remain distinct. Twelve `HopperRetryNativeControl` facts check actual event
indices, all aligned participants and physical-warp source PCs, and reject
cross-warp/instruction/reuse-round rendezvous, premature group completion and
missing participants. This closes the native participation component, not
combined TMA/CTA/native control acyclicity or full admitted execution existence.
The fixture's positive participation checks retain its negative full-memory
status; no arithmetic, visibility or physical-runtime result follows from
participation alone.

`RetryControlClock`, `RetryClockOrder` and `RetrySourceRank` now provide the
source-order part of a control rank for arbitrary finite heterogeneous retries.
A budget computed from all finite lane/tile retry counts bounds failed waits
inside a dedicated interval. Clock-list lengths equal actual source-event
lengths; strict block/list order then proves that every actual ProgramOrder
edge increases the source rank. Actual native instructions recover common
tile/instruction ticks plus lane offsets, and actual failed/successful waits
have checked positions, including cross-lane failed-wait order. Nine
`HopperRetrySourceRank` facts check these connections on the source-complete
retry fixture and demonstrate that directly reusing the old zero-retry serial
clock misaligns the same native instruction across lanes. This is a limitation
of that proof clock, not an invalid-kernel or execution-cycle result. The new
rank is a proof device: no kernel event, wait, visibility rule or arithmetic
semantics changes. CTA and native control edge ranks still need connection
before claiming combined ControlAcyclic.

`RetryResourceRanks`, `RetryTmaControl` and `RetryResourceControl` now connect
actual expect/copy issue and initialization/invalidation identities to that
source clock. Bounded copy-tile injectivity and A/B identity separation recover
each actual notification's role; later notification ranks accommodate every
failed wait. Every actual implicit TMA access/completion edge and every
ResourceEdge of the constructed retry histories increases the same rank as
source ProgramOrder, across both slots and same-slot reuse rounds. No kernel
event or visibility rule changes. Ten `HopperRetryTmaControl` facts include
positive actual byte-completion/resource components, ordered notifications,
1030/516-entry histories, an incompatible immediate-notification-clock example,
reverse completion rejection and cycle rejection for the subgraph explicitly
containing source, implicit TMA and resource edges. This subgraph excludes CTA
and native control edges; neither combined ControlAcyclic nor fully admitted
execution existence follows yet. The positive source/resource fixture retains
its known negative full-memory status.

`RetryCtaCases`, `RetryCtaTrace` and `RetryCtaControl` now reconstruct actual
initial/reuse/return CTA tags, generations and retry-dependent event identities
in both directions. Every actual CTA arrival/return edge increases the same
source/TMA/resource rank. This closes `Tma.ControlAcyclic` for positive-K source
families with arbitrary finite heterogeneous retries and their constructed
resource histories; source reconstruction supplies such a control witness for
every source-well-formed completed positive-K candidate. Twelve
`HopperRetryCtaControl` facts check actual indices, generations and all-lane
edges, reject cross-generation/barrier and reverse paths, and construct a
positive complete `TmaComponents` fixture with independently proved constant
bits-zero payload agreement. Its known negative full-memory status remains.
`Unified.ControlAcyclic`, including native arrival/rendezvous/operand/completion
edges, and fully admitted execution existence are still open. The zero-K
control branch, allocation/lifetime and runtime/Iris correspondence also remain
open; no new hardware or numerical-equivalence result follows.

`RetryClockGaps`, `RetryNativeRanks` and `RetryUnifiedControl` now close full
`Unified.ControlAcyclic` and `ControlAdmitted` for positive-K source families
with arbitrary finite heterogeneous retries and their constructed histories.
Every actual source clock is regular or a bounded failed-wait clock, yielding
a lane-independent gap before native arrival. Actual source signatures align
warp-local rendezvous ticks, and actual MMA groups/native waits bound every
operand completion edge. The same rank now increases across source, TMA,
resource, CTA, native arrival/rendezvous, operand issue and completion edges.
Source reconstruction supplies a control witness for every source-well-formed
completed positive-K canonical candidate. Fourteen `HopperRetryUnifiedControl`
facts check actual events, positive joint TMA/control components, mixed
TMA-to-native publication paths and reversed publication/completion/rendezvous
path rejection. This is construct control, not full memory/tensor admission:
the fixture retains its known negative full-memory status. Positive fully
admitted execution existence, zero-K control, arbitrary admitted-history input
characterization, allocation/lifetime and runtime/Iris correspondence remain
open. No source wait, memory-visibility rule or numerical semantics changes.

`RetryDataQueries`, `RetryDataOracle`, `RetryDataTensor` and `RetryDataTma` now
construct a separate independent-data source family for arbitrary real input
tiles and arbitrary finite heterogeneous retries. Pure source query accounting
proves unique native/copy tile roles and failed/successful wait separation.
The oracle computes matrix replies from the input recurrence. Actual TMA bytes
agree with independently represented global inputs, and existing TMA, unified
control and tensor components hold together on this family. Standard mathematical
choice selects only already-proven unique bounded Nat metadata, never a desired
real result. `RetryDataReads` constructs explicit RF: initial memory for global
data/descriptor reads and each actual current TMA producer for native operands.
Every actual read has checked source-value agreement without a memory-admission
premise. Twelve `HopperRetryData` facts include a nonzero three-tile result of
96 and reject bits payloads and stale reused-tile RF. This removes the old retry
fixture's known bits/realPart mismatch; that negative fixture is retained.
The new RF still needs causal/coherence/atomicity/SC-per-location and compatible
observer witnesses before claiming a fully admitted retry execution. Zero-K
control, allocation/lifetime and runtime/Iris correspondence remain open.

`RetryDataMemoryRank`, `RetryDataReadConflicts`, `RetryDataCausal`,
`RetryDataCoherent`, `RetryDataAtomicity`, `RetryDataSC` and `RetryDataMemory`
now derive full existing `MemoryConditions` for the independent-data retry
family. Only already-justified byte edges refine to control paths. Actual RF,
causality and communication edges increase the same checked rank; current
producer selection, immutable global reads and ordered shared reuse derive
latest-source, coherence, atomicity and SC-per-location fields. No memory
admission or desired result is a construction premise. `RetryDataExecution`
constructs a compatible final observer and combines the same source/TMA,
unified control, memory, all tensor and observer components. Its parameterized
execution-existence theorem retains `family.schedules = schedules` for every
given finite heterogeneous schedule and positive K under the existing bound.
Observed matrix bytes satisfy the independent GEMM specification, with the
existing output/adjacent-frame observation domain. Fourteen
`HopperRetryDataMemory` facts check positive joint components, actual same-slot
coherence and from-read order, communication-cycle rejection, observed nonzero
result 96, frame bytes and invalid coherence/observer cases. This closes joint
positive-K execution existence in the current model, not physical ISA/runtime,
allocation/lifetime, IEEE or Iris correspondence. Zero-K control and
characterization over all arbitrary admitted histories remain open.

`ZeroSource` and `ZeroInventory` now reconstruct the actual rich event lookup
and event-ID permutation for every source-well-formed completed zero-K
candidate, including arbitrary oracles and trace order. `TmaEventLookup` and
`UnifiedEventLookup` supply reusable control/access/collective transport;
resource history transport separately checks event-ID multiplicities. Equal
lookups alone cannot establish inventory exhaustiveness. `ZeroControl` derives
all actual zero-K resource/TMA and full unified control components, and its
common control-existence entry covers zero and positive bounded tile counts.
`ZeroMemory` proves absence of actual reads/native/TMA, unique actual output
writers and full memory conditions for arbitrary initial bytes. `ZeroExecution`
combines the same source, resource, control, memory and observer components,
preserving every output store. All observed matrix bytes are zero; frame bytes
outside the output remain initial on the observer domain. The zero-K output
refinement also admits arbitrary already-admitted RF/co/histories/cluster and
observers. Sixteen `HopperZeroExecution` facts include reversed traces and
arbitrary oracles, positive joint components, output/frame checks and a duplicate
trace whose lookup remains equal but whose repeated inventory invalidates source
and history admission. Invented notifications and omitted/stale observations
are rejected. Zero-K is closed in the current model; positive-K characterization
over arbitrary admitted histories, allocation/lifetime and Iris/runtime/physical
observer correspondence remain open. No GPU or IEEE claim follows.

`UnifiedHistoryControl` now turns actual control paths into necessary order in
any admitted resource history, using exhaustive origins and control acyclicity.
`RetryHistoryPaths` and `RetryArbitraryHistory` apply it both to expect/own-TMA
notification order and to every lane's successful wait before a later same-slot
expect, through the actual CTA return path. Prefix bounds follow without an
equality to the constructed history. `TmaHistorySwap` preserves inventory counts
and source order under separately checked protocol admission. Twelve
`HopperArbitraryHistory` facts include an actual three-tile, 128-lane swap that
passes these resource checks but is rejected by unified CTA control. A true
parity wait alone does not identify its intended completion phase. Exact phase
stamps, publication and positive-K output refinement over arbitrary admitted
histories remain open; the new ordering bounds do not close them.

`MbarrierAccounting`, `MbarrierPrefixAccounting`, `MbarrierTransactionCounts`
and `MbarrierResting` derive conservation laws from the original protocol,
including multiple arrivers, zero-byte arrivals, signed completion debt and
counter reset on reinitialization. `TmaPrefixAccounting` connects them to actual
history prefixes. `RetryPrefixAccounting` proves the one-init(1), 2304-byte
arrival and 2048/256-byte completion inventory properties for every actual
history permutation. Live prefixes satisfy `phase + 1 = arrivalCount + pending`
and `tx = 2304*arrivalCount - 2048*completionCount(2048) -
256*completionCount(256)`, with `pending <= 1` and lifetime stamp 1. No canonical
history order or readiness premise is needed. Nineteen facts check operational
edge cases, arbitrary actual waits/notifications and an old-phase successful
wait with positive next-phase credit. Exact tile phase attribution, matching
nonnegativity and all-history completion/publication/output refinement remain
open; the conservation and lifetime equations do not imply those properties.

`TmaMatchedCounts` and `RetryMatchedPrefixes` now derive completion-count bounds
from injective, prefix-present actual expect parents, including multiplicities.
Transaction credit is consequently nonnegative in every admitted live prefix.
`MbarrierPhaseMonotone`, `RetryArrivalPrefixes` and `RetryExactPhases` combine
single-lifetime monotonicity, actual source order and CTA reuse exclusion to
identify every lane's successful wait at phase `tile/2+1`, pending 1 and zero
credit. `RetryMatchedNotices` and `RetryArbitraryObservations` derive own-notice
order, phase `tile/2`, lifetime 1 and the existing `CompletionObserved` relation
for arbitrary admitted histories. A completed-positive-candidate entry obtains
the source family from existing TMA/control components. Twenty facts include
arbitrary real inputs/histories, an existing joint execution witness, rejected
old/future notices and two actual resource-valid histories that control rejects:
a late peer wait and an early notice producing negative debt. The constructed
history restriction is removed for completion observations. Full publication/native RF/input/output refinement over arbitrary histories,
and allocation/Iris/runtime/physical correspondence, remain open.

`RetryPublicationInterface` now supplies `NativePublicationFacts` from both the
existing constructed-history proof and arbitrary admitted completion histories.
`RetryPublicationPhases`, `RetryPublicationMemory` and `RetryPublicationTensor`
consume that interface to derive writer phases, native eligibility/current RF,
actual input bytes and source accumulation. Three existing payload/storage
rules are generalized over history parameters without new premises.
`RetryArbitraryOutput` derives its publication interface from existing TMA/control
components and proves positive-K GEMM output/frame refinement for arbitrary
admitted histories, RF, coherence and final observers. The existing tensor instruction semantic component remains explicit; a completed
source entry
reconstructs the family and exposes that obligation. Fifteen facts cover real
inputs, heterogeneous retries, an existing joint execution witness, nonzero
result 96, frame preservation and rejected stale/future/initial sources,
initial-only coherence, incorrect operand bytes and a corrupted observer.
Together with the prior zero-K result this removes the chosen-history restriction
from current-model input/output refinement. Allocation/in-flight ownership,
Iris/event/runtime adapters and the unified acceptance audit remain open;
physical ISA/IEEE/GPU or performance claims do not follow.

`Unified.ExecutionComponents` now packages source/TMA completion, full control,
full memory, actual MMA coverage/tensor semantics and the completed observer.
`TensorAdmission` proves that every actual source-matched collective has exactly
one tile's calls and sources, and that this candidate-wide tensor component is
equivalent to the earlier per-tile condition. `HopperDoubleBufferExecution`
provides one source-independent `execution_refines_gemm` entry for zero and
positive bounded K, and `gemm_execution_exists` supplies compatible complete
witnesses while retaining each given positive-K retry schedule. The same entry
proves model matrix equality for two complete executions with different retries.
Sixteen facts cover both branches, distinct schedules, actual MMA coverage,
nonzero output/frame bytes, rejected mixed-tile cohorts, orphan MMA coverage,
incorrect arithmetic for any memory, and missing/corrupted observers. Generated
proof projections are audited alongside authored theorems. This closes the
unified current-model entry; ownership/Iris/runtime links and the remaining
paper acceptance audit are still open, with physical GPU/numeric correspondence
outside the proved result.


The prepared-plan completion bridge now interprets actual 128-byte tensor-map
reads, TMA source/destination bytes and native operand reads in a finite
control-prefix relation. Each mapped FIFO ticket can advance only with its own
source-matched completion in that prefix. Successful acquisition that removes a
mapped loan implies every associated actual use has occurred; pending uses keep
their loans across acquisition of an older event. The same rule covers TMA and
native work, and rejects a counter-only device advance without actual completion.
This is a checked coupled model relation with a fixed ticket/work plan. Dynamic plan construction, physical allocation and
buffer/location binding, coupled Iris interpretation and CUDA runtime refinement
remain open. It does not establish scalar-cell/byte-value correspondence. The
seventeen regression facts include actual source-derived uses and completion
certificates, early-acquire rejection and old-event loan retention. Structural
rank cuts are not asserted to be reachable executions.


Reachability of finite prefixes is now proved:
`PrefixExistence` derives one-node reachability of any finite valid ranked cut.
`ControlInventory` covers all actual source, tensor-copy and native operand
nodes; `ControlPresence` checks control endpoints against actual source/resource
inventories. Full actual and bounded actual cuts are reachable, with bounded
cuts explicitly excluding absent nodes. `HopperDoubleBufferProgress` applies
this to positive bounded K and arbitrary finite heterogeneous retry schedules.
Sixteen facts include actual complete and unfinished prefixes, TMA/native
completion, prepared prefix/device/acquire/reclaim runs, protocol invariants and
rejection of a ghost-node prefix. These close positive prefix/protocol
nonvacuity for the prepared logical client. Physical buffer/command binding,
byte-value correspondence, dynamic plan construction, Iris and runtime
refinement remain open.


`RegionLoans` binds modeled byte regions to mode-correct logical loans;
`RegionComposition` renames logical IDs/tickets while preserving exact region,
work and mode coverage. The aggregate positive-K plan now uses eight separated
buffers and six logical tickets per tile for both A/B TMA copies and native
operand reads. Every actual `Progress.Use` is classified from the source and
covered without a caller-selected work scope. A completed-candidate entry
reconstructs the family and produces the layout/mapping/coverage certificate.
Actual full prefixes discharge every mapped completion guard, and prepared-plan
scripts lift one real protocol command per coupled step.

Twenty-three facts check a publicly prepared three-tile client with eighteen
commands and twenty-four live loans. All pending actual async regions are
protected under every coupled finite run; a complete coupled execution returns
every loan and permits reuse. An old event returns tile-zero loans while retaining
future tile-two loans on the same slot. Invalid stream/zero tickets, B/A copy
confusion and missing B-descriptor coverage are rejected. Coverage and completion
rules are parameterized by bounded positive tile count and heterogeneous replies;
public preparation and initial borrowing were first checked for this
three-tile client. They now have the parameterized proof described below.
Ordinary/resource source uses and zero-K source ownership
integration, dynamic layouts, real allocation/
command and byte-value simulation, and coupled Iris/runtime refinement remain
open. Modeled regions are not CUDA allocation certificates.


`Async.Preparation` proves public single-stream issue readiness from the actual
borrow/enqueue interpreter, with live buffers and stream/sequence-bounded loans.
`HopperDoubleBufferPreparation` builds the six-command-per-tile plan for every
finite tile count and any eight initial scalar values. Event IDs are indexed
and duplicate-free; the final event names exactly ticket `(0, 6*tiles)`.
`HopperDoubleBufferPreparedLoans` derives every initial region loan from the real
queue invariant and its exact command position, removing an externally supplied
`Borrowed` premise. Pending async reclaim/overwrite rejection is now generic on
the bounded positive-K source family and every coupled finite execution.
Eighteen facts check parameterized results, zero work, a four-tile concrete
client, a 90-tile symbolic instantiation beyond former fixed event IDs, exact
frontiers and duplicate-event rejection. The generic coupled drain/return witness is now checked as described below.
Ordinary/resource ownership and the existing Iris/runtime/value boundaries
remain open; zero protocol preparation does not establish zero-K whole-kernel
ownership.


`Async.Drain` now constructs the complete FIFO execution and final acquisition
for any valid prepared no-wait queue. It proves that real device execution
preserves alive/loan metadata and events while allowing data values to change;
a successful final acquire clears every bounded ticket loan. The aggregate
request language is proved to contain no wait commands. `HopperDoubleBufferLoanReturn`
therefore proves public prepare/drain/acquire success for every finite tile count
and arbitrary eight scalar values, with empty loans, live buffers, exact
completion counters and successful subsequent write/reclaim. On the bounded
positive-K source family, this lifts through the actual reachable prefix and
all mapped TMA/native completion guards into a parameterized complete coupled
run. Pending async guards also allow arbitrary resource-history environments.
Sixteen facts include zero/four-tile executions, both slots' data updates, early
and one-step-short acquisition rejection, generic data-family coupling and a
self-wait counterexample that satisfies the protocol invariant but cannot drain.
This proves a finite no-wait model execution, not physical scheduling fairness,
GPU/runtime termination, ordinary/resource ownership or byte-value refinement.

`Async.AccessLifetime` adds explicit read/write resource reservations through
public `Action.access` and `submitAccess`. Write-only output or barrier storage
can be reserved without inventing a copy source. Successful submission derives
the exact ticket/mode loan and blocks host writes/reclamation. Any finite valid
mixed use/copy/access request list has a constructed public preparation, record,
FIFO execution and final acquisition with all loans returned. Nineteen checks
cover independent-stream conflicts, ordered same-stream reservations, partial
and premature acquisition, explicit dependency waits, and write-only storage.
These reservations protect allocation lifetime; overlapping ordered queue
entries do not own simultaneous active byte permissions. Opaque access tasks
leave abstract values unchanged. Their source-level ordinary/resource connection is extended below; physical
allocation/value simulation and coupled Iris/WP remain open.
This adds no TTGIR frontend or compiler-correctness claim.

`Hopper.KernelUse` records actual ordinary byte accesses and separate opaque
mbarrier storage uses, including source operations and TMA notifications.
`Work.kernel` requires source termination and the full actual control prefix;
existing TMA/native completion remains finer grained. No resource contents are
fabricated as ordinary byte values. `KernelLease` constructs public mode-tagged
reservations, derives indexed loans and rejects host modification/reclamation
while a covered actual operation is pending. A chosen complete actual prefix
then permits real FIFO execution and acquisition with every loan returned.

`HopperDoubleBufferKernelOwnership` covers ordinary output bytes and both
mbarriers' storage spans for completed zero-K and bounded positive-K source
families. Zero K still initializes and invalidates both barriers: its public
client needs two modeled buffers (output and barrier storage), with no unused
descriptor/input buffers. Twenty checks include actual source stores and all
barrier bytes, source-coupled complete lifetimes for zero/positive data families,
pending source guards, omitted barrier coverage and premature acquisition.
The combined ten-region modeled layout and protocol are now checked below;
physical allocation/launch correspondence remains open. Coupled Iris byte
ownership/WP, actual allocation/value/runtime correspondence and the full case
and instruction audits remain open. No new GPU or performance result is added.

The `HopperDoubleBufferWhole*` modules now give one public positive-K lifetime
client for ten separated modeled regions: two descriptors, two inputs, four
shared operand buffers, output storage and mbarrier storage. Existing async
tickets retain their work and source-matched completion rules; the two appended
root tickets require whole-kernel completion. Actual ordinary/resource uses
and async uses share one exact-mode coverage predicate. Exhaustive actual-byte
classification also covers every read/write inventory node, with source-proved
absence of non-bulk copies; resource records cover their complete storage spans.
Public queue construction derives every loan and pending source-use rejection
for both host writes and reclamation. A chosen complete actual prefix followed
by FIFO execution and the final acquire returns every loan, with subsequent
write/reclaim possible for all ten regions. The original two-buffer source-zero
client remains available without unused descriptor/input buffers.

Twenty-one checks include arbitrary-data source coupling and actual inventory
coverage, symbolic generic preparation/return, four-tile 26-command/34-loan
instances, exact root tickets, missed-root completion and early-event failures,
and alias rejection. These are source/control/protocol lifetime facts; physical
allocation/launch/command and byte-value simulation, active byte ownership and
coupled Iris/WP remain open. No new GPU or performance evidence is added.

`Hopper.ByteAuthority` adds active access authority keyed injectively by actual
address space, CTA and byte address, with a separate control key. It checks
actual source uses and control readiness before claiming an available byte.
Retiring a source node requires all its actual byte uses to be held and returns
those claims while performing the existing source/control advance. Protocol
actions cannot bypass that requirement. Active claims remain actual and pending
through every finite authority execution; the ten-region public lifetime guard
then prevents host writes/reclamation of their containing region. Generic
`Progress.UnifiedUse` now lives in the Hopper layer rather than the GEMM case.

`Iris.ByteAuthority` interprets this authority heap through native GenHeap. Its
local claim WP consumes the source/control fragment and exactly one actual
byte's full authority, preserving unrelated fragments. Exclusive duplication
is rejected, and ordinary fractional splitting describes the same authority
cell. Closed one-step claim adequacy initializes the actual supplied map with
GenHeap instead of assuming arbitrary heap names. Twenty checks use actual
zero-K mbarrier source bytes and reachable rank cuts, reject duplicate/missing
authority and wrong modes, separate spaces/CTAs/control keys, and show omitted
barrier bytes prevent retirement. The baseline claims exclusively even for
reads. Authority cells contain permission metadata, not GPU byte values.
The subsequent finite-footprint and acquisition layers below provide per-node
pool construction and multibyte acquisition/return WP. Whole-kernel Iris
execution/adequacy, physical allocation/runtime and weak-memory value refinement
remain open.

Write authority now authorizes read demands as well as writes, allowing one
write grant per RMW byte while preserving the exact source-use/claim checks.
Read authority cannot authorize a write.

`Hopper.ByteFootprint` checks finite, distinct, source-sound and complete access
lists; supports RMW permission dominance; and proves that clearing a complete
list equals source-node retirement while framing every unrelated cell. Its
frame certificate is derived from supported/active claims reached from an
available pool. `ByteSourceFootprints` exhaustively classifies actual ordinary
and mbarrier source-event byte uses. No guessed role or assumed frame update
replaces these lookups.

`Iris.ByteRetirement` provides a native local multibyte retirement WP and closed
retirement adequacy through GenHeap initialization. It consumes precisely the
listed full byte fragments and the exclusive controller snapshot, returns the
listed available fragments, and advances the original source control. The
controller snapshot now records the complete authority state, so GenHeap
validity supplies exact current metadata. Knowing that metadata does not own
other byte fragments; unrelated byte fragments still frame the transition.
Twenty-six checks include a real completed source RMW, one write grant per
read/write byte, rejection of read-only RMW authority, complete eight-byte
mbarrier retirement, missing-final-byte rejection, and native retirement WP/
closed adequacy. The acquisition layer below composes this retirement rule with
actual claims from available authority. The inventory/source-script layers below
lift complete bounded source executions. These are authority metadata proofs;
GPU value/runtime refinement remains open. No new GPU or performance evidence
is added.

`Hopper.ByteAcquisition` constructs finite actual-byte available pools and
executes each checked claim before source retirement. Successful acquisition
requires initially available, distinct physical keys; grants preserve the source
cut. Complete retirement restores the initial authority map. The generic rules
also allow unrelated active claims under the existing supported/active
invariants. `Iris.ByteAcquisition` proves each physical update through native
GenHeap, composes the real action script with retirement, frames arbitrary Iris
resources and initializes the heap for closed adequacy. It assumes source-ready,
sound and complete footprints, and distinct available requested bytes; it does
not assume that their authority was already held.

Twenty-seven checks exercise actual mbarrier and unsplit RMW source nodes,
eight- and four-byte claim/retirement scripts, missing/duplicate byte rejection,
no source advancement during claims, retirement advancement, exact pool return,
an unrelated byte frame and closed adequacy. Nine and five count authority
actions, not hardware instructions. These are per-source-node authority
metadata results. The source-script layer below lifts finite bounded source
executions; kernel/value/runtime refinement and remaining paper/case audits
stay open. No new GPU or performance evidence is
added.

`Hopper.ByteInventory` normalizes a finite location inventory into a distinct,
source-sound access list for each node. It chooses a write grant when the actual
node writes a byte, otherwise an actual read grant, and omits unused locations.
Completeness follows from checked bounds on actual uses. This is noncomputable
proof-level selection, not a CLI footprint extractor. Duplicate catalog entries
normalize safely; duplicate actual claim requests remain rejected.

`Hopper.ByteExecution` lifts every finite coupled source/host/device execution
with bounded uses into real checked byte claims and retirements. Each completed
node restores the fixed initial pool, deriving subsequent availability. Existing
Hopper ten-region coverage supplies a complete inventory for descriptor, TMA,
native, ordinary and mbarrier storage uses.
`HopperDoubleBufferByteExecution` applies the lift to the entire bounded
positive-K source plus its original public drain/acquire execution. It adds no
physical wait or hardware scheduling claim.

`Iris.ByteSourceExecution` uses a restoring accessor to retain every heap
fragment across source nodes, composes each real claim/finish script through
continuations, and proves full-source-prefix native GenHeap WP and closed
adequacy. `HopperDoubleBufferByteIris` constructs this witness for the actual
parameterized positive-K source family. The source prefix keeps the existing
prepared protocol unchanged. The combined protocol layer below now adds native host/device steps to this
source-authority prefix. GPU byte-value and runtime refinement remain open. Twenty-six checks include RMW mode
merging, unused/omitted locations, complete finite-source witnesses, exact source
cuts, duplicate-node rejection, complete pool return and cross-node pool reuse.
All seven required cases remain partial and exact paper 81-form parity stays
unconfirmed. No new GPU execution, performance or logits/token result is added.

`Hopper.ByteProtocol` executes the original prepared-plan host/device commands
while checking each device step against its next mapped source work. It retains
original FIFO/dependency checks and error codes. Source-completion checks are proof-level Lean semantic
predicates. `Iris.ByteAuthority.Context`
fixes the plan and cluster scope for every action; protocol actions carry only
a command. Source claims/finishes retain their existing checks.

`Iris.ByteProtocol` updates the exclusive controller snapshot through native
GenHeap and frames every byte-authority fragment. Continuation rules compose
source claim/finish scripts with actual device steps and final host acquire,
retaining the complete pool and arbitrary frames. Failed actions preserve the
current controller and frame; this is not a rollback claim for earlier successful
actions. Every successful native action/script projects to the original coupled
source/protocol relation. The Hopper companion proves a parameterized combined
run and closed native adequacy, and derives rejection of host write/reclaim
from active byte claims in native prefixes using the existing public loan rules.

Twenty-nine checks use an actual RMW source and the actual Hopper data family.
They distinguish FIFO readiness from source completion, device completion from
loan return, and source completion from queued stream dependencies. They retain
errors for early acquire/reclaim/write, invalid stream/event, duplicate record,
empty queue and an omitted final device step; cross-stream waiting succeeds
only after its dependency finishes. Six strict false assertions against the
native command interpreter are individually refuted in addition to all 660
existing assertions.

Combined adequacy starts from the original publicly prepared state; its
preparation has a separately checked interpreter run. Native preparation,
physical allocation/commands, GPU byte values/RF/coherence and runtime refinement
remain open. Controller scalar buffers and byte-owner cells are protocol and
permission metadata. These changes add no GPU execution, performance or
IEEE/logits/token result; all seven cases stay partial and exact paper 81-form
parity stays unconfirmed.

`Hopper.ByteContents` couples owner and optional symbolic byte content at each
actual location key. Before completing a memory event it checks the existing
permission footprint, actual access-use linkage, completeness of all accesses
sharing its control node, and every emitted read against the local contents.
It applies actual emitted write payloads and returns authority in one event
transition. Claims preserve values, untouched keys retain contents, and erasure
projects successful steps/scripts to the existing byte-authority model.
RF/eligibility agreement can establish the read checks when an RF-compatible
local view has been proved. A global SC realization of arbitrary weak-memory
executions is not supplied or assumed.

`Iris.ByteContents` interprets the combined payloads with native GenHeap and
initializes the actual supplied map for closed script adequacy. Claims have
local cell/controller rules. The earlier general event/script value helpers consume the complete interpreted
heap fragments per event. The local interfaces below consume only the actual
listed byte fragments and the controller. Individual
claims and the final memory event remain separate physical language steps.
This is not a whole-script OwnP/atomic replacement.

Thirty-six checks connect a real completed RMW source to an available four-byte
heap, four actual claims and one indivisible modeled RMW update. Read values
come from its existing admitted memory execution and race-derived eligibility;
final contents agree with its actual write and observer. Native postconditions
expose the returned counter fragment containing one. Wrong/absent old data
fails despite identical full permissions; three-byte footprints and repeated
source completion fail, and unrelated contents remain unchanged. Two strict
finite-value refutations supplement all 666 existing rejection assertions.

This establishes an event-local modeled-value witness. Its RF/view realization
is not proved for arbitrary weak source executions; the earlier Hopper
source/device/acquire native pipeline still models permission/protocol metadata.
Composing these value cells with that pipeline, native preparation,
compiler/runtime/physical allocation and the
remaining original case/instruction obligations remain. Symbolic real fragments
retain their existing real-number abstraction; they are not IEEE storage bytes.
No new GPU execution, performance or logits/token result is claimed. All seven
required cases stay partial and exact paper 81-form parity stays unconfirmed.

`Iris.ByteContentsFootprint` provides native local value-completion and
continuation rules consuming only the actual access list's full payload
fragments plus the controller. Each listed cell is updated through native
GenHeap; unrelated cells and arbitrary Iris frames are retained. The update
store is proved equal to the original checked event transition. Acquisition
continuations construct each real claim from available payloads and compose
with local completion. Closed adequacy initializes the actual map and extracts
only the required fragments. These interfaces do not use the earlier
`allPoints_update`/whole-map update helper.

`Hopper.ByteContentsFrames` proves that adding an available cell outside a
complete footprint preserves every original source/permission/read-value check.
This uses actual read-use linkage and existing footprint coverage, including
correct RMW write dominance. The extra cell's payload is preserved. Twenty
checks exercise the actual RMW's local completion and full available-to-returned
cycle, a real extra cell containing 99, a fractional frame for that same heap
cell, native fragment extraction/splitting and closed adequacy. The counter
remains one; invalid old values and partial atomic footprints remain rejected.
Two strict counter/frame refutations supplement all 668 previous assertions.

RF/proxy-view realization for arbitrary weak source executions, whole-source
value/native protocol composition and runtime/compiler/allocation correspondence
remain open. The existing full-map helper is retained as a baseline; the local
interfaces remove that ownership requirement for these checked event/cycle
rules. All seven required cases stay partial and exact paper 81-form parity
stays unconfirmed. No new GPU, performance or IEEE/logits/token result is added.

`Hopper.ByteContentsPhases` relates successful completion to actual emitted
write values and proves that claims and nonwriters preserve values.
`Iris.ByteContentsPhases` preserves valid source cuts across successful scripts.
Its phase rule derives value preservation from the existing per-byte writer
partition: another writer is the current producer, precedes it, or follows the
reader. Closed cuts and checked freshness exclude interference between those
points. This does not require a global SC interpretation of PTX.

`Kernels.HopperDoubleBufferByteContents` derives that partition for the
parameterized double-buffer source and connects a successful script's reader
view to its admitted RF source and actual operand bytes. This theorem requires
the script as a premise. The control-only extension below supplies native
arrival steps; the complete source value witness is supplied by the later
`ValueFrontier/ValueExecution` construction below. Ten checks cover actual RMW value effects and cut validity, claim
and nonwriter preservation, allocated spare contents, completion freshness,
and the phase premise on both real-data arenas and their reuse. General weak
view realization and whole-source native/value composition remain open.

`Hopper.ByteContentsControl` adds a checked control-only action. The original
empty-footprint authority finish still checks presence, freshness, all source
predecessors, absence of byte/resource uses and absence of held fragments for
this node. An extra guard excludes every actual memory effect mapped to it,
including effects outside the authority use relation. Success advances only
the source cut, preserves every cell/value and projects to the original
authority relation. Native arrivals have no uses/effects by construction;
actual source presence and readiness remain checked.

`Iris.ByteContentsControl` provides controller-only native GenHeap update and
continuation rules, retaining all byte fragments in arbitrary frames. Existing
script projection, domain, monotonicity, validity and phase-value proofs now
cover this action. `Kernels.HopperDoubleBufferByteControl` constructs actual
arrival steps at reachable ranked source cuts for the parameterized bounded
positive-K family. Eighteen facts instantiate the real-data three-tile family,
including every lane/native position, a real byte containing 99, its fractional
frame and closed heap adequacy. RMW reads/writes, opaque mbarrier storage uses,
invented arrivals, missing real fence predecessors, repeated arrival and
discarding a held fragment are rejected.

These local control/value witnesses start from a proved reachable source cut.
The later construction below also supplies all preceding memory effects from
initial memory. Full native/value/protocol composition, physical allocation/runtime
and compiler correspondence remain open; all seven cases remain partial and
exact paper 81-form parity remains unconfirmed. No new GPU, performance or
IEEE/logits/token result is added.


The generated `byte_value_pipeline.ptx` helper now exercises a complete
store-to-load value script. The source binds `Ptr` to model byte address 64 and
allows any u32 parameter and an independent load reply. Actual unified source
production, completion, launch coverage and the two-event access inventory are
checked. Four real write claims and a checked write are followed by four real
read claims and a checked read, starting with an available initialized four-byte
pool. Source register correctness quantifies over every successful value script:
the full reply must equal the stored parameter modulo the PTX u32 representation.
Wrong replies pass all permission checks and then return `readMismatch`,
including replies whose low two bytes match but upper bytes differ.

`Iris.ByteContentsSequence` provides actual claim/cycle runs, local cycle
continuations and returned-pool/frame facts. Two native local cycles compose
with arbitrary Iris frames; closed adequacy initializes the supplied real
GenHeap map. The earlier phase-view theorem now has an actual writer/claim/
pending-reader script witness: its selected-writer RF view is derived from
actual byte effects and unique-writer inventory. Sixteen checks exercise a
full four-byte word, u32 wrapping, universal successful-reply correctness,
closed native heap execution, wrong data after all claims and an incomplete
reader footprint. Four strict refutations preserve all previous 670 assertions.
All 31 PTX fixtures are included in source regeneration and assembly checks.

The helper's full `Unified.MemoryConditions` witness is supplied below.
Arbitrary weak-memory SC realization remains open. Physical allocation,
compilation and GPU/runtime execution remain separate; its unused load may be
optimized away during assembly. No new GPU execution, performance or logits/token claim
is added. Full Hopper value/native/protocol composition and the original seven
partial cases/instruction inventory remain open.


`ByteValuePipelineMemoryOrder/Memory` constructs the full existing-model
memory witness for this generated source family, together with actual source,
TMA/resource and native control components. Source-derived ranks prove control,
byte-order and communication acyclicity; actual same-thread footprints derive
race freedom and eligibility. Causal agreement, initialization/no-stale/no-future,
coherence, single-copy atomicity, RMW atomicity and SC-per-location are checked.
The program has no atomic instruction; its atomicity fields do not extend
atomic instruction coverage.

`ByteValuePipelineMemoryLink` derives the actual store as RF source for every
admitted RF/co and independent load reply in this family. The real writer and
read-claim script then realize that RF view, and the original read-value checker
succeeds. Full-word register correctness, the ten-action native script, local
Iris WP with arbitrary frames and closed heap adequacy follow. Reply equality
and eligibility are conclusions, rather than assumed input preconditions.
The concrete full memory witness and native heap execution coexist for every
parameter, so the admitted family is nonempty.

Sixteen checks include all-RF/co correctness and native adequacy, a full word,
u32 wrapping, and rejection of missing/reflexive coherence, self/nonexistent RF
and incorrect upper bytes. A zero store/read can agree with initial-zero data
while its initial-memory RF is still rejected: data agreement alone does not
establish memory-model admission. Full Hopper source/native/value/protocol
composition and the original seven partial cases/instruction inventory remain
open. These are fixed-pointer one-thread model results; no new GPU, physical
allocation/compiler/runtime, IEEE/logits/token or performance evidence is added.

`Iris.ByteContentsFuture` establishes an invariant for pending readers: an
initial-memory read retains its initial byte, and a selected-writer read sees
that writer's actual byte once its producer completes. Source-specific control
frontiers exclude interfering writers, while permitting the current RMW's own
write after its reads. `ByteContentsNodes/Available/Source` construct actual
claim/finish cycles and checked arrivals for every reached source prefix, using
complete actual-use inventories and available allocated cells. Nonbulk copies
are excluded by an explicit source theorem because their two memory ports need
separate treatment. This does not serialize arbitrary weak PTX executions.

`HopperDoubleBufferValueFrontier/ValueExecution/ValueOutput` prove these
premises for independent represented real A/B, arbitrary initial frame bytes,
positive K up to 2^28 tiles, and finite heterogeneous per-lane retries. The
complete script starts from the actual initial ten-region byte pool. Actual
TMA producer writes supply native operand values; all source read checks pass,
and every unique output cell contains its independent GEMM specification
fragment. No successful value script or desired intermediate cell value is an
input assumption. The final pool is available, and real values erase to the
previous authority execution. Native closed adequacy uses the retained
whole-map script helper; this adds no full-source footprint-local WP.

Twelve checks cover the complete three-tile script, both arenas and reuse,
derived eligibility, final matrix fragments, native adequacy and protocol
preservation, including a nonzero 1-times-2 matrix with result 96. Even placing
the correct operand byte into an available cell cannot bypass the missing TMA
producer: the original claim still returns `authority.unready`. The new source
actions leave the host/device protocol unchanged; their protocol composition
is supplied below. Native public preparation, zero-K value scripts, physical allocation,
compiler/runtime correspondence and Hopper GPU evidence remain open. No new
IEEE/logits/token, performance or novelty claim follows.

`Hopper.ByteContentsProtocol` lifts the original prepared-plan commands into the
symbolic-byte state. Device completion retains its actual-source guard, FIFO
dependencies and original errors. `Iris.ByteContentsProtocol` combines existing
source actions with these commands in one language, projects every successful
mixed execution to the prior authority/event protocol, and supplies native
GenHeap WP and closed adequacy. Successful protocol commands update only the
controller; local rules frame every byte fragment, including fractional ones.
A checked rejection preserves the controller and its entire frame.

`HopperDoubleBufferValueProtocol` constructs the actual full source script,
device drain and final acquire from the publicly prepared protocol plus initial
byte pool. The same final state has correct real GEMM matrix fragments,
available cells, all ten returned modeled loans and native closed adequacy.
Arbitrary successful source/protocol interleavings with the complete source
cut retain the correct matrix, using a reusable actual unique-writer invariant.
Active byte claims still block host writes/reclamation through the original
source/region loan guard. Twenty checks exercise a real RMW counter, fractional
byte framing on successful and rejected commands, early/duplicate command
errors, an actual public preparation run, and nonzero three-tile GEMM with
matrix value 96 and all ten returned regions in the same execution witness.

`Iris.ByteContentsMachine` reuses the original byte GenHeap interpretation for
a supplied fixed transition with proved cell-domain preservation. Full-source
closed adequacy still uses the retained whole-map update baseline. Protocol
commands update scalar metadata; their buffers are not physical GPU bytes,
and accepted host writes/reclamation are not simulated physical byte effects.
The native public preparation construction is supplied below. Physical
value/protocol/runtime correspondence, zero-K value scripts and the original
case/instruction obligations remain open. No new GPU, performance or
IEEE/logits/token evidence is added.

`Iris.ByteContentsPreparation/PreparationExecution` runs the real public
borrow/enqueue requests and records the exact plan frontier in the existing
symbolic-byte GenHeap state. Requests require an untouched source cut, an
available byte pool and a fresh reserved event. Sealing checks the exact queue,
including resource modes, before recording its frontier. Source/device actions
are gated on that frontier. Recorded events persist through the old checked
protocol; subsequent preparation is rejected even after acquire returns loans.
Actual request/record errors are retained, and preparation does not change any
GPU byte cell. Local preparation and rejection rules frame real fractional
byte resources. These are proof-level protocol guards, not a CUDA launcher.

`HopperDoubleBufferPublicValues` constructs one native script from the initial
no-loan protocol and initial ten-region byte pool through public preparation,
actual source value execution, checked device drain and final acquire. Correct
independent real GEMM fragments, available cells, all returned modeled loans
and closed native GenHeap adequacy coexist in the final state. Arbitrary
successful full-client runs with a complete source cut have the correct matrix;
prepared-prefix active claims retain the original host write/reclaim guard.
Twenty-eight checks cover exact preparation, incomplete/wrong-mode sealing,
unprepared access, late preparation, held claims, original invalid-buffer/copy
errors, real fractional-byte framing and a nonzero three-tile full client from
initial no loans with result 96. Native preparation is closed for this bounded
client; the zero-K value construction is supplied below. Physical allocation/
value/runtime/compiler refinement and original case/instruction obligations
remain open. Full-source
closed adequacy still retains the whole-map baseline. No new GPU, performance,
IEEE/logits/token, fairness or research-novelty evidence is added.

`HopperDoubleBufferZeroValues/ZeroPublicValues` construct complete checked value
and native public-client scripts for every source-well-formed completed zero-K
candidate and arbitrary initial bytes. Actual output writes and initialization/
invalidation of both barriers retain complete byte-use inventories. The minimal
pool contains only output and opaque barrier storage, with no fabricated input
or descriptor reservations. Native preparation, actual source execution,
source-matched two-ticket completion and acquire return both modeled loans in
the same state as the correct zero matrix and available byte permissions.

`Iris.ByteContentsImmutable` preserves values at locations with no actual source
write across every client action. This proves preservation of the zero-K opaque
barrier payloads in this model; those payloads are not physical mbarrier data
encodings. `Async.Drain.returned_can_write/returned_can_reclaim` derive metadata
reuse permission from returned loans and live buffers at any valid index.
`HopperDoubleBufferFullValues` joins zero K and the bounded positive-K data
family under the same independent real GEMM specification and native language.
Its successful-run contract and separate complete execution witness include
public preparation, final matrix cells, returned loans and closed native GenHeap
adequacy. Full-source adequacy retains the whole-map ownership baseline.

Twenty-three checks cover nonzero initial payload 99 overwritten by zero matrix
fragments, actual zero-K source completion/output writes, both barriers' full
storage spans, all-use pool coverage, arbitrary completed zero-K sources and
successful client runs, opaque barrier payload preservation, missing-barrier
preparation rejection, source-matched device completion, insufficient completion/
acquire rejection, and reuse of both returned regions. A common bounded-K test
checks the same public contract across zero and positive K. Physical allocation,
command/value/runtime/compiler interpretation, broader weak RF/proxy realization
and original case/instruction obligations remain open. No new GPU, performance,
IEEE/logits/token, fairness or novelty claim is added.
