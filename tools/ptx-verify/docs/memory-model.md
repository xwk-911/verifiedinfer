# Generic memory model

This is the current generic-proxy layer, with ordinary weak accesses and scoped
relaxed RMWs, shared
by concrete integer bytes and symbolic exact-real float fragments.
It follows archived [PTX ISA 9.4](https://docs.nvidia.com/cuda/archive/13.4.2/parallel-thread-execution/index.html)
sections 8.7–8.10 and the reference paper's approach.
It is not a statement of complete PTX ISA compliance or a proof of compiler/runtime
correctness. Extending the payload type does not admit any new memory qualifier.

## Representation and conditions

- `Memory.lean` extracts byte footprints without rounding addresses down or
  merging shared memory across CTAs. A byte before the base, beyond the payload,
  or in another address space is not part of that access. Reads-from assigns a
  separate source identifier to each read byte. Value agreement requires an
  eligible read's source to be initialization or an actual write covering that
  byte; tainted reads have weaker constraints.
- `Relations.lean` defines program order on emitted event positions and barrier
  arrival-to-return synchronization within one CTA/resource/generation. Their
  strict transitive closure is base causality. Async agents and proxy crossings
  are not encoded as ordinary program-order edges.
- `Consistency.lean` uses scopes from actual RMW events for mutual thread inclusion
  and complete footprint overlap. Observation order may pass through RMWs;
  causality retains the specified construction rather than an arbitrary
  transitive closure of communication. Ordinary weak accesses retain their
  prior same-thread rule. Conservative no-RMW relation lemmas are checked.
- Coherence is a partial per-byte order with initialization, domain, comparison,
  race-unordered and causality obligations. Causality disallows future sources and
  coherence-stale sources. RMW atomicity excludes skipping a morally strong
  preceding modification, including constraints across different bytes.
  Single-copy atomicity and SC-per-location are separate
  predicates; SC-per-location is restricted to pairwise morally strong overlapping
  slices, not asserted as global sequential consistency.
- Value agreement applies only after excluding mixed-size races and proving that
  the read is untainted. A read can be tainted by its own race with a write or by
  two writes racing on a byte it reads. Mixed-size races disable the memory-model
  conditions rather than making the candidate inadmissible. Race classification
  alone does not prove a candidate satisfies all remaining conditions.

The memory conditions are definitions and theorem obligations, not Lean axioms.
NTA is deliberately omitted as in the paper. The accepted atomic form is
`atom.global.relaxed.gpu.add.u32` (also accepted with the documented
sem/scope/space order). Acquire/release, scoped plain loads/stores, fence.sc,
non-generic proxies and non-coherent loads remain unsupported.

An RMW is one event with equal-length read/write payloads. From-read communication
relates distinct operations: the internal read-to-own-write progression does not
become a cycle after collapsing an RMW into one event. Reads-from-self is still
represented and rejected by SC-per-location. The separate `AtomicMemory` regression
constructs an actual completed two-instruction scalar run and satisfies ALL memory
conditions, guarding against accidentally excluding every RMW. Formal correspondence
of this representation to the PTX standard remains open. See also the split-RMW
analysis in [Lustig et al., ASPLOS 2019](https://d1qx31qr3h6wln.cloudfront.net/publications/ASPLOS_2019_PTXMemoryModel.pdf),
§3.5.3.

## Barrier completion and control order

Barrier returns require matching earlier arrivals and arrival/exit coverage for
all threads represented in that CTA. Launch-wide thread coverage and provenance
remain the separate `Candidate.WellFormed` obligation.

An exited-thread summary alone is insufficient. Suppose each of two threads waits
at a different barrier and then exits. Each finite local candidate contains a
return and exit, so each thread could spuriously justify returning by saying its
peer exited without reaching its barrier. `BarrierControlAcyclic` adds the required
exit-before-return ordering and rejects the resulting cycle. These edges express
execution control requirements; they are not used to infer memory visibility from
a peer's exit. They do not prove fairness or termination.

## Current proof evidence

- `publish_across_barrier` derives base causality from the actual write/arrival,
  matched arrival/return and return/read order facts.
- `stale_initial_forbidden` rules out initialization as a source after a causal
  write under the no-mixed-size-race obligation.
- `unique_writer_visible` combines source validity and causality to identify the
  value of an eligible read after its only writer. Eligibility, uniqueness and
  the order path must be proved by clients, not added as unexplained assumptions.
- `read_only_conditions` constructs the generic-memory predicates from actual
  read values, a fixed initial map, absence of writes and control obligations.
- `Tests/EventMemory.lean` applies that rule to one real integer program for
  every scalar input, proving launch coverage, trace provenance, completion and
  a memory witness. It also proves that a load returning 42 from zero initial
  memory is rejected for every reads-from/coherence witness, and that a source
  which is not an actual write cannot justify an eligible read.
- `Tests/EventRaces.lean` derives uniform-size races from traces generated by one
  shared program and checks taint. Mixed-size graphs test only the relation layer:
  byte loads are not part of the current frontend. These tests are not yet full
  allowed-outcome litmus witnesses.
- `Tests/EventBarrier.lean` generates local traces from one program with divergent
  barrier resources and proves that no memory witness can admit their circular
  exit exemptions, despite both local traces ending with `done`.

## Publication witnesses and observed output

`Witnesses.initial_co_conditions` constructs a complete ordinary generic-memory
witness for a graph with at most one writer per byte. Clients prove the actual
byte values and show that program, barrier, reads-from and from-read edges respect
a ranking. The ranking is a way to construct one execution, not a restriction on
all permitted executions or a replacement for universal output proofs.

`Kernels/BarrierPublish.lean` uses the actual generated `barrier_publish.ptx` AST.
For every input word, address parameter and initial byte map, it constructs the
producer/consumer traces, establishes launch coverage and completion, and proves
the generic-memory conditions. A separate theorem leaves the reader's answer and
reads-from/coherence witnesses arbitrary and derives equality with the stored u32
within that trace family. `BarrierPublishUniversal.lean` now closes the coverage
step: arbitrary complete candidates have the same event view as a member of this
family, independent of unused oracle answers and trace-list order. It proves a
`Ptx.Event.Triple` and separate `Nonvacuous` theorem for the stated launch/input
and word-observation domain. These are model-relative contracts; they do not prove
allocation safety or ISA UB freedom.

`Observation.lean` models logical one-byte global reads after synchronized
completion using an explicit domain, output map and source map. API completion
places the observer after all kernel writes. The ordinary generic-memory
projection therefore requires value agreement for eligible bytes and forbids
coherence-stale sources after every kernel write. Write/write races can taint an
observer byte; mixed-size races disable the corresponding memory guarantees.
These conditions are not a proof of CUDA API implementation correctness. Full
correspondence to a combined kernel/observer event graph remains outstanding.

`observer_unique_writer` derives the observed byte from source agreement and
coherence constraints. `observer_unwritten` proves an eligible unwritten observed
byte retains initialization. The publication example constructs an observation
witness and proves its final word, with a separate untouched frame-byte check.
Tests reject a wrong consumer value, a wrong observed word, and an initial SOURCE
after a store even when initialization could contain the same numeric value.

`Ptx.Event.Triple` quantifies over arbitrary
well-formed candidates and checked synchronized observations, with the observation
domain fixed by the contract. `Nonvacuous` is the separate execution/observation
existence obligation. Defining these interfaces is not proving any kernel satisfies
them.

## Complete traces and event-view transport

`Trace.lean` proves concatenation of finite runs and uniqueness of successful
completed runs from the same initial state and oracle. A thread cannot execute
further instructions after `done`; consequently two successful completed runs
have equal lengths and payloads. Counts are arbitrary naturals, not a chosen
fuel bound, and the theorem does not imply that a thread eventually completes.

`Equivalence.lean` transports the ordinary memory predicates across equal
`eventAt` functions. It preserves reads, writes, causality, races, eligibility,
coherence and observation constraints. Barrier participation/control and completed
status depend on trace metadata, so the target's proofs of these facts are supplied
explicitly. Equal event views alone do not prove that an unfinished graph completed.
`Tests/TraceCoverage.lean` checks this boundary and rejects forged instruction
counts and an extra store attached to an otherwise authentic trace.

`Scalar/Execution.lean` checks provenance with the actual mixed scalar interpreter.
The graph retains its scalar oracle and final integer/control state; an existential
float register bank must reproduce the full final scalar state by a successful run.
Memory relations, taint, witness construction, observer conditions and event-view
transport are polymorphic in the payload and oracle metadata types. The original
byte/integer-oracle types remain their defaults. No parallel float memory model or
integer surrogate program is used to prove a scalar candidate.

Scalar execution contexts now carry CTA dimensions. The legacy Event context is
embedded with a unit block for local compatibility, while `Scalar.WellFormed`
requires production using `launch.geometry.block`. A trace produced under a unit
block is rejected if its `%ntid` result disagrees with the actual launch; local
provenance under one context cannot justify production under another context.
`Scalar/Memory.lean` packages represented-real input and output rules over the
same bytewise predicates: immutable reads require actual initialization,
eligibility and absence of writes; observed writes require source uniqueness and
observer eligibility. The existing float-literal contract reuses the real-write
rule. These rules do not establish allocation, overflow or matrix loop invariants.

`ScalarMatmulLoop.lean` now proves the actual generated PCs 32--42 from a loop
invariant: K is bounded as u32, active read addresses do not wrap, pointer updates
use exact modulo-2^64 arithmetic and the accumulator follows `prefixProduct`.
Induction constructs a complete suffix for every remaining iteration count.
`ScalarMatmulLoopTrace.lean` extracts typed load replies from any successful
complete suffix, then derives its event shape and length. Wrongly typed replies
cannot be hidden by the fallback used to name extracted real values. This local
trace result does not establish that a read equals matrix initialization: the
ordinary memory conditions, source footprints and eligibility must still prove
that correspondence. Full arbitrary-launch initialization, masking, global output
and execution/observation existence remain separate matrix-kernel obligations.

`ScalarMatmulInput/Init/Guards/Address/Thread.lean` now close the local source-entry
connection under explicit value, coordinate-product and active-address bounds.
The actual parameter and index instructions execute from PC=0; the row/column
guards preserve both branches and masked threads produce no memory events. Active
address initialization uses modular integer facts and establishes the existing
loop invariant, including exact zero initialization. Arbitrary completed source
traces are classified as masked-row, masked-column or active, without a selected
oracle/count. `IndexBounds` can be derived for valid threads of bounded launch
geometry; component bounds alone are insufficient, as the actual overflow test
demonstrates. The local `AddressBounds` constrains access starts;
`ScalarMatmulConfig.lean` now derives it from whole matrix-region bounds and also
proves all four byte addresses valid and bases aligned. `Scalar/Regions.lean`
allows empty input regions, and A/B may alias if their initial representations
agree. C is separated from nonempty A/B. Actual event reconstruction derives
read/write region membership, unique output ownership and race freedom.
`ScalarMatmulInputs.lean` uses immutable-load rules to force arbitrary local
answers to initial matrix values; `ScalarMatmulOutput.lean` proves the all-candidate
matrix postcondition and preservation of observed bytes outside C. Physical
allocation/UB and full PTX/observer correspondence remain open. Separately,
`ScalarMatmulCandidate.lean` uses duplicate-free geometry enumeration and actual
source completion to build complete launch candidates. `ScalarMatmulWitness.lean`
proves their initial reads-from and unique-writer coherence satisfy the existing
memory predicates, then constructs permitted observations with actual emitted
writers. The resulting `Scalar.Nonvacuous` covers each admissible launch, including
empty dimensions/K=0. This does not establish progress for every allowed schedule.

`FloatLiteralsMemory.lean` uses the actual generated `float_literals.ptx`: compute
(1+2)*3, write shared memory, read shared memory and write the answer globally.
For arbitrary real read answers, initial symbolic maps and reads-from/coherence
witnesses, the existing `unique_writer_visible` rule forces the shared answer to
be 9. It constructs a complete legal graph and synchronized global observation.
`FloatLiteralsUniversal.lean` reconstructs every complete provenance-checked
candidate, including arbitrary instruction counts, unused oracle replies and
trace-list order, and proves `Scalar.Triple` plus a separate `Scalar.Nonvacuous`.
Tests reject answer 17, missing/duplicate threads, forged counts and an integer
reply used for a float load; a concrete address-64 instance observes 9. This is
an auxiliary model-relative contract over its four-byte output domain. Allocation,
64-bit footprint validity, full observer/PTX correspondence, IEEE rounding and GPU
execution are not established by it. FMA's global contract remains separate;
scalar matmul has the parameterized contract and nonvacuity described above.

`CopyEvent.lean` reuses the original `CopyContract.Config` and `Params`, including
arbitrary length/count, disjoint layout, source/destination bounds and flexible
parameter bindings. Active traces have 12 steps and two memory events; masked
traces have 7 steps and no memory events. For every complete well-formed candidate,
the event footprint theorem identifies those accesses and the original layout
proves data-race freedom. `CopyEventOutput.lean` supplies a universal byte-output
contract over the entire allocated global domain, and `CopyEventWitness.lean`
constructs a complete consistent execution and observation for every admissible
positive launch. `Event/Cells.lean` relates initialized u32 cells to bytes, leaving
uninitialized initial cells arbitrary; their frame bytes retain the same fallback.
Any completed operational execution has the same encoded allocated bytes as any
permitted event observation. `CopyCompletion.lean` now constructs a completed
operational execution from every original Copy precondition, using a decreasing
work potential and the existing concrete progress rule. Relational executions
are replayable by `run`. `CopyEventRefinement.output_inclusion` consequently
includes every allowed event observation in actual completed operational outputs
on the entire allocated global domain. This is output inclusion, not an event-
by-event simulation or full PTX compliance theorem.

The old zero-thread CPU case is connected by `zero_count_skip`: coverage implies
empty input, the empty action list completes and returns the identical byte map.
This explicitly models host skip/no-launch; it never invents a physical launch
with zero threads. Positive-count launches, including empty inputs, retain the
separate event contract and non-vacuity proof.

`SharedEvent.lean` reconstructs the original SharedSwap AST's 17-step traces with
independent first/second load answers and six emitted events per thread. For every
complete well-formed candidate, `SharedEventMemory.lean` establishes unique writers,
race freedom and shared-write-to-shared-read causality through the actual barrier.
`SharedEventOutput.correct` derives the exchanged output bytes and unchanged
allocated-global frame for every memory/observation witness; the precondition does
not prescribe shared-load answers. `SharedEventWitness.nonvacuous` constructs
complete, provenance-checked, consistent executions and synchronized observations
for every original configuration and represented global initialization. Initial
shared bytes remain arbitrary and are overwritten before they are read.

The observer construction now has a domain-restricted coverage rule: only writes
to observed bytes must be selected. This permits the same global-only observer to
handle kernels with internal shared-memory writes; the earlier stronger rule is
retained as a corollary. Missing a GLOBAL writer cannot be justified by this rule.

`Tests/SharedEvent.lean` compares original round-robin and reverse-layout executions
on finite inputs and rejects wrong shared/output bytes, stale initialization sources
and barrier-event removal from authentic traces. Removing events from the original
AST is distinct from changing the program to `missing_sync.ptx`. These finite
comparisons are separate from the universal bridge proved below.

`SharedCompletion.complete_from_pre` constructs a completed operational execution
for every original SharedSwap configuration/precondition. The proof uses the
existing invariant's concrete progress, PC work and one remaining collective
release. A release preserves PC work but reduces the extra release component;
ordinary thread instructions reduce PC work and preserve the epoch. No wait is
inserted into the original program and no fairness or termination assumption is
added. Relational witnesses are replayable interpreter schedules via `steps_run`.

`SharedEventRefinement.output_inclusion` proves that every permitted event
observation equals some actually completed operational result on every allocated
global byte. `completed_output_agreement` also covers any supplied completed
operational execution, and a regression applies it to the original round-robin run
against arbitrary event candidates. The proof reuses `Event/Region.lean` with Copy:
initialized values are related by representation, while unknown frame bytes are
preserved by an explicit byte-frame duty and the same initial fallback. Cell
representation alone does not establish equality on unknown bytes.

Still required: allocation/UB obligations,
scoped strong/RMW/proxy extensions and correspondence to a full PTX specification.
PTX assembly and GPU execution tests are separate evidence; no such result is
implied by these Lean proofs.

## Atomic-dispatch provenance and bytewise tickets

`Scalar/Control.eq_branch_run` and the fixed interpreter's integer-store rule
connect both comparison branches and the no-job branch to actual source steps.
`AtomicDispatchBody/Thread.lean` prove full execution for any integer first reply
and reconstruct every completed run, without selecting its count or unused
replies. Normalization to u32 determines the branch and count (10 or 11).

`AtomicDispatchConfig.lean` specifies two CTAs, one thread each, three separated
aligned four-byte global cells with full u64 bounds, and only counter=0 as input
initialization. Other bytes remain arbitrary. `Events/Layout` derive all accesses
from completed source provenance. Overlapping accesses have the same footprint,
so there is no mixed-size race even before output races are settled. Counter
accesses are GPU-scoped RMWs, making the counter reads eligible without assuming
the entire launch race-free.

`AtomicDispatchTickets.tickets` uses coherence at one counter byte to choose an
order. SC-per-location excludes first-in-order reads from the later RMW at ANY
byte, and excludes self-sourcing. With the source-derived two-writer inventory,
the first RMW reads initialization on all four bytes. Cross-byte RMW atomicity
prevents the second from reading initialization; it reads the first RMW's write
on each byte. `Scalar/IntegerMemory.lean` reconstructs u32 values from those byte
fragments, yielding tickets {0,1}. Uniform sources and ticket assignments are
conclusions, not preconditions. No inter-CTA relaxed causality is required.

Complete local two-CTA candidates are constructed for arbitrary reply assignments.
The regression proves every equal assignment is inconsistent for ALL memory
witnesses, while retaining its local well-formedness/completion proof. This is a
negative consistency regression, not a legal two-CTA global existence witness.
`AtomicDispatchAssigned.lean` derives a job assignment from those ticket results
and source coverage, retaining both counter RMWs and both job writes. Unique job
writers and separation determine x/y. For the counter, the second RMW reads the
first at byte zero; SC-per-location prevents reversing their coherence order at
any other byte. `observer_latest_writer` then excludes initialization and the
first modification as stale observer sources. `AtomicDispatchOutput.correct`
proves counter=2/x=1/y=2 and preservation of observed bytes outside all three cells
for every complete candidate satisfying the common memory/observer predicates.
`AtomicDispatchWitness.lean` now independently supplies legal complete two-CTA
execution/observation witnesses for every admissible launch and either CTA order.
Allocation/UB, full PTX correspondence and GPU tests remain open.

## Ranked consistency and observation construction

`Event/RankedWitness.lean` extends witness construction beyond one writer per
byte. Its selected coherence relates actual sources with increasing source rank,
placing initialization before writes. The client must justify actual read values,
program/synchronization/control edges, injective ranks for overlapping writes,
absence of races and strict ranks for reads-from/from-read edges. From-read
ranking applies to distinct operations, so an RMW's internal read/write does not
require rank(event)<rank(event). The theorem discharges ALL existing memory
conditions, including bytewise RMW atomicity, using these premises. These are
construction duties for a PARTICULAR witness, not new allowed-execution or
launch preconditions. The universal dispatch contract continues to quantify over
all memory witnesses.

`Event/RankedObservation.lean` filters a supplied finite event inventory by actual
written bytes and selects a rank-maximal writer per location. The inventory must
cover every actual writer; it cannot hide a later modification. Output values
come from the emitted write or fixed initial fallback, and the proof establishes
the same observer conditions, including no stale source. `Tests/RankedAtomic.lean`
checks a completed single-RMW candidate under the ranked construction and observes
1 from initialization 0. This positive case guards against excluding unsplit
RMWs; the separate two-CTA dispatch nonvacuity theorem is now implemented in
`Kernels/AtomicDispatchWitness.lean`.

## Two-CTA dispatch nonvacuity

`AtomicDispatchRace.lean` derives full race exclusion from a source-checked job
assignment, without assuming memory consistency. Every read lies in the counter
region; x/y accesses are writes and their writers are unique. Counter RMWs are
mutually morally strong. The proof reuses the same layout and footprint rules
used by the universal contract.

`AtomicDispatchWitness.assignment_consistent` constructs reads-from and ranked
coherence for any actual complete source candidate with such an assignment, under
the original launch precondition. The first job's RMW reads initialization and
the second reads its write. Initial counter representation supplies the first
read value; actual emitted RMW bytes supply the second. Source/edge ranks, local
writer-rank injectivity, control obligations and race exclusion establish ALL
memory conditions through `ranked_co_conditions`. Neither consistency nor the
universal output theorem is used to establish this construction.

The canonical source candidates are instantiated with either CTA receiving 0.
This is a choice for an existence witness, not a fixed assignment in the
universal contract. The complete four-event inventory feeds the rank-maximal
observer selector; values come from actual writes and the fixed initial fallback.
`nonvacuous` proves complete consistent execution/observation existence for every
admissible launch and requested global observation domain. Concrete regressions
for both CTA orders combine this construction with the independent universal
contract to observe counter=2/x=1/y=2 and preserve the initial frame byte 165.
Nonvacuity does not prove progress under all schedules, runtime correctness,
allocation/UB freedom, full PTX correspondence or actual GPU execution.

## Online attention arithmetic and the memory boundary

`Scalar/RealMath.lean` defines the paper's exact-real abstraction of
`ex2.approx.f32` as `exp(log(2)*x)`. `Scalar/OnlineSoftmax.lean` proves a rescaled
prefix-sum invariant and normalization against the independent natural-exp
attention specification. The PTX source takes a base-2 scale from memory;
`alpha=log(2)*scale` relates the two specifications without idealizing a rounded
f32 `log2(e)` literal. Empty key rows explicitly produce zero; nonempty rows use
their first score, avoiding a negative-infinity sentinel. Every nonempty abstract
prefix has a strictly positive normalizer. Zero-divisor faults delimit this
finite-real arithmetic fragment, not PTX's IEEE special-value behavior.

`ScalarAttentionUpdate.lean` proves the actual generated PTX initialization,
nine-instruction rescaling update and normalization/store/return blocks. The
normalization tail derives a nonzero divisor from the invariant. These are local
execution theorems: the source still must be proved to reach each block with
that invariant and with the actual input matrix values. They do not introduce
new memory qualifiers or change the common memory predicates. Source-loop
reconstruction, initial matrix/scale read correspondence, byte bounds and race
exclusion, all-candidate output/frame correctness, and a separate legal complete
execution/observation witness remain open for this kernel. Mathematical evidence
and local traces do not establish a global attention contract, approximation
accuracy, GPU execution or bit equality.

`ScalarAttentionDot.lean` now supplies forward completion of the actual inner
dot loop under arbitrary bounded dimensions, oracle offsets and symbolic input
functions. Its derived `9*D+2`-step trace ends before the scale multiply; one more
actual instruction yields scale*dot at PC 53. The `2*D` read events and modular
one-past pointer states are reconstructed for that selected run. The generic
`Scalar/RegisterFrame.lean` rules preserve BOTH banks outside changed register
names, including cross-bank invalidation. Dot iteration/exit and softmax
initialization/update reuse these local rules. Such a register frame does not
preserve global memory by itself. At that stage, entry/outer-loop completion,
arbitrary-candidate reconstruction, global read-value correspondence and independent
legal global execution/observation witnesses remained open.

`ScalarAttentionOuter/OuterUpdate.lean` now compose the actual nested loops from
PC 37 through final store/return. First-item state does not require initialized
softmax registers. For N>0, remaining-iteration induction derives the suffix count
N*(9*D+26)-2, input events and exact-real natural-exp attention output under
explicit local reply hypotheses. The nonzero divisor follows from the online
prefix invariant. N=0 remains the separate early-store path; the new theorem's
positive-key premise describes entry to the normalization loop, not a restriction
on the full kernel's accepted input. A concrete PC=0 source execution exercises
N=2/D=1, both initialization/update branches and a changed maximum, producing 8
in 105 steps. General PC=0 initialization, reconstruction of arbitrary complete
candidates, global initial-input correspondence, full byte bounds/race/UB duties,
the universal memory/output/frame contract and independent legal complete global
witnesses remain open. Local completion under reply hypotheses does not close
those duties or establish hardware approximation/IEEE/GPU correctness.

`ScalarAttentionInput/Init/Guards/Address/Entry/Thread.lean` now supply the general
PC=0 parameter/index/guard/address/scale prefix. Shared `Scalar/Indexing.lean`
rules retain the existing matmul bounds/theorem API and certify the same runtime
index arithmetic for attention. Constructed typed replies give complete local
source runs for arbitrary real matrices: N>0 takes 35+N*(9*D+26), row/column masks
take 21/23, and N=0 takes 32 with no scale or matrix reads. Empty keys use ONLY
the output-start bound; tests prove completion when nonempty input bounds are
false. The empty branch also has arbitrary-complete-run shape reconstruction.
`ScalarAttentionOracle.lean` constructs replies by query slot; that does not
prove initial memory could supply them. Nonempty arbitrary-candidate
reconstruction, global matrix/scale correspondence, complete byte/race/UB duties,
the universal output/memory-frame contract and independent legal global execution/
observation witnesses remain open. Local read-start bounds are not allocation
safety or a global consistency witness.

`ScalarAttentionDotTrace/Trace/SourceTrace.lean` now reconstruct every successful
completed source run under the same explicit bounds, with arbitrary oracle and
instruction count. Successful actual loads derive the f32 constructor/tag for
scale and every Q/K/V query. A shared projection helper's default cannot justify
integer or wrong-format answers. Dot and outer-loop induction recover all query
positions; completion uniqueness fixes the exact count and full emitted events
for all four PC=0 branches. Source reconstruction permits per-item Q answers to
differ even though addresses repeat; input equality is not slipped into its
precondition. A locally complete test reads Q=0 then Q=1 at the same address,
yielding 8 while the uniform-Q spec yields 7. This trace is not asserted globally
consistent. A final V reply tagged f64 cannot complete. Global memory reasoning
must still establish each reply's initial-input value, complete byte/race/UB
duties, the universal output/memory-frame contract and independent legal global
execution/observation witnesses.

## Attention global contract and independent witnesses

`ScalarAttentionConfig/ReadEvents/Events/Memory/Inputs/Output.lean` now close the
previously separate global attention duties within the current symbolic-real
memory/observer model. The configuration covers the output matrix with a 2-D
launch, bounds complete four-byte words, aligns every actual access and separates
O from the read-only Q/K/V/scale regions. Read-only regions may alias if their
represented initial values agree. When no thread can read (M=0, D=0 or N=0),
no read-region bounds, alignment, separation or initialization are required.
These are mathematical layout facts, not physical CUDA allocation guarantees.

Every complete provenance-checked source candidate has either no events (masked)
or actual scale/Q/K/V reads followed by one output write. Read-event indexing
handles repeated Q loads across outer iterations. Full footprints, no RMWs,
input immutability, unique output writers and race freedom follow from source
provenance and layout; they are not supplied as hypotheses to the precondition.
The shared immutable-real-load rule then forces every scale/Q/K/V reply to its
represented initial value. In particular, the earlier locally complete trace
with different Q answers cannot be globally consistent under these conditions.

Finite-support congruence for dot products and online averages connects the
candidate's reconstructed answer to the independent natural-exp specification
with alpha=log(2)*scale. The universal contract covers every complete candidate,
memory witness and permitted observation, producing the specified output matrix
and preserving observed bytes outside O. It does not select an oracle/count.

`ScalarAttentionCandidate/Witness.lean` separately construct actual completed
PC=0 executions for every valid launch thread. They prove initialized read
payloads directly from the constructed input oracle, then construct initial
reads-from, coherence and permitted observations using the shared initial-read/
unique-writer rules. This existence proof does not assume global consistency
or the output theorem. Mathematical launch enumeration includes both masked
paths and N=0; unused read memory is not required on those paths.

Concrete regressions use a 2x2 grid of 2x2 CTAs with M=3, N=2, D=3, so both
masks and non-unit coordinate arithmetic participate. An independent complete
consistent execution/observation witness yields output 7 and preserves a nonzero
frame byte. Another witness permits N=0, Q=K=V=O, and an unaligned unused scale
pointer at 2^64-1, producing zero. Repeated-Q disagreement, incorrect scale,
output and frame are rejected. The GPU suite also compares all nine output cells
and guard words for the 3x3 case exactly; its current report has twelve exact-byte
comparisons and one completion-only smoke check.

The attention case remains partial against the full goal: exact-real ex2 and
arithmetic, projected observers, physical allocation/UB and full PTX-model
correspondence retain their stated boundaries. A finite Ada GPU result does not
establish arbitrary-input IEEE/approximation correctness, bit equivalence,
optimized FlashAttention, Ampere/Hopper features or performance. The barrier
legality gap described separately is not silently removed from the shared model.

## Aligned barrier legality and hardware evidence

The first live GPU run exposed a source-level gap in the barrier model. The old
publication fixture sent its reader and writer to different `bar.sync 0` PCs
(5 and 9). The owned test process stalled at that fixture and was terminated;
the source, hash and observed failure are preserved in
`gpu-barrier-divergence.json`. Assembly had accepted the source. NVIDIA specifies
that `bar.sync` is equivalent to `barrier.sync.aligned`, with all CTA threads
executing the same instruction; divergent conditional use is undefined under
those aligned requirements. See the [pinned PTX barrier specification](https://docs.nvidia.com/cuda/archive/13.4.2/parallel-thread-execution/index.html#parallel-synchronization-and-communication-instructions-bar).

The corrected source joins both branches at PC 7. Its actual producer and
consumer runs now take 9 and 10 steps respectively, while emitting the same
abstract memory/barrier events as before. Existing universal model-relative
correctness and independent complete-consistency witnesses were rebuilt.
`ISA/BarrierSites.lean` certifies the common single static site;
`Tests/BarrierSites.lean` proves the old source has two sites and actual local
prefixes reaching different ones. The old source is retained in
`examples/divergent_barrier.ptx` and a false single-site assertion is rejected.

This is a sufficient source fact, not a general convergence/warp-participation
checker. Resource ID and generation matching in the current event model do not
by themselves establish full aligned-instruction legality. No new global
consistency premise silently closes that gap. Requiring one static site for
every program would also exclude legitimate multi-site programs; a general
rule must describe dynamic collective participation and the relevant source
instruction requirements.

`scripts/check_gpu.sh` now runs finite driver-API/JIT tests against the actual
PTX. The recorded RTX 4060 Laptop sm_89 run passes eleven exact-byte comparisons
and one completion-only loop check. Matrix and attention references use exact
rationals on selected small inputs, with no tolerance. Publication exports only
its producer write; the unused consumer load may be optimized away, so that
comparison does not independently establish read visibility. The runner's
whole-run watchdog records a failure and exits 124 on expiry; that failure path
was also exercised. Reports include fixture hashes and device/library details.
Existing matching workspace driver libraries were selected in a child process;
system drivers were not modified.

`assembly-evidence.json` records twelve fixtures accepted by ptxas 12.8.93,
including the divergent negative source. Assembly acceptance is therefore not a
proof of execution legality. `gpu-evidence.json` records the finite positive
tests separately. Neither report proves arbitrary-input IEEE/approximation
behavior, universal GPU bit equality, Hopper execution, performance, allocation
safety or correspondence of the event model to the full PTX specification.

## Source-aware integer barrier admission

`Event/SourceRun.lean` now instruments arbitrary finite interpreter executions:
each emitted event receives the PC of the actual state before its generating
step. Generic construction, erasure and event-origin theorems relate those
annotations to the unchanged plain run. `Event/Origins.lean` instantiates this
instrumentation for the actual integer interpreter and launch candidate. A
candidate's source PC is computed by rerunning its recorded program/oracle/count;
it is not another unconstrained oracle or caller-supplied tag. Provenance and
annotation erasure identify each graph event with its actual generating step.
Barrier origins additionally prove the source instruction is the matching
`bar.sync` resource.

`AlignedBarrierSources` requires every same-CTA, same-resource/generation
arrival/return pair to have a common source PC. It does not require different
generations to use the same PC. A static `uniqueBarrierSites` certificate is
proved sufficient for arbitrary provenance-checked candidates; it is not the
definition of dynamic alignment. The source rule implements the same-instruction
obligation in the pinned [PTX aligned-barrier rule](https://docs.nvidia.com/cuda/archive/13.4.2/parallel-thread-execution/index.html#parallel-synchronization-and-communication-instructions-bar).
It does not purport to specify every SIMT/warp convergence, early-exit timing,
allocation or instruction UB condition.

`Event/Checked.lean` introduces source-aware admission, combining actual source
provenance, dynamic barrier-source matching and existing graph-memory conditions.
Its checked contract and checked nonvacuity interfaces retain the ordinary
observer conditions. Every old universal graph contract implies a checked
contract. Existence remains separate: `Kernels/SourceChecked.lean` derives
source alignment from static source certificates and lifts complete memory/
observation witnesses for Copy, SharedSwap and publication. Their caller
preconditions gain no alignment assumption. The original graph-only API remains
available as a weaker admission layer; graph conditions alone are not relabeled
as a source-aware legality verdict.

`Tests/SourceOrigins.lean` checks both sides of this boundary. The archived
generated divergent source has two actual complete local runs, covers the CTA,
and emits exactly the same graph events as the positive publication candidate.
Its writer arrival originates at PC 9 and reader return at PC 5. It therefore
fails checked admission for every initial memory, reads-from and coherence
choice. A separate four-instruction integer program uses `bar.sync 0` at PCs 0
and 2 in successive generations. Its static unique-site check is false, yet
actual source matching, complete launch coverage, memory consistency and an
observation preserving arbitrary initial global bytes all hold. This positive
witness prevents replacing the required dynamic rule with a blanket single-site
restriction. The four-instruction program is a hand-authored Lean semantic
regression, not an additional generated PTX or GPU fixture.

`Scalar/Origins/Checked.lean` now extend the same admission layer to mixed scalar
execution, as described below. No PTX fixture or GPU runner changed in this step; the previous
finite hardware reports remain distinct evidence, not a new hardware validation
of the source-aware model. Full PTX/SIMT and observer correspondence remain open.

## Mixed scalar source admission

The mixed interpreter now instantiates the same generic source-run instrumentation
and `AlignedBarrierSources` predicate. `Scalar/Origins.lean` executes the actual
scalar program, preserving its complete float bank and using the launch's actual
block dimensions. It proves both successful annotation construction and exact
full-state/event erasure. Event-origin extraction checks actual scalar provenance;
it does not translate the float program into the private integer stepping aid.
`Scalar/Thread.lean` proves that every scalar barrier event originates from the
actual `.integer (.barrier bid)` at that PC. Floating operations, special-register
reads and atomic RMWs cannot fabricate barrier events. The integer barrier-kind
predicate is shared polymorphically across byte and symbolic-real payloads.

`Scalar/Checked.lean` bundles provenance, actual source matching and the SAME
generic memory conditions. Its checked contract/nonvacuity interfaces preserve
the existing observers. Static unique-site certificates are sufficient; dynamic
matching remains the definition and permits different PCs across generations.
`Kernels/ScalarSourceChecked.lean` connects scalar matmul, atomic dispatch,
attention and the literal/shared helper. Their checked contracts keep the same
preconditions, output formulas and frame guarantees. Independent checked complete
executions/observations are constructed using the earlier nonvacuity witnesses
and proved source alignment; no alignment assumption is added to caller inputs.

The typed hand-authored semantic regression in `Tests/ScalarSourceOrigins.lean`
reads `%ntid.x` from a block of size two, branches on that value, executes f32
move/add operations and encounters `bar.sync 0` at PCs 7 and 9 in successive
generations. Its full scalar state, including float bank, is checked. Complete
CTA coverage, dynamic source matching, memory consistency and observations
preserving arbitrary initial global bytes are independently proved. Substituting
the unit block chooses a different path and the recorded eight-step source run
faults; actual block source PC 7 cannot be replaced by that result. Its static
unique-site test is false, so checked acceptance is not restricted to single-site
programs. The archived divergent source also has complete local scalar runs and
launch provenance, but source PCs 9/5 reject it for every memory/coherence choice.
These semantic regressions are not new generated PTX or hardware fixtures.

`Tests/ScalarSourceChecked.lean` retains complete checked matmul and attention
output/frame instances, empty-key attention with aliasing and unused invalid
scale, both atomic ticket assignments observing counter/job/frame bytes, and the
literal/shared helper's output 9. Full PTX/SIMT/observer correspondence, physical
allocation/runtime and arbitrary-input IEEE/GPU bit equality remain separate.
This source check neither adds async/MMA instructions nor closes the remaining
same-stream composition, in-flight resource or Ampere/Hopper goal requirements.

## Completed same-stream composition and publication

`Event/Publication.lean` addresses the finite observer boundary explicitly.
Observer conditions constrain only `o.domain`; `o.output` may contain arbitrary
values elsewhere. Equating a successor's initial map with that raw function
would import unconstrained bytes. `CoversGlobalWrites` instead requires every
actual emitted global write byte to lie in the observer domain. `published`
uses observed values on that domain and retains the initial bytes elsewhere.
The `publication_observed` theorem proves this normalized map satisfies the
ordinary observer conditions on ANY finite global domain, with corresponding
sources. New outside-domain locations have no writes, so selecting initialization
there cannot hide a newer modification. This uses the existing observer model;
it does not claim full augmented-graph/PTX correspondence.

`Scalar/Stream.lean` stores persistent GLOBAL bytes separately from each
invocation's shared initialization, code, geometry, parameters and publication
domain. A completed step contains actual source-checked candidate provenance,
memory consistency, completed observation, and proved global-write coverage. The
next invocation receives the published global heap. Its shared bytes come from
its own initialization function, not the prior kernel's shared writes. Local
event IDs stay within their individual step records; no flattened graph silently
identifies events from different kernels.

The ordered `Runs` relation composes these completed steps. Append/splitting and
consequence rules prove universal pipeline postconditions, while a separate
nonvacuity rule first constructs an actual predecessor execution, derives the
successor precondition from its universal postcondition, and constructs the tail.
It does not assume a successful whole pipeline or prescribe desired load answers.
`single_correct`/`single_nonvacuous` connect existing scalar checked contracts to
these rules. `Kernels/StreamEffects.lean` derives publication coverage from actual
matmul, attention and literal/shared write provenance. Coverage is a proved
effect obligation; it is not supplied as an unexplained fact about source code.

The generated-entry composition baseline in `StreamPipeline.lean` first runs
the literal/shared kernel at A=64, then scalar matmul with A=64, B=128 and C=192,
M=N=K=1. Its theorem quantifies over arbitrary represented real B and initial
global heaps, proving C=9*B and preserving a frame byte. Separate component
nonvacuity and the intermediate-memory proof give an independent complete
checked pipeline witness. A positive instance starts with uninitialized A/C,
has B=2, and produces 18; a stale successor input is rejected. Tests also cover
unobserved poisoned payloads, omitted global writes and fresh shared state.

The GPU harness queues these two existing entries on one default stream, with
both modules loaded beforehand, no intermediate host synchronization, and one
completion wait after both launches. It compares A=9, B=2, C=18 and all three
guards byte for byte. The current report records thirteen exact-byte cases and
one completion-only test. This finite run is separate from model-relative
universal correctness and is not an arbitrary-input IEEE/bit-equivalence proof.

This stream layer specifies the completed ordinary-global-memory boundary
described in the paper's section 3.5; it is not a proof of the CUDA driver or an
operational derivation of every API/proxy rule. Tensormap/other proxy boundaries,
in-flight borrowing, runtime/Iris connection, concurrent kernels, and the actual
three-kernel routing/expert/combine MoE remain outside this step. The two-entry
baseline is not substituted for the required MoE case or the full goal.


### MoE source and finite execution boundary (2026-11-05)

The frontend now accepts one additional fixed form, `setp.gt.f32`: a `.pred`
destination, two finite f32/b32 real operands (or supported finite literals),
ordered greater-than, and integer-bank predicate assignment with cross-bank
invalidation. No NaN, unordered/Boolean comparison, dual-predicate destination,
ftz modifier or IEEE bit-level claim is added. `Scalar/Compare.lean` derives the
step, predicate bound, tie behavior, bank validity and register-frame rules from
the fixed interpreter. Other comparison/modifier/type forms fail closed.

The three actual MoE entries total 121 source instructions (23 route, 57 expert,
41 combine); this is our implementation, not a reconstructed paper artifact or
an exact-instruction-parity claim. The independent `Kernels/MoeSpec.lean`
specification chooses the larger of two gate scores, breaking ties toward zero,
and computes a dense linear expert with the source FMA iteration order. Routing
uses u32 output. Experts read that routing and write only the selected plane at
`((expert*M+row)*N+col)`. Combine reads that same selected plane and writes
row-major Y. Sparse layout uniqueness/bounds and selected-score maximality are
proved mathematically. This normalized top-1 baseline has unit combine weight;
it does not include a gating network, packing, capacity or top-k>1 behavior.

`MoeRouteSelect.lean` proves both actual selection branches and the u32 store/
return for arbitrary ready scalar states. `MoeRouteThread.lean` proves actual
PC=0 traces with runtime block/CTA/thread indices and explicit 32/64-bit bounds:
22 steps with two gate reads and one routing store for active tokens, 11 steps
with no data events for masked tokens. Arbitrary successful completed active
traces reconstruct typed f32 gate replies, exact count and the source events;
masked traces reconstruct count and absence of events. No correct-input oracle
or successful global execution is assumed. This is local execution evidence:
initial-memory correspondence for gate replies, complete launch enumeration,
byte ownership/race proofs and global consistency/observation witnesses remain.
Expert/combine source reconstruction and their universal contracts are pending.

The updated driver runner loads all three modules before queuing the dependent
stages on one default stream, with one final completion wait. An independent
exact-rational host specification computes expected routing and dot products.
Each entire arena is compared byte for byte, including immutable G/X/W, route,
selected and unselected expert slots, final Y and guards after every segment.
Five finite chains cover mixed routing and ties with overlaunch, negative and
positive-subnormal gate comparisons, K=0 with unused X/W aliases, N=0 and M=0
with unused aliases. The current sm_89 report records eighteen exact-byte cases
plus the separate completion-only loop check. Fifteen fixtures pass ptxas 12.8.93
assembly. These checks do not establish universal hardware/IEEE correctness,
performance or the three-stage formal memory/composition contract. The earlier
two-entry stream example is retained as a separate completed-boundary proof.


### MoE route universal memory contract and publication (2026-11-05)

The routing component now has a universal current-model contract and a separate
complete consistency/observation witness. `MoeRouteConfig.lean` bounds every
byte of the two finite-real gates and u32 route for each active token. A 1-D
launch avoids duplicate ownership from unused y/z coordinates; explicit x index
bounds prevent u32 wrap. Gate and route regions are separated only as live
regions; M=0 requires no gate representation, alignment or distinct pointers.
Hardware launch/allocation validity remains outside these mathematical bounds.

`MoeRouteEvents.lean` reconstructs every event of every complete produced trace
from the actual PC=0 execution. `MoeRouteMemory.lean` derives immutable gates,
unique byte writers and race freedom. The payload-independent rule in
`Event/ReadOnlyInputs.lean` is reused by existing scalar matmul as well. These are
derived source effects, not extra no-race/unique-writer assumptions on the caller.
`MoeRouteOutput.lean` uses the shared value-agreement and observer predicates to
identify every gate reply and prove u32 top-1 routing plus the observed frame for
all complete candidates, all memory witnesses and permitted observations.
`Scalar/IntegerMemory.lean` supplies the reusable u32 observation rule.

`MoeRouteCandidate.lean` enumerates all launched IDs, chooses typed gate answers
only for the existential construction, and executes the actual active/masked
entry path to completion. `MoeRouteWitness.lean` proves the independent memory
witness and synchronized observer witness, with source-aware admission for the
actual mixed program. The construction does not use the universal postcondition
as its input or assume an already successful global execution.

`MoeRouteStream.lean` derives coverage of every global write from the actual
u32 source store and proves a single route launch publishes represented u32
routes into the successor's global initial heap. Normalized publication retains
all other heap bytes, including outside the finite observer. This uses the same
completed ordinary-memory boundary as earlier stream proofs; it is not a CUDA
runtime/proxy correspondence proof. New stream u32 representation rules coexist
with the finite-real representation rather than reinterpret float bits.

Concrete regressions use three tokens across two CTAs with two threads per CTA,
including one masked thread, both experts and a tie; every complete candidate
has routes [0,1,0] and preserves the nonzero observed frame. A separate complete
checked legal execution/observation witness exists. A locally complete typed
wrong-gate candidate is rejected by global value agreement even though its
chosen expert need not change. A zero-token launch with unaligned G=R=1 and
uninitialized gates has a separate complete checked legal witness preserving
all observed bytes. The route stream has a complete witness and rejects stale
successor initialization. Omitting the final byte of the last route is rejected
using an actual canonical source write, not merely a desired-output assertion.

Expert/combine full source and memory proofs, their independent complete legal
witnesses and the complete three-stage MoE composition remain. Existing finite
GPU evidence is unchanged; no PTX or GPU-runner source changed in this round.


### Relocatable expert FMA fragment (2026-11-05)

`Scalar/FmaLoop.lean` proves a native scalar loop against the fixed interpreter,
with arbitrary actual code, entry PC, prior query count, K, data and layout. A
`Fragment code base` certificate checks eleven consecutive instruction fetches,
including the absolute branch/back-edge targets and final store/return. The
iteration count 9*K+4 is derived by induction. `FmaLoopTrace.lean` extracts every
required typed f32 reply from any successful complete local execution and derives
its exact count, events and final accumulator; defaults in reply projections are
not evidence of a valid reply. The proof is not a replacement interpreter or an
oracle-supplied source mapping.

Existing matmul `iteration`/`finish` now instantiate this common proof at PC32,
query origin 0, with their prior public invariants and theorems retained. Expert
loop register names were aligned with the common fragment. Its actual typed
source certifies PC46 and query origin 1 because the u32 route read comes first.
`MoeExpertsLoop.lean` instantiates the same rules for arbitrary K and connects the
ordered result to the independent `Moe.linear` recurrence. The fragment supports
other source positions/query offsets; it imposes no claim about code outside its
window or initial state construction.

PC=0 tests use CTA=(1,1,0), block=(2,2,1), tid=(0,0,0), M=N=3/K=2 and both expert
choices, retaining arbitrary real X/weights. Both branches read route R[2] at136,
then enter the checked loop with one prior query; expert 0 writes H[0,2,2] at288,
expert 1 writes H[1,2,2] at324. Complete local executions take 62/68 steps with
five queries. A K=0/X=W=H instance has a complete 50-step local witness with only
the route read and zero store. Wrong integer/f64 replies, resetting query origin,
a wrong loop branch target and a missing store certificate are rejected. Another
program keeps the certified loop but changes PC0 to return: its certificate and
immediate source completion coexist, demonstrating why entry proof is separate.

These are universal local fragment rules and concrete actual-entry instances,
not universal full-entry expert correctness or launch-wide memory witnesses.
The local layout inherits matmul's start-address bounds; clients still establish
full word bounds, alignment, live-region separation and represented initial
memory, including the u32 route, before applying global contracts. All-dimension
expert entry/selection, combine, complete global legal witnesses and full MoE
composition remain. Renamed PTX was reassembled with the other fourteen fixtures,
and the GPU suite was rerun for eighteen exact-byte comparisons and one separate
completion-only test. Neither these finite runs nor exact-real loop proofs imply
arbitrary hardware/IEEE equivalence.


### Parameterized full expert source (2026-11-05)

The expert source proof now covers actual PC=0 for arbitrary declared word-sized
parameters and runtime indices with explicit no-wrap index bounds. `MoeExpertsInit`
executes the seven parameter reads and two-dimensional index instructions;
`MoeExpertsGuards` executes both masks and the actual return. Row-masked threads
complete in 20 steps, column-masked threads in 22, without data events or queries.
Data pointers can be unaligned, aliased and uninitialized on these masked paths;
only intrinsic parameter/index typing is retained.

`MoeExpertsRoute` proves the actual route-pointer arithmetic and u32 source load.
New reusable scalar rules extract an integer reply from any successful integer
load and prove its wrapping, read payload and query increment. The generalized
unsigned comparison/branch rule handles register and immediate operands; the
prior register-only rule now reuses it. Route normalization is `wrap 32 value`,
not an unproved assumption that every supplied integer oracle was already u32.
`MoeExpertsSelect` executes the actual limit check and zero/nonzero branch.
Normalized routes >=2 return in 27 steps after just the route read. Only 0/1
proceed to their corresponding weight and result planes. Plane arithmetic keeps
64-bit modular behavior rather than assuming products or sums fit.

`MoeExpertsAddress` proves the actual 12-instruction pointer/stride/accumulator
initialization and establishes the shared FMA-loop invariant at PC46/query1.
The natural layout includes X[row,k], W[expert,k,col] and H[expert,row,col];
read-start and output bounds eliminate wrap where those accesses occur. X/W
read bounds quantify only over k<K, so they are vacuous for K=0. Global full-word
bounds, alignment, separation and actual allocation remain separate duties.

`MoeExpertsThread` constructs complete source executions with arbitrary real
X/weights under corresponding typed local replies, and reconstructs arbitrary
successful complete executions without prescribing desired replies. It derives
query zero's integer constructor from the actual load, classifies invalid routes
and both masks, and connects valid source prefixes to the shared arbitrary-K
loop reconstruction. The two valid branches take 44+9*K and 50+9*K steps; route
queries are followed by the actual 2*K float reads and one expert-plane store.
The source classification does not imply those replies agree with initial memory.

Regressions apply these parameterized rules to non-unit CTA/block coordinates,
all successful local float oracles, a raw 2^32+1 route that selects expert 1 after
normalization, an invalid route 17 with no float accesses, and M=0/N=0 with
unaligned X=W=R=H=1 and K=2^32-1 without any memory queries. Separate negative
assertions reject skipping expert-1 plane instructions and using expert-0's
output address for expert 1. No PTX or GPU-runner source changed; earlier exact
GPU/assembly evidence is retained subject to current source-hash checks.

Initial X/W/R representation, route agreement with the prior kernel's u32
publication, full byte regions/alignment, writer uniqueness and race freedom,
universal expert observed-output/frame correctness and independent complete
legal global witnesses remain. Combine and complete three-stage MoE composition
also remain; local completion is not substituted for global nonvacuity.


### Expert global memory, selected-byte frame and publication (2026-11-05)

`MoeExpertsConfig` supplies the live four-byte R/X/W/H layout, alignment,
no-wrap launch indices, output coverage and input/output region separation.
K=0 imposes no X/W reads, initialization or alignment; either outer dimension
zero imposes no input initialization. Only intrinsic word-sized parameters
remain on masked paths. `MoeExpertsEvents.access_bounds` derives aligned global
four-byte footprints below 2^64 from actual complete-source event shapes.

The global proof bootstraps without assuming valid/correct routing. Any source
candidate may initially choose an arbitrary integer route, including >=2 and its
actual early return. Reads still lie in R/X/W, while every write is a unique H
word owned by its row/column thread. Expert-plane index injectivity and actual
launch-coordinate injectivity show overlapping writers are the same event.
The common read-only-input/unique-writer rule then derives race freedom before
input agreement is used. This avoids circularly restricting candidate routes
in order to prove the memory condition that establishes their validity.

`Scalar.IntegerMemory.immutable_u32_load` inspects all four read bytes and uses
bounded u32 injectivity; reading only byte zero would not identify general u32
values. `MoeExpertsInputs.expert_correct` derives the normalized route from
initial represented R, so it equals the independent selected gate expert.
Immutable exact-real loads then identify X/W replies, and induction connects
the shared FMA recurrence to `Moe.output`. No desired float or route oracle is
inserted into universal preconditions. R represents the prior stage's selected
indices, but this component theorem does not itself prove the complete pipeline.

`MoeExpertsOutput.correct` quantifies over all complete well-formed candidates,
shared memory-condition witnesses and synchronized finite observations. It
establishes every selected expert output and preserves every observed byte
outside `SelectedByte`, including unselected words inside the H allocation.
The stronger frame follows actual writes and derived route agreement rather
than framing only outside the full two-plane H region. The output observer need
only cover selected words for the current gates.

`MoeExpertsCandidate/Witness` independently enumerate every launched thread and
construct actual PC=0 completed executions with a typed route/float oracle.
Masked threads execute their actual return. Canonical read bytes agree with the
initialized R/X/W maps, and an initial-reads/unique-writes coherence witness
establishes consistency and a complete legal observation. Source-aware checked
admission uses actual source provenance and certified unique barrier sites.
This existence proof does not use the universal output theorem to assume its
own conclusion or assume an already-completed launch in the precondition.

`MoeExpertsStream` derives coverage of all actual global writes, publishes the
selected exact-real H words to the successor global heap and preserves all
nonselected heap bytes. It separately proves completed-boundary nonvacuity.
Shared memory still starts afresh per launch under the existing stream model.
The tests prove mixed routes [0,1,0] and outputs [12,20,12] in a 3x3x2 launch,
preserve unselected-plane sentinels and reject a locally complete wrong-route
candidate for every reads-from/coherence choice. K=0/X=W=H has no float input
initialization; M=0 and N=0 separately permit all pointers=1 and K=2^32-1 with
only sentinel memory. Stale successor heaps and missing published bytes fail.

Combine source/memory contracts and complete route/expert/combine composition
remain. This is ordinary-memory exact-real model progress, without new ISA,
allocation, runtime, physical GPU, IEEE or proxy correspondence claims. Broader
async/MMA, atomics/shuffle and the actual Iris in-flight-access bridge remain in
the original goal. No new ownership method or measured optimization is claimed.


### Full combine and three-stage MoE stream contract (2026-11-05)

Combine now has actual parameterized PC=0 proofs rather than a local typed
trace or finite GPU example. Source initialization reads R/H/Y/M/N and runtime
2-D coordinates, checks row/column masks, loads R as u32, checks its limit and
selects the expert H plane. Nine actual address instructions compute H/Y
pointers; one f32 read, one f32 store and return finish the gather. Active
expert-0/1 paths complete in 38/41 steps with queries=2 and R-read/H-read/Y-write
events. Row/column masks complete in 18/20 steps without data events; invalid
normalized routes return after 25 steps and one R read. Arbitrary completed
runs derive integer/float reply constructors from actual loads and reconstruct
these source events rather than assuming the desired oracle.

The global gather config bounds and aligns all four bytes and separates live
R/H inputs from Y. Event reconstruction retains invalid-route candidates.
Immutable inputs and row/column writer uniqueness derive race freedom first.
The existing all-four-byte u32 agreement rule then identifies R with the
independent selected route. Only the selected H word's exact-real representation
is required to identify the float answer; unselected H contents are arbitrary.
Every output and observed byte frame follows for all admitted complete
candidates and shared memory witnesses. The existence proof separately
constructs actual completed source traces, initial reads/coherence, complete
observation and source-aware checked admission. Publication covers actual Y
writes and frames every other global byte.

`MoePipeline.Config` connects stage dimensions and R/H bases while allowing each
kernel its own geometry, parameter bindings, shared initialization and observer
domain. Its precondition requires G, X and W values only. No initial R/H/Y value
or complete run appears there. The route stage's universal u32 result provides
expert R, while its frame preserves live X/W under explicit separation. That
separation is conditional on active dimensions: N=0 need not protect unused X,
and M=0 need not protect unused W. The expert result provides selected H and its
selected-byte frame preserves R; combine's precondition follows. Successors use
the existing normalized global publication relation, never an unconstrained
finite observer payload. Shared initialization remains fresh per stage.

The pipeline's all-run postcondition states independent `Moe.Post` Y values and
whole-heap preservation outside route words, selected H words and Y words.
`nonvacuous` constructs complete legal boundaries in source order by each
stage's independent witness and the proved readiness implications. It uses
existing stream append/split rules; this is ordinary completed same-stream
composition, not simultaneous or concurrent kernels. It does not discharge
CUDA runtime, proxy, full PTX/observer/augmented-graph or physical allocation
correspondence obligations.

Regressions poison R/H/Y at entry, use mixed/tie routes [0,1,0] with 3x3x2 data
and non-unit expert/combine CTAs/blocks, establish Y rows [12,20,12], and retain
unselected-plane sentinels. Their entry memory provably lacks the final R/H/Y
representations. K=0/X=W=H needs no float inputs and yields zeros. N=0 permits
dead X/W/H/Y aliases while the still-active route R/G remain aligned; M=0
permits all pointers=1 and maximum u32 K and preserves every byte. Typed wrong
H or R oracles construct locally complete gather candidates but violate global
value agreement for every reads-from/coherence choice. Invalid route 17 has an
actual 25-step source witness without H access. Truncated Y publication is
rejected. Negative evaluator assertions additionally check live-region overlap,
full-word wrap, stage inventory order and poisoned entry data.

The three-stage ordinary-memory mathematical baseline is now established. The
case stays partial in the full coverage inventory because complete ISA/runtime
correspondence remains open. No optimized MoE, packing/capacity, top-k>1,
gating-network or weighted-combine claim is made. Ampere/Hopper, broader
atomics/shuffle, exact instruction parity and the concrete asynchronous Iris
resource bridge remain in the original active goal.


### Ampere non-bulk copy source and graph foundation (2026-11-05)

The ordinary event layer assumes thread-owned accesses in issuer program order.
Reusing it unchanged for cp.async would insert false ordering. The new
`Ampere` layer therefore carries its own instruction data, source state and
augmented nodes; it does not coerce asynchronous copies into ordinary scalar
loads/stores or use the old consistency predicates unchanged.

`Syntax` adds explicit cache/address/byte-width and group-control constructors.
`Thread` delegates scalar slots at the same source PC, preserving branch targets.
An issue records oracle bytes in an append-only ledger, its uncommitted group
and a fresh per-thread ordinal; it advances the actual query index. The local
step mutates no heap. Commit and wait instructions record control events.
`Rules` proves group-count monotonicity, copy-ledger extension, persistence and
source origins for every finite run, with no fixed fuel/shape assumption.
`Source` proves both directions between emitted issue events and final ledger
entries of provenance-checked candidates. Synthetic read/write nodes thus have
actual source operations behind them.

`Graph.Node` distinguishes thread events, copy reads and copy writes. Program
order is defined only on thread events. Source-before-issue, read-before-write,
issuer-specific wait completion and CTA barrier edges are separate relations.
A copy-write node has no outgoing base edge except its completion edge. The
proved no-wait/no-path theorem therefore also excludes publication through a
barrier that was merely issued after the copy. Wait-frontier tests distinguish
older, recent and uncommitted groups; a peer thread's wait cannot complete the
issuer's group. Cache hints remain metadata, with no invented ordering effect.

The graph-parametric `MemoryGraph` core now defines rf/coherence, taint/mixed-size
races, SC-per-location, RMW conditions and final observations on an explicit node
and agent type. A source encoding is proved isomorphic to optional writer nodes;
this introduces no semantic axiom. `MemoryGraph/Ordinary.lean` proves the ordinary
memory conditions are equivalent to the new fragment plus the original barrier
participation/control obligations. Its observer conditions are also equivalent.
The existing ordinary model is unchanged.

`Ampere/Memory.lean` instantiates this fragment on actual augmented nodes. Thread
agents and `(owner, copy ordinal)` agents differ even when they share a physical
issuer; owners are retained separately for scope membership. Copies are proved
not to be RMWs and not morally strong with ordinary thread accesses. A waited
unique copy is visible to an eligible later read for every admitted rf/co.
Eligibility, unique writes and actual completion are premises to prove, not
substitutes for the desired value. Graph-generic consistency/observer witness
constructors are independently tested on a small model with a parameterized byte
value; removing ordering yields a race and ineligibility. That model witness is
not a complete legal PTX source execution.

`Ampere/Origins.lean` instruments the actual full interpreter with pre-step PCs.
Erasure is proved in both directions, and every event is traced to an actual
source step. Barrier events can only come from a scalar `barrier` slot at that
PC. `SourceAligned` requires matched synchronization events to share that actual
PC. Unique static sites are a sufficient certificate, not the definition: dynamic
matching accepts multiple sites used in distinct generations.

`Ampere/Checked.lean` combines source production, dynamic barrier matching,
full-CTA barrier participation, exited-peer control obligations and the augmented
memory fragment. Its control graph includes all async base edges as well as
exit-before-return edges. Exit does not imply a pending copy has completed and
these exit edges are not added to memory causality. An actual two-thread source
that would let each completed trace exempt its peer is rejected by a constructed
control cycle, even though participation alone passes. The actual generated copy
helper has separately proved source-PC alignment, participation and acyclic
control order. These are construct facts, not its missing data-correctness or
complete memory-witness theorem.

`Ampere/Trace.lean` supplies arbitrary finite-run decomposition, successful-prefix
inversion and completed-run uniqueness over the full Ampere state. It adds no
fuel bound, heap replacement or termination premise.

The actual helper now has parameterized source reconstruction and all-candidate
output/frame correctness in `Kernels/CpAsyncCopy{Trace,Source,Graph,Memory,Correct}`.
`CpAsyncCopySpec` independently specifies sixteen-byte copy and preservation of
all other observed global arena bytes. Its layout uses one CTA/thread, a bounded
arena, a sixteen-byte aligned input, four-byte aligned output and disjoint ranges;
four represented bounded u32 inputs support the independent nonvacuity construction.
Source completion forces payload size, four integer reply shapes and exactly
fifteen source instructions, for arbitrary finite candidate counts. Copy bytes
and scalar replies remain independent until the memory proof.

Actual read/write classifications and footprint bounds derive input immutability,
unique writes and race freedom for every rf. Copy-to-load ordering uses the
actual own-group wait, never issuer PO or same-agent strength. Thus eligibility
is derived rather than added to the kernel precondition. Copy read agreement
forces all sixteen payload bytes to the initial input; later reads see the copy,
and the observer sees their global output stores. Every complete source candidate
is transported to this graph by a proved equality of augmented memory views;
unused oracle metadata is unrestricted. Source-complete candidates with wrong
payloads or scalar answers are rejected for every rf/co on a represented input.

`CpAsyncCopy{Control,Payload,Witness}` now independently constructs a complete
checked source/rf/co/observer execution for every launch satisfying the same Pre.
The initial representation supplies four bounded words; the payload is assembled
from those words. An explicit rf reads initialization for the copy and its shared
write for scalar loads. Unique writers, actual read values and a rank of actual
base/control edges certify InitialCo using the generic graph witness rule.
The observer is selected from actual writes and retains initial bytes elsewhere.
This construction does not use the universal output theorem and adds no new
precondition or desired-output assumption. The concrete sample has checked
source, memory and observer witnesses; output/guard values follow from Post.

Remaining async construct/UB/storage legality and full PTX ISA/runtime
correspondence remain open. New copy nodes have not yet been connected to the
existing Iris/runtime ownership model. Neither checked admission nor conditional
visibility alone proves the full tiled-matmul contract.

The checked helper has a complete generated source trace and separate augmented
copy access nodes. Its no-wait variant is deliberately locally complete: later
memory admission must constrain it, rather than the interpreter silently turning
bar.sync into completion. It is assembled but never run on GPU. The waited
sixteen-byte helper is executed on sm_89 and compared exactly, including its
output guard. Group/wait source regressions and malformed-size rejection are
separate from that finite native execution.

Reference boundaries: the [paper, section 3.5](https://sf-tensor.com/papers/formalizing-ptx.pdf)
uses independent copy identities; the [PTX non-bulk copy/group/wait descriptions](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#data-movement-and-conversion-instructions-cp-async)
are the primary instruction reference. This implementation initially accepts
only the documented basic forms selected by the frontend and keeps optional
copy variants, other MMA forms, TMA and proxy constructs rejected. The required f16-input,
f32-output, 16x8x16 tiled MMA kernel and its buffer-reuse proof remain in scope.


## MMA fragment and logical f16-pair foundation

`Ampere/MmaLayout.lean` models f16 m16n8k16 fragment coordinates and their inverse
owners as equivalences. Thus every A, B and C/D element has exactly one lane/slot.
The coordinate reference is [NVIDIA PTX ISA 9.5, section 9.7.16.5.8](https://docs.nvidia.com/cuda/parallel-thread-execution/).
The reference selects the f16 layout; other formats have different coordinates.
`MmaFragments` proves gather/scatter identities for arbitrary element types and
connects exact-real fragment arithmetic to the independent matrix step.
`MmaPacked` reversibly groups scalar slots into four A and two B pairs per lane.
`PackedF16` serializes a pair as two existing symbolic f16 fragments, proves exact
decode/encode correspondence and rejects integer byte storage. It exposes no IEEE
bits and enables no bitwise float reinterpretation.

The frontend now accepts exactly
`mma.sync.aligned.m16n8k16.row.col.f32.f16.f16.f32`, plus global/shared word loads
into b32 registers. `MmaSyntax` checks the four/four/two/four register vectors,
packed b32 inputs, f32-compatible D/C and distinct destinations. `Thread` reads
all named input registers before updating D, keeps packed and integer/float
representations exclusive on writes, and emits entry/return events with actual
PC, dynamic ordinal and launch-derived warp/lane. The oracle supplies only output
values locally; it cannot supply the captured input matrices.

`MmaProtocol` requires a participant from every lane, actual matching emitted
events and source PCs, launch-derived identity, matching CTA/warp/ordinal/PC and
fragment arithmetic for every output. `CheckedConditions.mma` is mandatory.
`matched_mma_output` derives the matrix step when a kernel establishes the input
representations through execution/memory agreement. Source completion alone
continues to permit incorrect output answers; checked admission constrains them.
A one-lane source-complete candidate is rejected for every rf/co. Existing copy
witnesses discharge the new condition from the absence of MMA source instructions.

`MmaControl` connects matched warp entries to returns in `ControlEdge`; mixed
barrier/MMA cycles are rejected. This control relation is deliberately absent
from `BaseEdge`: rendezvous alone establishes no memory publication. The
[NVIDIA MMA description](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#warp-level-matrix-instructions-mma)
is the source for `.sync`/`.aligned` participation. No additional memory-fence
semantics is assumed.

`Tests/MmaWarp` constructs all 32 traces from actual source runs, proves launch
coverage, completion, source PCs and full-warp arithmetic, without using the
kernel correctness theorem. This finite positive checks source/protocol
nonvacuity only: no rf/co/observer witness is claimed. Its `launch.initial` is a
placeholder; an admissible represented initial-memory family still has to be
specified and proved against the observed word-load values. `MmaWarpMemory`
and `MmaWarpWitness` now supply that separate represented launch: actual read
and write inventories, input/output separation, unique output writers and
race freedom are derived from the source traces. Explicit initial rf, certified
InitialCo and an actual-writer-selected observer produce complete checked
source/memory/observer witnesses for the fixed all-ones instance, with every
output byte equal to f32 encoding of 16 and a preserved guard. The placeholder
integer-byte initial map is rejected for every rf/co. This closes finite
probe nonvacuity, without claiming parameterized kernel correctness.

`mma_probe.ptx` is a generated 25-instruction fragment-layout probe with six packed
loads, zero accumulators, one MMA and four stores per lane. Its native 32-thread
execution compares 528 bytes, including guards, against independent rational
matmul with exact small f16 input integers. Assembly and native tests remain
separate from formal proofs. Parameterized full memory-admitted MMA witnesses,
tiled K-loop accumulation/reuse proofs and kernel
correctness/nonvacuity remain required for the paper's
[Ampere case](https://sf-tensor.com/papers/formalizing-ptx.pdf). Neither real
arithmetic nor this finite execution establishes general IEEE/logit equivalence.


## Repeated-write witnesses and the tiled source frontier

`MemoryGraph/RankedWitness` lifts the existing ordinary graph's rank-certified
coherence construction to arbitrary nodes and source encodings. It handles
multiple writers per byte, including distinct async agents. The certificate
requires actual read-value agreement, rank-respecting po/base/rf/fr, race
freedom and writer-rank injectivity per byte; the theorem derives all seven
memory-condition fields, including SC and RMW atomicity. These are sufficient
construction duties for a chosen witness, not changes to allowed-execution
predicates or extra kernel preconditions. `RankedObservation` selects a maximal
actual writer from a finite inventory that must cover every emitted write.
The repeated-write model test has distinct operation agents and writes 7 then
42 around an intervening read; the observer returns 42 and a stale selector is
rejected. This is model-level evidence, not a source-program witness.

The new generated 83-instruction `ampere_tiled_matmul.ptx` uses block=(4,8,1),
row-major f16 A, column-major f16 B and row-major f32 C. Each CTA computes a 16x8
tile and advances K by 16. Three 8-byte copies per lane populate shared A/B;
commit/wait precede CTA publication. Six packed shared loads feed MMA, and a
second barrier prevents overwriting the shared tile before readers finish.
A local two-iteration trace records both actual static barrier PCs in alternating
dynamic generations. `uniqueBarrierSites` is false here: the full proof must
establish dynamic source matching, not assume the static sufficient certificate.

Four native exact-byte cases cover one tile, four CTAs with three K iterations,
K=0 with unused A/B aliasing C, and extra inactive CTAs with two K iterations.
All active inputs remain unchanged and C guards are preserved. The independent
host reference is rational matrix multiplication, with small exactly
representable input/products/sums. Full parameterized tiled source reconstruction,
MMA/CTA matching, read values, race freedom and shared reuse, output/frame proof
and independent complete legal witnesses remain required. Native execution and
a complete local trace do not substitute for those obligations.


`Ampere/TiledLayout` now proves parameterized shared-byte ownership and fragment
address equations for every x in Fin 4, y in Fin 8 and relevant register/half
slot. Each 8-byte cooperative copy has a unique (part,y,x,offset) owner and lies
within the 768-byte tile. Every 4-byte A/B word is located in the correct producer
copy, including the second half of an 8-byte copy, and its two f16 elements
agree with the independent MMA A/B coordinate maps. These are reusable layout
facts. Connecting them to arbitrary actual source/register states and loop
iterations is a remaining kernel proof obligation. The source explicitly bases
shared pointers on the declared tile symbol; current ptxas allocation is 768 bytes.

## Phase visibility and parameterized tiled control

`MemoryGraph.phase_writer_source` handles repeated writes without choosing a
special rf/co. For an actual eligible read r of byte l, a current actual write w
must be causally before r. Every actual writer u at l must satisfy u=w, u before w,
or r before u. Initialization is excluded by no-stale. An earlier source is
excluded by coherence followed by no-stale; a later source is excluded by
no-future. Agreement therefore forces rf(r,l)=w and the current byte value.
`phase_writer_visible` exposes the value consequence. No read-value premise or
unique-writer premise is introduced. This is a sufficient theorem about the
existing memory predicates, not a restriction added to their definition.

`Ampere.published_phase_copy_source/value` combine this rule with an actual
copy's wait, issuer arrival and peer return/read. The issuer and consumer may
be different threads. Eligibility, exhaustive writer inventory/classification
and actual source/barrier matching remain obligations. The repeated-write
ranked graph test independently admits a witness, proves the first read's rf for
all admitted witnesses, rejects a future source for every co and observes the
final overwrite. It does not establish those properties for the tiled source.

The independent `AmpereTiledSpec` now provides a canonical-grid exact-real
contract. `AmpereTiledLoop.Invariant` describes a running source state at PC 57:
counter=16*i, query=firstQuery+10*i, global copy pointers advanced by 32*i modulo
2^64, fixed shared/read/output/K registers, and represented f32 accumulators
with no conflicting integer-bank bindings. Actual instruction rules establish
preservation without assuming accumulator values. The local reply certificate
specifies three eight-byte payloads and four A/two B packed reply tags per
iteration; bytes, packed real values and MMA answers are otherwise independent.
After t remaining iterations, the actual source completes in 21*t+7 slots with
17*t+4 events. Complete-run uniqueness gives those counts to any other completed
local run from the same entry under the reply certificate.

Neither the invariant nor that certificate is added to `AmpereTiledSpec.Pre`.
They must be derived from arbitrary complete source candidates for the final
kernel proof. PC-zero initialization/masks, full-warp/CTA matching, race freedom,
actual phase order and memory values, universal output/frame correctness and a
separate independent complete legal execution witness remain open. A local
test deliberately uses inconsistent copy bytes and packed words to keep this
distinction explicit. Native overlaunch evidence remains separate from the
current canonical-grid specification; no physical allocation/IEEE claim follows.

## Complete tiled initialization and source address bounds

The PC-zero initialization frontier above is now closed for the canonical-grid
local execution theorem. `AmpereTiledInit` executes actual parameters and
special-register reads, retaining width truncation, then checks the actual CTA
guards. `AmpereTiledAddresses` executes slots 16..51 using explicit wrapped
dataflow formulas. `AmpereTiledEntry` executes the four actual zero-literal moves
and counter initialization. Its 57-slot prefix theorem establishes the loop
invariant rather than assuming it at the kernel boundary. Generic
`Ampere/FloatSteps` proves the real scalar-float update with packed-bank
invalidation; integer-bank filtering is retained throughout.

`AmpereTiledGeometry` derives non-wrapping tile bases from Layout's M/N
divisibility/bounds and valid canonical thread identities. It derives the active
guards and per-lane low/high output-row and input/output-column bounds. Complete
active local source execution/counts follow in `AmpereTiledSource`, at
64+21*(K/16) slots, conditional on the existing reply size/tag certificate.
There is no matrix-value premise. The certificate must still be extracted from
arbitrary completed source candidates; the kernel `Pre` is unchanged.

Zero K is stronger: the full 64-slot execution emits exactly the four source
stores of zero, for every oracle, without any reply certificate. Its complete
run has four events and zero queries. Unused A/B may alias C with only four-byte
alignment. Empty M exits in fifteen slots; positive M/empty N exits in seventeen,
both with no events and zero queries for every oracle. Tests include a large
valid CTA x index near the u32 boundary, maximum u64 unused pointers and an
oracle that would fail both copy-size and packed-register checks if used.

`AmpereTiledAddressRules` proves source-produced A/A-high/B/C/C-high pointer
formulas modulo 2^64. Shared source pointers reduce to the layout offsets for
arbitrary valid x/y. Actual `CopyStage.operation` destinations at every K step
and all six actual `MmaBlock.readEvents` addresses equal the earlier copy/fragment
layout functions. No read values or publication properties are inferred from
these equalities. `AmpereTiledBounds` derives the source start and entire
eight-byte extent of each active copy from Layout. A reusable strided matrix-span
inequality, tile/element bounds and step<K/16 suffice; unused zero-K inputs and
the unused final advanced pointers get no extra bounds. The last A-high/B copy
in the nonzero-coordinate three-iteration instance ends exactly at its input
buffer end, checking the full access rather than just its first byte.

Remaining obligations are extraction of active reply lengths/tags, complete
source event/copy/barrier/MMA inventory, launch-wide participation/source-site
matching, race freedom and actual phase order, memory-value agreement, universal
matrix output/frame correctness and an independent complete checked legal
launch/observer witness. Local successful source execution and address bounds
do not establish these. There is no new native run, performance optimization,
floating-point equivalence claim or change to the original full goal.

## Arbitrary completed tiled source reconstruction

Reply sizes/tags in the source constructor are now derived from actual complete
runs. Generic `Ampere/Inversion` inverts successful copy and MMA slots and
extracts a completed tail after any successful prefix. `CopyInversion` advances
through three actual issue slots, deriving all eight-byte reply lengths before
using the existing copy-stage replay theorem. It retains arbitrary prior copy
ledgers and counters. No memory value is inferred from a length check.

`RawLoads` executes the actual six shared word loads with arbitrary integer or
packed replies. Its packed-bank lookup equations account for all six writes and
for integer invalidation of old packed values. Generic MMA-step inversion
extracts the actual successful `readMmaInputs`; its six required lookups must be
present. Because each loaded word overwrote the corresponding bank entry, this
forces the six actual oracle replies to be packed. Earlier packed bindings
cannot mask an incorrect new integer reply. This conclusion uses successful
actual MMA execution, not a packed-tag kernel precondition.

`AmpereTiledReplies` combines guard/copy/raw-load/MMA reasoning and advances the
real twenty-one-slot iteration. Induction over the remaining K iterations derives
lengths and tags at every actual query. The loop preservation rule now accepts
one iteration's values independently of any certificate about future iterations;
the previous certificate API is retained as a wrapper. The derived finite query
facts can then form a `Replies` object using witnesses selected from the actual
oracle values. `AmpereTiledReconstruct` applies this after the already proved
57-slot initialization prefix, so arbitrary completed PC-zero counts no longer
require a caller-supplied reply certificate.

`AmpereTiledTrace` recursively defines the actual source state and event prefix
at each K iteration. It proves prefix execution and the exact completed
store/return trace. Every completed active source run equals one of these
canonical states/event lists, for arbitrary fuel and oracle. A candidate-level
theorem applies this to each actual member of a well-formed complete launch.
Copy/group/MMA/query counts and two barrier generations per iteration follow
from state-update equations. Old C is zero at the first MMA and the previous
actual oracle matrix answer thereafter; it is not assumed to equal the desired
partial matrix product.

`AmpereTiledEvents` gives the seventeen phase tags, actual copy operation
identities/groups/source/destination/payloads, MMA PC=71 and ordinal, exact old-C
capture and query indexing. Every in-range phase event can be selected from the
complete event list at 17*phase+slot, and output events start at 17*(K/16).
This is exact source structure. Complete byte-level graph read/write inventories,
actual barrier source PCs and full-warp/CTA matching, phase causality/races,
memory values and matrix output/frame correctness remain separate duties.

Tests refute completion at every fuel count when the third iteration's copy
reply has length seven, the second iteration's B reply is an integer, or the
third iteration's A reply is an integer. An explicit old `%rb1` packed value is
cleared by the new integer word. A positive source run permits integer `word32`
answers at all matrix-query slots, since those slots read `oracle.matrix`
instead. It preserves the intended finite query/type boundary. Canonical
three-iteration counters and event positions are checked without claiming a
memory-admitted execution or a correct matrix result. The independent full
legal witness and universal value proof remain in the original active goal.

## Actual tiled inventories and repeated shared-buffer phases

`AmpereTiledInventory` partitions the entire canonical event list into seventeen
events per K phase followed by four output events. It exhaustively classifies
copy issues, shared reads, global stores, MMA returns and both barrier halves,
and excludes RMWs. The finite slot split covers arbitrary K through the source
reconstruction theorem, rather than checking one fixed number of iterations.

`AmpereTiledGraph.SourceInfo` bundles only the original Layout/parameters/geometry,
an active output shape, actual source well-formedness and completion. The helper
is derived from the independent Pre plus provenance/completion; it adds no
inventory, race, value or rf/co premise. Completion is the existing observer-side
obligation when used by a kernel contract. Source reconstruction and actual
issue/final-ledger correspondence give every byte read/write and copy case.
Ordinary reads are shared packed words; ordinary writes are the four final
global f32 stores. Copy reads/writes stay independent operation nodes, with
actual owners and ordinals. No RMW can occur in this source family.

Positive event rules derive the actual wait and barrier events for any launched
thread and valid K phase. `AmpereTiledPhaseOrder` derives three base-order paths:
current copy write through its wait and pre-read CTA publication to a peer read;
that read through the post-read CTA barrier to any later-phase copy write;
and an earlier-phase copy write to a later-phase copy write. Different issuers
and consumers are permitted in the same CTA. These paths retain independent
copyRead/copyWrite nodes outside issuer PO and add no MMA memory-fence edge.

`AmpereTiledSharedWriters` derives that every shared-byte writer is an actual
copy, with an eight-byte footprint. At one phase, the cooperative-copy layout
makes overlapping byte owners equal, including thread z=0 and the full CTA
identity. This is not a unique-writer claim across a complete K loop. Combining
this fact with phase order gives `AmpereTiledPhaseVisibility.writer_classification`:
every competing write is current, causally before it, or causally after the read.
The existing generic phase rule then forces the current rf source and byte value
for every memory-admitted rf/co, provided the actual read is eligible. This
eligibility premise remains explicit; the complete global no-race proof is not
yet discharged. No desired byte value or chosen rf/co is assumed.

`AmpereTiledSourceCandidate` enumerates arbitrary canonical geometry with actual
completed source traces and proves duplicate-free, complete thread coverage,
provenance and completion. It accepts a supplied per-thread reply family and
does not prove its memory/warp/observer admission. `AmpereTiledAccesses` derives
existence of the actual bytes throughout copy/read footprints. The four-CTA,
three-iteration source instance has a grid/block volume of 128, tests distinct
producer/consumer lanes, waited publication, read-before-reuse and old/current
copy order, and verifies a second-word byte inside an eight-byte producer copy.
Its deliberately inconsistent value oracle is not a legal memory witness.

Global input/output separation, output-byte ownership, complete race freedom and
read eligibility remain next. Those are needed to use the conditional visibility
rule without extra caller premises. Actual barrier source-PC matching, complete
warp/CTA/control admission, initial/shared-value agreement, universal matrix/
frame correctness and an independent complete checked legal witness also remain.
No PTX, frontend, native performance or exact-logit target is changed here.
