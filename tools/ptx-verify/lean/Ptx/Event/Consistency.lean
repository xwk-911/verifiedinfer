import Ptx.Event.Relations

/-! Generic-proxy memory predicates, polymorphic in the stored byte/fragment type.
Ordinary accesses are weak; relaxed RMWs retain their scope. Acquire/release,
fences, other proxies and the full PTX correspondence are not established here.
The conditions follow PTX ISA 9.4 sections 8.7–8.10, omitting NTA as in the paper.
These are Lean predicates, not axiom declarations. This layer still needs launch
allocation/UB obligations, synchronized observer outputs and a model correspondence
proof before operational kernel contracts can be transferred to it.
-/
namespace Ptx.Event
open Ptx.ISA

variable {ByteValue Answers : Type}

def Kind.strongScope (kind : Kind ByteValue) : Option Scope :=
  match kind with | .rmw scope _ _ => some scope | _ => none

def MutuallyScoped (c : Candidate ByteValue Answers) (a b : EventId) : Prop :=
  ∃ sa sb, (c.eventAt a).bind Kind.strongScope = some sa ∧
    (c.eventAt b).bind Kind.strongScope = some sb ∧
    sa.Includes a.thread b.thread ∧ sb.Includes b.thread a.thread

/-- The current instructions all use the generic proxy. Both operations must
include one another's thread, and their byte footprints must match completely. -/
def MorallyStrong (c : Candidate ByteValue Answers) (a b : EventId) : Prop :=
  (a.thread = b.thread ∨ MutuallyScoped c a b) ∧ c.SameFootprint a b

theorem scope_requires_rmw {c : Candidate ByteValue Answers} {event scope}
    (hs : (c.eventAt event).bind Kind.strongScope = some scope) : c.IsRMW event := by
  cases he : c.eventAt event with
  | none => simp [he] at hs
  | some kind =>
    cases kind with
    | rmw s base bytes => exact ⟨s,base,bytes,he⟩
    | _ => simp [he,Kind.strongScope] at hs

theorem morally_strong_of_no_rmw {c : Candidate ByteValue Answers} {a b}
    (hn : ¬ c.IsRMW a) : MorallyStrong c a b ↔ a.thread = b.thread ∧ c.SameFootprint a b := by
  constructor
  · rintro ⟨he | ⟨_,_,hs,_,_,_⟩,hf⟩
    · exact ⟨he,hf⟩
    · exact (hn (scope_requires_rmw hs)).elim
  · rintro ⟨he,hf⟩; exact ⟨Or.inl he,hf⟩

theorem write_self_strong {c : Candidate ByteValue Answers} {event loc value}
    (hw : c.writeByte event loc = some value) : MorallyStrong c event event := by
  cases he : c.eventAt event with
  | none => simp [Candidate.writeByte,he] at hw
  | some kind =>
    cases kind with
    | write base bytes =>
      exact ⟨Or.inl rfl,(base,bytes.length),by simp [he,Kind.footprint],by simp [he,Kind.footprint]⟩
    | rmw scope base bytes =>
      exact ⟨Or.inl rfl,(base,bytes.before.length),by simp [he,Kind.footprint],by simp [he,Kind.footprint]⟩
    | read base bytes => simp [Candidate.writeByte,he,Kind.writeByte] at hw
    | barrierArrival bid generation => simp [Candidate.writeByte,he,Kind.writeByte] at hw
    | barrierReturn bid generation => simp [Candidate.writeByte,he,Kind.writeByte] at hw

def Observed (c : Candidate ByteValue Answers) (rf : ReadsFrom) (write read : EventId) : Prop :=
  MorallyStrong c write read ∧ ∃ loc value,
    c.readByte read loc = some value ∧ rf read loc = .write write ∧
    (c.writeByte write loc).isSome = true

/-- Observation may pass through RMWs, but not through arbitrary intervening
reads/writes. Relaxed observation is not itself cross-thread causality. -/
inductive ObservationOrder (c : Candidate ByteValue Answers) (rf : ReadsFrom) : EventId → EventId → Prop
  | direct {a b} : Observed c rf a b → ObservationOrder c rf a b
  | viaRMW {a middle b} : c.IsRMW middle → ObservationOrder c rf a middle →
      ObservationOrder c rf middle b → ObservationOrder c rf a b

theorem observation_order_of_no_rmw {c : Candidate ByteValue Answers} {rf a b}
    (hn : ∀ event, ¬ c.IsRMW event) : ObservationOrder c rf a b ↔ Observed c rf a b := by
  constructor
  · intro ho
    cases ho with
    | direct h => exact h
    | viaRMW hm _ _ => exact (hn _ hm).elim
  · exact ObservationOrder.direct

def ProxyPreservedBase (c : Candidate ByteValue Answers) (a b : EventId) : Prop :=
  c.Overlap a b ∧ BaseCausality c a b

/-- Causality is not closed transitively beyond the ISA's definition. -/
def Causality (c : Candidate ByteValue Answers) (rf : ReadsFrom) (a b : EventId) : Prop :=
  ProxyPreservedBase c a b ∨
    ∃ middle, ObservationOrder c rf a middle ∧ ProxyPreservedBase c middle b

structure DataRace (c : Candidate ByteValue Answers) (rf : ReadsFrom) (a b : EventId) : Prop where
  overlap : c.Overlap a b
  conflict : c.Writes a ∨ c.Writes b
  notForward : ¬ Causality c rf a b
  notBackward : ¬ Causality c rf b a
  notStrong : ¬ MorallyStrong c a b

def MixedSizeRace (c : Candidate ByteValue Answers) (rf : ReadsFrom) : Prop :=
  ∃ a b, DataRace c rf a b ∧ ¬ c.SameFootprint a b

/-- A read is also tainted by racing writes to a byte it reads, even when that
read does not itself race with either write. Mixed-size races disable all the
memory-model conditions below, rather than being silently filtered out. -/
def Tainted (c : Candidate ByteValue Answers) (rf : ReadsFrom) (read : EventId) (loc : Location) : Prop :=
  (∃ write, (c.writeByte write loc).isSome = true ∧ DataRace c rf read write) ∨
  (∃ a b, (c.writeByte a loc).isSome = true ∧ (c.writeByte b loc).isSome = true ∧
    DataRace c rf a b)

def Eligible (c : Candidate ByteValue Answers) (rf : ReadsFrom) (read : EventId) (loc : Location) : Prop :=
  ¬ MixedSizeRace c rf ∧ ¬ Tainted c rf read loc

abbrev Coherence := Location → Source → Source → Prop

structure Coherent (c : Candidate ByteValue Answers) (initial : ByteMap ByteValue) (rf : ReadsFrom)
    (co : Coherence) : Prop where
  irrefl : ∀ loc a, ¬ co loc a a
  transitive : ∀ loc a b d, co loc a b → co loc b d → co loc a d
  domain : ∀ loc a b, co loc a b →
    (sourceByte c initial loc a).isSome = true ∧ (sourceByte c initial loc b).isSome = true
  initialization : ∀ loc writer value, c.writeByte writer loc = some value →
    co loc .initial (.write writer)
  comparable : ∀ loc a b va vb, a ≠ b →
    c.writeByte a loc = some va → c.writeByte b loc = some vb →
    (MorallyStrong c a b ∨ Causality c rf a b ∨ Causality c rf b a) →
    co loc (.write a) (.write b) ∨ co loc (.write b) (.write a)
  raceUnordered : ∀ loc a b, DataRace c rf a b →
    ¬ co loc (.write a) (.write b)
  causality : ∀ loc a b va vb, c.writeByte a loc = some va →
    c.writeByte b loc = some vb → Causality c rf a b → co loc (.write a) (.write b)

structure CausalityConditions (c : Candidate ByteValue Answers) (rf : ReadsFrom) (co : Coherence) : Prop where
  noFuture : ∀ read writer loc vr vw, c.readByte read loc = some vr →
    c.writeByte writer loc = some vw → Causality c rf read writer →
    rf read loc ≠ .write writer
  noStale : ∀ writer read loc vw vr, c.writeByte writer loc = some vw →
    c.readByte read loc = some vr → Causality c rf writer read →
    ¬ co loc (rf read loc) (.write writer)

def SingleCopyAtomicity (c : Candidate ByteValue Answers) (rf : ReadsFrom) (co : Coherence) : Prop :=
  ∀ read writer, MorallyStrong c read writer →
    ∀ loc vr vw, c.readByte read loc = some vr → c.writeByte writer loc = some vw →
      rf read loc = .write writer →
      ∀ other vr' vw', c.readByte read other = some vr' →
        c.writeByte writer other = some vw' → ¬ co other (rf read other) (.write writer)

/-- An RMW cannot read before a morally strong overlapping modification that
precedes its own write. The source byte and ordering byte may differ. -/
def RMWAtomicity (c : Candidate ByteValue Answers) (rf : ReadsFrom) (co : Coherence) : Prop :=
  ∀ atomic writer, c.IsRMW atomic → MorallyStrong c atomic writer →
    ∀ loc vr vw, c.readByte atomic loc = some vr → c.writeByte writer loc = some vw →
      co loc (rf atomic loc) (.write writer) →
      ∀ other va vb, c.writeByte atomic other = some va → c.writeByte writer other = some vb →
        ¬ co other (.write writer) (.write atomic)

def Communication (c : Candidate ByteValue Answers) (rf : ReadsFrom) (co : Coherence)
    (a b : EventId) : Prop :=
  (∃ loc value, c.readByte b loc = some value ∧ rf b loc = .write a ∧
    (c.writeByte a loc).isSome = true) ∨
  (∃ loc, co loc (.write a) (.write b)) ∨
  -- An unsplit RMW's internal read-to-own-write step is not an inter-operation
  -- from-read edge. Reads-from-self remains represented by the first case.
  (a ≠ b ∧ ∃ loc value, c.readByte a loc = some value ∧ co loc (rf a loc) (.write b))

/-- SC-per-location applies within pairwise morally strong overlapping slices,
not to all communication between arbitrary weak accesses in the grid. -/
def SCPerLocation (c : Candidate ByteValue Answers) (rf : ReadsFrom) (co : Coherence) : Prop :=
  ∀ members : EventId → Prop,
    (∀ a, members a → c.Present a) →
    (∀ a b, members a → members b → MorallyStrong c a b ∧ c.Overlap a b) →
    ∀ a, members a → ¬ Path (fun x y => members x ∧ members y ∧
      (ProgramOrder c x y ∨ Communication c rf co x y)) a a

/-- Current generic memory constraints. Mixed-size races relax the memory
conditions; they do not make the candidate disappear. Complete kernel correctness
additionally needs provenance, API observation and explicit launch preconditions. -/
structure GenericMemoryConditions (c : Candidate ByteValue Answers) (initial : ByteMap ByteValue)
    (rf : ReadsFrom) (co : Coherence) : Prop where
  baseAcyclic : BaseAcyclic c
  barriers : BarrierParticipation c
  barrierControl : BarrierControlAcyclic c
  agreement : ValueAgreement c initial (Eligible c rf) rf
  coherence : ¬ MixedSizeRace c rf → Coherent c initial rf co
  causality : ¬ MixedSizeRace c rf → CausalityConditions c rf co
  atomicity : ¬ MixedSizeRace c rf → SingleCopyAtomicity c rf co
  scPerLocation : ¬ MixedSizeRace c rf → SCPerLocation c rf co
  rmwAtomicity : ¬ MixedSizeRace c rf → RMWAtomicity c rf co

theorem causal_of_base {c : Candidate ByteValue Answers} {rf a b} (ho : c.Overlap a b) (hb : BaseCausality c a b) :
    Causality c rf a b := .inl ⟨ho, hb⟩

theorem barrier_memory_causal {c : Candidate ByteValue Answers} {rf write arrive leave read}
    (ho : c.Overlap write read) (hw : ProgramOrder c write arrive)
    (hs : BarrierSync c arrive leave) (hr : ProgramOrder c leave read) :
    Causality c rf write read :=
  causal_of_base ho (publish_across_barrier hw hs hr)

theorem mixed_size_disables_eligibility {c : Candidate ByteValue Answers} {rf} (hm : MixedSizeRace c rf) (read loc) :
    ¬ Eligible c rf read loc := fun he => he.1 hm

theorem race_taints_read {c : Candidate ByteValue Answers} {rf read writer loc}
    (hw : (c.writeByte writer loc).isSome = true) (hr : DataRace c rf read writer) :
    Tainted c rf read loc := .inl ⟨writer, hw, hr⟩

theorem stale_initial_forbidden {c : Candidate ByteValue Answers} {initial rf co writer read loc vw vr}
    (hc : GenericMemoryConditions c initial rf co) (hm : ¬ MixedSizeRace c rf)
    (hw : c.writeByte writer loc = some vw) (hr : c.readByte read loc = some vr)
    (hbefore : Causality c rf writer read) : rf read loc ≠ .initial := by
  intro hi
  exact (hc.causality hm).noStale writer read loc vw vr hw hr hbefore
    (hi ▸ (hc.coherence hm).initialization loc writer vw hw)

/-- Any eligible read causally after the only writer of its byte sees that
writer. Eligibility and writer uniqueness are explicit proof obligations. -/
theorem unique_writer_visible {c : Candidate ByteValue Answers} {initial rf co writer read loc vw vr}
    (hc : GenericMemoryConditions c initial rf co) (he : Eligible c rf read loc)
    (hw : c.writeByte writer loc = some vw) (hr : c.readByte read loc = some vr)
    (hbefore : Causality c rf writer read)
    (hu : ∀ other value, c.writeByte other loc = some value → other = writer) : vr = vw := by
  cases hs : rf read loc with
  | initial => exact False.elim (stale_initial_forbidden hc he.1 hw hr hbefore hs)
  | write other =>
    have hv := write_read_value hc.agreement he hr hs
    have hid := hu other vr hv
    subst other
    exact Option.some.inj (hv.symm.trans hw)

theorem no_writes_no_race {c : Candidate ByteValue Answers} {rf} (hn : ∀ writer loc, c.writeByte writer loc = none) (a b) :
    ¬ DataRace c rf a b := by
  intro hr
  rcases hr.conflict with ⟨loc, value, hv⟩ | ⟨loc, value, hv⟩
  all_goals simp [hn] at hv

theorem no_writes_eligible {c : Candidate ByteValue Answers} {rf} (hn : ∀ writer loc, c.writeByte writer loc = none) (read loc) :
    Eligible c rf read loc := by
  constructor
  · rintro ⟨a,b,hr,_⟩
    exact no_writes_no_race hn a b hr
  · rintro (⟨w,hw,_⟩ | ⟨a,b,ha,_,_⟩)
    · simp [hn] at hw
    · simp [hn] at ha

theorem race_free_eligible {c : Candidate ByteValue Answers} {rf} (hn : ∀ a b, ¬ DataRace c rf a b) (read loc) :
    Eligible c rf read loc := by
  constructor
  · rintro ⟨a,b,hr,_⟩
    exact hn a b hr
  · rintro (⟨w,_,hr⟩ | ⟨a,b,_,_,hr⟩)
    · exact hn read w hr
    · exact hn a b hr

/-- A constructive consistency rule for read-only graphs. It uses the actual
initial map and emitted read values, and does not assume the desired conclusion
or require all PTX reads globally to be race-free. -/
theorem read_only_conditions {c : Candidate ByteValue Answers} {initial}
    (hn : ∀ writer loc, c.writeByte writer loc = none)
    (hb : BaseAcyclic c) (hp : BarrierParticipation c) (hx : BarrierControlAcyclic c)
    (hr : ∀ read loc value, c.readByte read loc = some value → value = initial loc) :
    GenericMemoryConditions c initial (fun _ _ => .initial) (fun _ _ _ => False) := by
  have hw : ∀ writer loc value, c.writeByte writer loc = some value → False := by
    intro writer loc value h
    simp [hn] at h
  refine ⟨hb, hp, hx, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro read loc value _ h
    simpa [sourceByte] using congrArg some (hr read loc value h).symm
  · intro _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · intro loc writer value h; exact (hw writer loc value h).elim
    · intro loc a b va vb _ ha; exact (hw a loc va ha).elim
    · simp
    · intro loc a b va vb ha; exact (hw a loc va ha).elim
  · intro _
    constructor
    · intro read writer loc vr vw _ h; exact (hw writer loc vw h).elim
    · intro writer read loc vw vr h; exact (hw writer loc vw h).elim
  · intro _ read writer _ loc vr vw _ h
    exact (hw writer loc vw h).elim
  · intro _ members _ _ a _ hpath
    have hlt := Path.rank_lt (fun e : EventId => e.serial) (r := fun x y =>
      members x ∧ members y ∧ (ProgramOrder c x y ∨
        Communication c (fun _ _ => .initial) (fun _ _ _ => False) x y))
      (by
        intro x y hedge
        rcases hedge.2.2 with hpo | hcom
        · exact hpo.2.2.2
        · simp [Communication] at hcom) hpath
    omega

  · intro _ atomic writer _ _ loc vr vw _ _ hco
    exact False.elim hco

end Ptx.Event
