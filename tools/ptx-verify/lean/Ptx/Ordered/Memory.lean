import Ptx.Ordered.Execution

/-! Generic-proxy scoped memory predicates for the explicit ordered layer.
Scopes affect morally-strong accesses, observation, races and value eligibility,
not just a release/acquire edge added to the old weak predicates. All conditions
are definitions over source candidates, not Lean axioms or assumed lemmas.
Only direct ordered load/store patterns are added; fence/extended patterns,
cross-proxy operations and host/multi-device system scope are outside this layer.
Reference: PTX ISA 9.4 sections 8.7--8.10. NTA is omitted, as in the base model. -/
namespace Ptx.Ordered
open Ptx.ISA Ptx.Event
noncomputable section

def Kind.strongScope (kind : Kind) : Option Scope :=
  kind.scope.orElse (fun _ => kind.event.strongScope)

def MutuallyScoped (candidate : Candidate) (a b : EventId) : Prop :=
  ∃ sa sb, (candidate.kindAt a).bind Kind.strongScope = some sa ∧
    (candidate.kindAt b).bind Kind.strongScope = some sb ∧
    sa.Includes a.thread b.thread ∧ sb.Includes b.thread a.thread
def MorallyStrong (candidate : Candidate) (a b : EventId) : Prop :=
  (a.thread = b.thread ∨ MutuallyScoped candidate a b) ∧ candidate.view.SameFootprint a b

def Observed (candidate : Candidate) (rf : ReadsFrom) (writer reader : EventId) : Prop :=
  MorallyStrong candidate writer reader ∧ ∃ loc value,
    candidate.view.readByte reader loc = some value ∧ rf reader loc = .write writer ∧
    (candidate.view.writeByte writer loc).isSome = true
inductive ObservationOrder (candidate : Candidate) (rf : ReadsFrom) : EventId → EventId → Prop
  | direct {a b} : Observed candidate rf a b → ObservationOrder candidate rf a b
  | viaRMW {a middle b} : candidate.view.IsRMW middle → ObservationOrder candidate rf a middle →
      ObservationOrder candidate rf middle b → ObservationOrder candidate rf a b

def ReleaseAcquireSync (candidate : Candidate) (rf : ReadsFrom) (release acquire : EventId) : Prop :=
  ((candidate.kindAt release).map Kind.order = some .release) ∧
  ((candidate.kindAt acquire).map Kind.order = some .acquire) ∧
  MorallyStrong candidate release acquire ∧ ObservationOrder candidate rf release acquire

def BaseCausality (candidate : Candidate) (rf : ReadsFrom) : EventId → EventId → Prop :=
  Path (fun a b => ProgramOrder candidate.view a b ∨ BarrierSync candidate.view a b ∨ ReleaseAcquireSync candidate rf a b)
def Causality (candidate : Candidate) (rf : ReadsFrom) (a b : EventId) : Prop :=
  (candidate.view.Overlap a b ∧ BaseCausality candidate rf a b) ∨
    ∃ middle, ObservationOrder candidate rf a middle ∧ candidate.view.Overlap middle b ∧ BaseCausality candidate rf middle b

structure DataRace (candidate : Candidate) (rf : ReadsFrom) (a b : EventId) : Prop where
  overlap : candidate.view.Overlap a b
  conflict : candidate.view.Writes a ∨ candidate.view.Writes b
  notForward : ¬Causality candidate rf a b
  notBackward : ¬Causality candidate rf b a
  notStrong : ¬MorallyStrong candidate a b
def MixedSizeRace (candidate : Candidate) (rf : ReadsFrom) : Prop :=
  ∃ a b, DataRace candidate rf a b ∧ ¬candidate.view.SameFootprint a b
def Tainted (candidate : Candidate) (rf : ReadsFrom) (read : EventId) (loc : Location) : Prop :=
  (∃ writer, (candidate.view.writeByte writer loc).isSome = true ∧ DataRace candidate rf read writer) ∨
  ∃ a b, (candidate.view.writeByte a loc).isSome = true ∧ (candidate.view.writeByte b loc).isSome = true ∧ DataRace candidate rf a b
def Eligible (candidate : Candidate) (rf : ReadsFrom) (read : EventId) (loc : Location) : Prop :=
  ¬MixedSizeRace candidate rf ∧ ¬Tainted candidate rf read loc

structure Coherent (candidate : Candidate) (initial : Scalar.ByteMap) (rf : ReadsFrom) (co : Coherence) : Prop where
  irrefl : ∀ loc a, ¬co loc a a
  transitive : ∀ loc a b d, co loc a b → co loc b d → co loc a d
  domain : ∀ loc a b, co loc a b →
    (sourceByte candidate.view initial loc a).isSome = true ∧ (sourceByte candidate.view initial loc b).isSome = true
  initialization : ∀ loc writer value, candidate.view.writeByte writer loc = some value → co loc .initial (.write writer)
  comparable : ∀ loc a b va vb, a ≠ b → candidate.view.writeByte a loc = some va →
    candidate.view.writeByte b loc = some vb →
    (MorallyStrong candidate a b ∨ Causality candidate rf a b ∨ Causality candidate rf b a) →
    co loc (.write a) (.write b) ∨ co loc (.write b) (.write a)
  raceUnordered : ∀ loc a b, DataRace candidate rf a b → ¬co loc (.write a) (.write b)
  causality : ∀ loc a b va vb, candidate.view.writeByte a loc = some va → candidate.view.writeByte b loc = some vb →
    Causality candidate rf a b → co loc (.write a) (.write b)
structure CausalityConditions (candidate : Candidate) (rf : ReadsFrom) (co : Coherence) : Prop where
  noFuture : ∀ read writer loc vr vw, candidate.view.readByte read loc = some vr →
    candidate.view.writeByte writer loc = some vw → Causality candidate rf read writer → rf read loc ≠ .write writer
  noStale : ∀ writer read loc vw vr, candidate.view.writeByte writer loc = some vw →
    candidate.view.readByte read loc = some vr → Causality candidate rf writer read → ¬co loc (rf read loc) (.write writer)
def SingleCopyAtomicity (candidate : Candidate) (rf : ReadsFrom) (co : Coherence) : Prop :=
  ∀ read writer, MorallyStrong candidate read writer → ∀ loc vr vw,
    candidate.view.readByte read loc = some vr → candidate.view.writeByte writer loc = some vw → rf read loc = .write writer →
    ∀ other vr' vw', candidate.view.readByte read other = some vr' → candidate.view.writeByte writer other = some vw' →
      ¬co other (rf read other) (.write writer)
def RMWAtomicity (candidate : Candidate) (rf : ReadsFrom) (co : Coherence) : Prop :=
  ∀ atomic writer, candidate.view.IsRMW atomic → MorallyStrong candidate atomic writer → ∀ loc vr vw,
    candidate.view.readByte atomic loc = some vr → candidate.view.writeByte writer loc = some vw →
    co loc (rf atomic loc) (.write writer) → ∀ other va vb,
      candidate.view.writeByte atomic other = some va → candidate.view.writeByte writer other = some vb →
        ¬co other (.write writer) (.write atomic)
def SCPerLocation (candidate : Candidate) (rf : ReadsFrom) (co : Coherence) : Prop :=
  ∀ members : EventId → Prop, (∀ a, members a → candidate.view.Present a) →
    (∀ a b, members a → members b → MorallyStrong candidate a b ∧ candidate.view.Overlap a b) →
    ∀ a, members a → ¬Path (fun x y => members x ∧ members y ∧
      (ProgramOrder candidate.view x y ∨ Communication candidate.view rf co x y)) a a

structure MemoryConditions (candidate : Candidate) (initial : Scalar.ByteMap) (rf : ReadsFrom) (co : Coherence) : Prop where
  baseAcyclic : ∀ event, ¬BaseCausality candidate rf event event
  barriers : BarrierParticipation candidate.view
  barrierControl : BarrierControlAcyclic candidate.view
  agreement : ValueAgreement candidate.view initial (Eligible candidate rf) rf
  coherence : ¬MixedSizeRace candidate rf → Coherent candidate initial rf co
  causality : ¬MixedSizeRace candidate rf → CausalityConditions candidate rf co
  atomicity : ¬MixedSizeRace candidate rf → SingleCopyAtomicity candidate rf co
  scPerLocation : ¬MixedSizeRace candidate rf → SCPerLocation candidate rf co
  rmwAtomicity : ¬MixedSizeRace candidate rf → RMWAtomicity candidate rf co

theorem program_causal {candidate rf a b} (hp : ProgramOrder candidate.view a b) : BaseCausality candidate rf a b :=
  .single (.inl hp)
theorem release_acquire_causal {candidate rf a b} (hs : ReleaseAcquireSync candidate rf a b) :
    BaseCausality candidate rf a b := .single (.inr (.inr hs))
theorem publish_release_acquire {candidate rf writer release acquire reader}
    (hw : ProgramOrder candidate.view writer release) (hs : ReleaseAcquireSync candidate rf release acquire)
    (hr : ProgramOrder candidate.view acquire reader) : BaseCausality candidate rf writer reader :=
  .trans (program_causal hw) (.trans (release_acquire_causal hs) (program_causal hr))

theorem causal_read_unique_writer {candidate initial rf co read writer loc vr vw}
    (hm : MemoryConditions candidate initial rf co) (he : Eligible candidate rf read loc)
    (hr : candidate.view.readByte read loc = some vr) (hw : candidate.view.writeByte writer loc = some vw)
    (hc : Causality candidate rf writer read)
    (hu : ∀ other value, candidate.view.writeByte other loc = some value → other = writer) : vr = vw := by
  have ha := hm.agreement read loc vr he hr
  cases hs : rf read loc with
  | initial =>
    exact False.elim ((hm.causality he.1).noStale writer read loc vw vr hw hr hc
      (by simpa only [hs] using (hm.coherence he.1).initialization loc writer vw hw))
  | write other =>
    have hwrite : candidate.view.writeByte other loc = some vr := by simpa [sourceByte,hs] using ha
    have hi := hu other vr hwrite
    subst other
    exact Option.some.inj (hwrite.symm.trans hw)

theorem message_passing_value {candidate initial rf co writer release acquire reader loc vr vw}
    (hm : MemoryConditions candidate initial rf co) (he : Eligible candidate rf reader loc)
    (hr : candidate.view.readByte reader loc = some vr) (hw : candidate.view.writeByte writer loc = some vw)
    (hpw : ProgramOrder candidate.view writer release) (hs : ReleaseAcquireSync candidate rf release acquire)
    (hpr : ProgramOrder candidate.view acquire reader)
    (hu : ∀ other value, candidate.view.writeByte other loc = some value → other = writer) : vr = vw := by
  have hoverlap : candidate.view.Overlap writer reader :=
    ⟨loc,Or.inr (by rw [hw]; rfl),Or.inl (by rw [hr]; rfl)⟩
  exact causal_read_unique_writer hm he hr hw (.inl ⟨hoverlap,publish_release_acquire hpw hs hpr⟩) hu

end
end Ptx.Ordered
