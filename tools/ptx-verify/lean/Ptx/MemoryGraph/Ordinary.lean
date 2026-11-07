import Ptx.MemoryGraph.Observation
import Ptx.Event.Observation

/-! Ordinary candidates embed without changing memory/race/observation meaning.
Barrier participation and control remain separate construct obligations. -/
namespace Ptx.MemoryGraph.Ordinary
open Ptx.ISA
variable {ByteValue Answers : Type}

instance : Sources Ptx.Event.EventId Ptx.Event.Source where
  decode := fun s => match s with | .initial => none | .write node => some node
  encode := fun s => match s with | none => .initial | some node => .write node
  decode_encode s := by cases s <;> rfl
  encode_decode s := by cases s <;> rfl

def graph (c : Ptx.Event.Candidate ByteValue Answers) : Graph Ptx.Event.EventId ByteValue := {
  kind := c.eventAt
  present := c.Present
  agent := fun e => .thread e.thread
  po := Ptx.Event.ProgramOrder c
  base := Ptx.Event.BaseCausality c
  complete := c.Complete
}

@[simp] theorem readByte {c : Ptx.Event.Candidate ByteValue Answers} (event loc) :
    (graph c).readByte event loc = c.readByte event loc := rfl
@[simp] theorem writeByte {c : Ptx.Event.Candidate ByteValue Answers} (event loc) :
    (graph c).writeByte event loc = c.writeByte event loc := rfl
@[simp] theorem overlap {c : Ptx.Event.Candidate ByteValue Answers} (a b) :
    (graph c).Overlap a b ↔ c.Overlap a b := Iff.rfl
@[simp] theorem sameFootprint {c : Ptx.Event.Candidate ByteValue Answers} (a b) :
    (graph c).SameFootprint a b ↔ c.SameFootprint a b := Iff.rfl
@[simp] theorem rmw {c : Ptx.Event.Candidate ByteValue Answers} (event) :
    (graph c).IsRMW event ↔ c.IsRMW event := Iff.rfl
@[simp] theorem sourceByte_eq {c : Ptx.Event.Candidate ByteValue Answers} (initial loc source) :
    sourceByte (graph c) initial loc source = Ptx.Event.sourceByte c initial loc source := by cases source <;> rfl
@[simp] theorem initial_eq : (initialSource : Ptx.Event.Source) = .initial := rfl
@[simp] theorem write_eq (node : Ptx.Event.EventId) : (writeSource node : Ptx.Event.Source) = .write node := rfl

@[simp] theorem mutually_scoped {c : Ptx.Event.Candidate ByteValue Answers} (a b) :
    MutuallyScoped (graph c) a b ↔ Ptx.Event.MutuallyScoped c a b := Iff.rfl
@[simp] theorem morally_strong {c : Ptx.Event.Candidate ByteValue Answers} (a b) :
    MorallyStrong (graph c) a b ↔ Ptx.Event.MorallyStrong c a b := by
  change ((Agent.thread a.thread = Agent.thread b.thread) ∨ MutuallyScoped (graph c) a b) ∧ (graph c).SameFootprint a b ↔ _
  simp only [Agent.thread.injEq,mutually_scoped,sameFootprint,Ptx.Event.MorallyStrong]
@[simp] theorem observed {c : Ptx.Event.Candidate ByteValue Answers} {rf} (a b) :
    Observed (graph c) rf a b ↔ Ptx.Event.Observed c rf a b := by
  simp only [Observed,Ptx.Event.Observed,morally_strong,readByte,writeByte,write_eq]
@[simp] theorem observation_order {c : Ptx.Event.Candidate ByteValue Answers} {rf} (a b) :
    ObservationOrder (graph c) rf a b ↔ Ptx.Event.ObservationOrder c rf a b := by
  constructor
  · intro h
    induction h with
    | direct h => exact .direct ((observed _ _).mp h)
    | viaRMW hm _ _ ha hb => exact .viaRMW hm ha hb
  · intro h
    induction h with
    | direct h => exact .direct ((observed _ _).mpr h)
    | viaRMW hm _ _ ha hb => exact .viaRMW hm ha hb
@[simp] theorem proxy_base {c : Ptx.Event.Candidate ByteValue Answers} (a b) :
    ProxyPreservedBase (graph c) a b ↔ Ptx.Event.ProxyPreservedBase c a b := Iff.rfl
@[simp] theorem causality {c : Ptx.Event.Candidate ByteValue Answers} {rf} (a b) :
    Causality (graph c) rf a b ↔ Ptx.Event.Causality c rf a b := by
  simp only [Causality,Ptx.Event.Causality,proxy_base,observation_order]
@[simp] theorem race {c : Ptx.Event.Candidate ByteValue Answers} {rf} (a b) :
    DataRace (graph c) rf a b ↔ Ptx.Event.DataRace c rf a b := by
  constructor
  · intro h
    exact ⟨h.overlap,h.conflict,fun hb => h.notForward ((causality _ _).mpr hb),
      fun hb => h.notBackward ((causality _ _).mpr hb),fun hs => h.notStrong ((morally_strong _ _).mpr hs)⟩
  · intro h
    exact ⟨h.overlap,h.conflict,fun hb => h.notForward ((causality _ _).mp hb),
      fun hb => h.notBackward ((causality _ _).mp hb),fun hs => h.notStrong ((morally_strong _ _).mp hs)⟩
@[simp] theorem mixed_race {c : Ptx.Event.Candidate ByteValue Answers} {rf} :
    MixedSizeRace (graph c) rf ↔ Ptx.Event.MixedSizeRace c rf := by
  simp only [MixedSizeRace,Ptx.Event.MixedSizeRace,race,sameFootprint]
@[simp] theorem tainted {c : Ptx.Event.Candidate ByteValue Answers} {rf} (read loc) :
    Tainted (graph c) rf read loc ↔ Ptx.Event.Tainted c rf read loc := by
  simp only [Tainted,Ptx.Event.Tainted,race,writeByte]
@[simp] theorem eligible {c : Ptx.Event.Candidate ByteValue Answers} {rf} (read loc) :
    Eligible (graph c) rf read loc ↔ Ptx.Event.Eligible c rf read loc := by
  simp only [Eligible,Ptx.Event.Eligible,mixed_race,tainted]
@[simp] theorem agreement {c : Ptx.Event.Candidate ByteValue Answers} {initial rf} :
    ValueAgreement (graph c) initial (Eligible (graph c) rf) rf ↔
      Ptx.Event.ValueAgreement c initial (Ptx.Event.Eligible c rf) rf := by
  simp only [ValueAgreement,Ptx.Event.ValueAgreement,eligible,readByte,sourceByte_eq]

@[simp] theorem coherent {c : Ptx.Event.Candidate ByteValue Answers} {initial rf co} :
    Coherent (graph c) initial rf co ↔ Ptx.Event.Coherent c initial rf co := by
  constructor
  · intro h
    refine ⟨h.irrefl,h.transitive,?_,h.initialization,?_,?_,?_⟩
    · intro loc a b hc
      simpa only [sourceByte_eq] using h.domain loc a b hc
    · intro loc a b va vb hn ha hb hrel
      exact h.comparable loc a b va vb hn ha hb (by simpa only [morally_strong,causality] using hrel)
    · intro loc a b hr
      exact h.raceUnordered loc a b ((race _ _).mpr hr)
    · intro loc a b va vb ha hb hc
      exact h.causality loc a b va vb ha hb ((causality _ _).mpr hc)
  · intro h
    refine ⟨h.irrefl,h.transitive,?_,h.initialization,?_,?_,?_⟩
    · intro loc a b hc
      simpa only [sourceByte_eq] using h.domain loc a b hc
    · intro loc a b va vb hn ha hb hrel
      exact h.comparable loc a b va vb hn ha hb (by simpa only [morally_strong,causality] using hrel)
    · intro loc a b hr
      exact h.raceUnordered loc a b ((race _ _).mp hr)
    · intro loc a b va vb ha hb hc
      exact h.causality loc a b va vb ha hb ((causality _ _).mp hc)

@[simp] theorem causal_conditions {c : Ptx.Event.Candidate ByteValue Answers} {rf co} :
    CausalityConditions (graph c) rf co ↔ Ptx.Event.CausalityConditions c rf co := by
  constructor
  · intro h
    exact ⟨fun r w l vr vw hr hw hb => h.noFuture r w l vr vw hr hw ((causality _ _).mpr hb),
      fun w r l vw vr hw hr hb => h.noStale w r l vw vr hw hr ((causality _ _).mpr hb)⟩
  · intro h
    exact ⟨fun r w l vr vw hr hw hb => h.noFuture r w l vr vw hr hw ((causality _ _).mp hb),
      fun w r l vw vr hw hr hb => h.noStale w r l vw vr hw hr ((causality _ _).mp hb)⟩
@[simp] theorem single_copy_atomicity {c : Ptx.Event.Candidate ByteValue Answers} {rf co} :
    SingleCopyAtomicity (graph c) rf co ↔ Ptx.Event.SingleCopyAtomicity c rf co := by
  simp only [SingleCopyAtomicity,Ptx.Event.SingleCopyAtomicity,morally_strong,readByte,writeByte,write_eq]
@[simp] theorem rmw_atomicity {c : Ptx.Event.Candidate ByteValue Answers} {rf co} :
    RMWAtomicity (graph c) rf co ↔ Ptx.Event.RMWAtomicity c rf co := by
  simp only [RMWAtomicity,Ptx.Event.RMWAtomicity,rmw,morally_strong,readByte,writeByte,write_eq]
@[simp] theorem communication {c : Ptx.Event.Candidate ByteValue Answers} {rf co} (a b) :
    Communication (graph c) rf co a b ↔ Ptx.Event.Communication c rf co a b := by
  simp only [Communication,Ptx.Event.Communication,readByte,writeByte,write_eq]
@[simp] theorem sc_per_location {c : Ptx.Event.Candidate ByteValue Answers} {rf co} :
    SCPerLocation (graph c) rf co ↔ Ptx.Event.SCPerLocation c rf co := by
  simp only [SCPerLocation,Ptx.Event.SCPerLocation,morally_strong,overlap,communication]
  rfl

theorem memory_conditions_iff {c : Ptx.Event.Candidate ByteValue Answers} {initial rf co} :
    Ptx.Event.GenericMemoryConditions c initial rf co ↔
      MemoryConditions (graph c) initial rf co ∧ Ptx.Event.BarrierParticipation c ∧ Ptx.Event.BarrierControlAcyclic c := by
  constructor
  · intro h
    refine ⟨⟨h.baseAcyclic,agreement.mpr h.agreement,?_,?_,?_,?_,?_⟩,h.barriers,h.barrierControl⟩
    · intro hm; exact coherent.mpr (h.coherence (fun hmix => hm (mixed_race.mpr hmix)))
    · intro hm; exact causal_conditions.mpr (h.causality (fun hmix => hm (mixed_race.mpr hmix)))
    · intro hm; exact single_copy_atomicity.mpr (h.atomicity (fun hmix => hm (mixed_race.mpr hmix)))
    · intro hm; exact sc_per_location.mpr (h.scPerLocation (fun hmix => hm (mixed_race.mpr hmix)))
    · intro hm; exact rmw_atomicity.mpr (h.rmwAtomicity (fun hmix => hm (mixed_race.mpr hmix)))
  · rintro ⟨h,hbar,hctrl⟩
    refine ⟨h.baseAcyclic,hbar,hctrl,agreement.mp h.agreement,?_,?_,?_,?_,?_⟩
    · intro hm; exact coherent.mp (h.coherence (fun hmix => hm (mixed_race.mp hmix)))
    · intro hm; exact causal_conditions.mp (h.causality (fun hmix => hm (mixed_race.mp hmix)))
    · intro hm; exact single_copy_atomicity.mp (h.atomicity (fun hmix => hm (mixed_race.mp hmix)))
    · intro hm; exact sc_per_location.mp (h.scPerLocation (fun hmix => hm (mixed_race.mp hmix)))
    · intro hm; exact rmw_atomicity.mp (h.rmwAtomicity (fun hmix => hm (mixed_race.mp hmix)))

def observation (o : Ptx.Event.Observation ByteValue) : Observation ByteValue Ptx.Event.Source := ⟨o.domain,o.output,o.source⟩
@[simp] theorem observer_eligible {c : Ptx.Event.Candidate ByteValue Answers} {rf loc} :
    ObserverEligible (graph c) rf loc ↔ Ptx.Event.ObserverEligible c rf loc := by
  simp only [ObserverEligible,Ptx.Event.ObserverEligible,mixed_race,writeByte,race]
theorem observer_conditions_iff {c : Ptx.Event.Candidate ByteValue Answers} {initial rf co o} :
    ObserverConditions (graph c) initial rf co (observation o) ↔ Ptx.Event.ObserverConditions c initial rf co o := by
  constructor
  · intro h
    refine ⟨h.complete,h.globalOnly,?_,?_⟩
    · intro loc hd he
      exact (sourceByte_eq initial loc (o.source loc)) ▸ h.agreement loc hd (observer_eligible.mpr he)
    · intro loc hd hm writer value hw
      exact h.noStale loc hd (fun hmix => hm (mixed_race.mp hmix)) writer value hw
  · intro h
    refine ⟨h.complete,h.globalOnly,?_,?_⟩
    · intro loc hd he
      exact (sourceByte_eq initial loc (o.source loc)).symm ▸ h.agreement loc hd (observer_eligible.mp he)
    · intro loc hd hm writer value hw
      exact h.noStale loc hd (fun hmix => hm (mixed_race.mpr hmix)) writer value hw

end Ptx.MemoryGraph.Ordinary
