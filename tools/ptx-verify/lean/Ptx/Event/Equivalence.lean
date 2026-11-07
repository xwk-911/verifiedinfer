import Ptx.Event.Observation

/-! Transport ordinary memory reasoning across equal event views. This permits
different trace-list order, unused oracle answers and proof metadata. Barrier
participation/control and completion depend on trace metadata, so target proofs
of those obligations are explicit rather than inferred from event equality.
-/
namespace Ptx.Event
open Ptx.ISA

variable {ByteValue Answers : Type}

abbrev SameEvents (c d : Candidate ByteValue Answers) : Prop := c.eventAt = d.eventAt

namespace SameEvents

theorem reads {c d : Candidate ByteValue Answers} (h : SameEvents c d) : c.readByte = d.readByte := by
  funext id loc
  simp only [Candidate.readByte]
  rw [h]

theorem writes {c d : Candidate ByteValue Answers} (h : SameEvents c d) : c.writeByte = d.writeByte := by
  funext id loc
  simp only [Candidate.writeByte]
  rw [h]

theorem sources {c d : Candidate ByteValue Answers} (h : SameEvents c d) (initial : ByteMap ByteValue) :
    sourceByte c initial = sourceByte d initial := by
  funext loc source
  cases source with
  | initial => rfl
  | write id => exact congrFun (congrFun (writes h) id) loc

theorem accesses {c d : Candidate ByteValue Answers} (h : SameEvents c d) : c.Accesses = d.Accesses := by
  funext id loc
  simp only [Candidate.Accesses, reads h, writes h]

theorem write_accesses {c d : Candidate ByteValue Answers} (h : SameEvents c d) : c.Writes = d.Writes := by
  funext id
  simp only [Candidate.Writes, writes h]

theorem overlaps {c d : Candidate ByteValue Answers} (h : SameEvents c d) : c.Overlap = d.Overlap := by
  funext a b
  simp only [Candidate.Overlap, accesses h]

theorem footprints {c d : Candidate ByteValue Answers} (h : SameEvents c d) : c.SameFootprint = d.SameFootprint := by
  funext a b
  simp only [Candidate.SameFootprint]
  rw [h]

theorem present {c d : Candidate ByteValue Answers} (h : SameEvents c d) : c.Present = d.Present := by
  funext id
  simp only [Candidate.Present]
  rw [h]

theorem program_order {c d : Candidate ByteValue Answers} (h : SameEvents c d) : ProgramOrder c = ProgramOrder d := by
  funext a b
  simp only [ProgramOrder, present h]

theorem synchronization {c d : Candidate ByteValue Answers} (h : SameEvents c d) : BarrierSync c = BarrierSync d := by
  funext a b
  simp only [BarrierSync]
  rw [h]

theorem base {c d : Candidate ByteValue Answers} (h : SameEvents c d) : BaseCausality c = BaseCausality d := by
  simp only [BaseCausality, program_order h, synchronization h]

theorem strong {c d : Candidate ByteValue Answers} (h : SameEvents c d) : MorallyStrong c = MorallyStrong d := by
  funext a b
  simp only [MorallyStrong,MutuallyScoped, footprints h,h]

theorem is_rmw {c d : Candidate ByteValue Answers} (h : SameEvents c d) : c.IsRMW = d.IsRMW := by
  funext event
  simp only [Candidate.IsRMW,h]

theorem observed {c d : Candidate ByteValue Answers} (h : SameEvents c d) (rf : ReadsFrom) : Observed c rf = Observed d rf := by
  funext a b
  simp only [Observed, strong h, reads h, writes h]

theorem observation_order_imp {c d : Candidate ByteValue Answers} {rf a b} (h : SameEvents c d)
    (ho : ObservationOrder c rf a b) : ObservationOrder d rf a b := by
  induction ho with
  | direct he => exact .direct (by simpa only [observed h rf] using he)
  | viaRMW hm _ _ ih₁ ih₂ => exact .viaRMW (by simpa only [is_rmw h] using hm) ih₁ ih₂

theorem observation_order {c d : Candidate ByteValue Answers} (h : SameEvents c d) (rf : ReadsFrom) :
    ObservationOrder c rf = ObservationOrder d rf := by
  funext a b
  exact propext ⟨observation_order_imp h,observation_order_imp h.symm⟩

theorem proxy_base {c d : Candidate ByteValue Answers} (h : SameEvents c d) : ProxyPreservedBase c = ProxyPreservedBase d := by
  funext a b
  simp only [ProxyPreservedBase, overlaps h, base h]

theorem cause {c d : Candidate ByteValue Answers} (h : SameEvents c d) (rf : ReadsFrom) : Causality c rf = Causality d rf := by
  funext a b
  simp only [Causality, proxy_base h, observation_order h rf]

theorem race_imp {c d : Candidate ByteValue Answers} {rf a b} (h : SameEvents c d) (hr : DataRace c rf a b) : DataRace d rf a b where
  overlap := by simpa only [overlaps h] using hr.overlap
  conflict := by simpa only [write_accesses h] using hr.conflict
  notForward := by simpa only [cause h rf] using hr.notForward
  notBackward := by simpa only [cause h rf] using hr.notBackward
  notStrong := by simpa only [strong h] using hr.notStrong

theorem races {c d : Candidate ByteValue Answers} (h : SameEvents c d) (rf : ReadsFrom) : DataRace c rf = DataRace d rf := by
  funext a b
  exact propext ⟨race_imp h, race_imp h.symm⟩

theorem mixed {c d : Candidate ByteValue Answers} (h : SameEvents c d) (rf : ReadsFrom) : MixedSizeRace c rf = MixedSizeRace d rf := by
  simp only [MixedSizeRace, races h rf, footprints h]

theorem tainted {c d : Candidate ByteValue Answers} (h : SameEvents c d) (rf : ReadsFrom) : Tainted c rf = Tainted d rf := by
  funext read loc
  simp only [Tainted, writes h, races h rf]

theorem eligible {c d : Candidate ByteValue Answers} (h : SameEvents c d) (rf : ReadsFrom) : Eligible c rf = Eligible d rf := by
  funext read loc
  simp only [Eligible, mixed h rf, tainted h rf]

theorem coherent {c d : Candidate ByteValue Answers} {initial rf co} (h : SameEvents c d) (hc : Coherent c initial rf co) :
    Coherent d initial rf co where
  irrefl := hc.irrefl
  transitive := hc.transitive
  domain := by simpa only [sources h initial] using hc.domain
  initialization := by simpa only [writes h] using hc.initialization
  comparable := by simpa only [writes h, strong h, cause h rf] using hc.comparable
  raceUnordered := by simpa only [races h rf] using hc.raceUnordered
  causality := by simpa only [writes h, cause h rf] using hc.causality

theorem causal_conditions {c d : Candidate ByteValue Answers} {rf co} (h : SameEvents c d) (hc : CausalityConditions c rf co) :
    CausalityConditions d rf co where
  noFuture := by simpa only [reads h, writes h, cause h rf] using hc.noFuture
  noStale := by simpa only [reads h, writes h, cause h rf] using hc.noStale

theorem communication {c d : Candidate ByteValue Answers} (h : SameEvents c d) (rf : ReadsFrom) (co : Coherence) :
    Communication c rf co = Communication d rf co := by
  funext a b
  simp only [Communication, reads h, writes h]

theorem memory {c d : Candidate ByteValue Answers} {initial rf co} (h : SameEvents c d)
    (hb : BarrierParticipation d) (hx : BarrierControlAcyclic d)
    (hc : GenericMemoryConditions c initial rf co) : GenericMemoryConditions d initial rf co := by
  refine ⟨?_, hb, hx, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [BaseAcyclic, base h] using hc.baseAcyclic
  · simpa only [ValueAgreement, reads h, sources h initial, eligible h rf] using hc.agreement
  · intro hm
    exact coherent h (hc.coherence (by simpa only [mixed h rf] using hm))
  · intro hm
    exact causal_conditions h (hc.causality (by simpa only [mixed h rf] using hm))
  · intro hm
    simpa only [SingleCopyAtomicity, strong h, reads h, writes h] using
      hc.atomicity (by simpa only [mixed h rf] using hm)
  · intro hm
    simpa only [SCPerLocation, present h, strong h, overlaps h, program_order h, communication h rf co] using
      hc.scPerLocation (by simpa only [mixed h rf] using hm)
  · intro hm
    simpa only [RMWAtomicity,is_rmw h,strong h,reads h,writes h] using
      hc.rmwAtomicity (by simpa only [mixed h rf] using hm)

theorem observer_eligible {c d : Candidate ByteValue Answers} (h : SameEvents c d) (rf : ReadsFrom) :
    ObserverEligible c rf = ObserverEligible d rf := by
  funext loc
  simp only [ObserverEligible, mixed h rf, writes h, races h rf]

theorem observation {c d : Candidate ByteValue Answers} {initial rf co o} (h : SameEvents c d) (hd : d.Complete)
    (ho : ObserverConditions c initial rf co o) : ObserverConditions d initial rf co o where
  complete := hd
  globalOnly := ho.globalOnly
  agreement := by simpa only [observer_eligible h rf, sources h initial] using ho.agreement
  noStale := by simpa only [mixed h rf, writes h] using ho.noStale

end SameEvents
end Ptx.Event
