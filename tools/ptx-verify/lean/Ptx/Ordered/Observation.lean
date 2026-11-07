import Ptx.Ordered.Witnesses
import Ptx.Scalar.IntegerMemory

/-! Synchronized global observation for ordered candidates. Eligibility uses
the scoped ordered race rules, rather than the old weak candidate predicates.
API completion ordering is an explicit model condition, not a runtime proof. -/
namespace Ptx.Ordered
open Ptx.ISA Ptx.Event
noncomputable section

def ObserverEligible (candidate : Candidate) (rf : ReadsFrom) (loc : Location) : Prop :=
  ¬MixedSizeRace candidate rf ∧
    ¬∃ a b, (candidate.view.writeByte a loc).isSome = true ∧ (candidate.view.writeByte b loc).isSome = true ∧
      DataRace candidate rf a b

structure ObserverConditions (candidate : Candidate) (initial : Scalar.ByteMap) (rf : ReadsFrom)
    (co : Coherence) (observation : Scalar.Observation) : Prop where
  complete : Complete candidate
  globalOnly : ∀ loc ∈ observation.domain, loc.space = .global
  agreement : ∀ loc ∈ observation.domain, ObserverEligible candidate rf loc →
    sourceByte candidate.view initial loc (observation.source loc) = some (observation.output loc)
  noStale : ∀ loc ∈ observation.domain, ¬MixedSizeRace candidate rf → ∀ writer value,
    candidate.view.writeByte writer loc = some value → ¬co loc (observation.source loc) (.write writer)

theorem unique_byte_observer_eligible {candidate rf loc} (hn : ¬MixedSizeRace candidate rf)
    (hu : ∀ a b va vb, candidate.view.writeByte a loc = some va → candidate.view.writeByte b loc = some vb → a = b) :
    ObserverEligible candidate rf loc := by
  refine ⟨hn,?_⟩
  rintro ⟨a,b,ha,hb,hr⟩
  obtain ⟨va,hva⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨vb,hvb⟩ := Option.isSome_iff_exists.mp hb
  have he := hu a b va vb hva hvb
  subst b
  exact hr.notStrong ⟨Or.inl rfl,(Ptx.Event.write_self_strong hva).2⟩

theorem observer_unique_writer {candidate initial rf co observation loc writer value}
    (hm : MemoryConditions candidate initial rf co) (ho : ObserverConditions candidate initial rf co observation)
    (hd : loc ∈ observation.domain) (he : ObserverEligible candidate rf loc)
    (hw : candidate.view.writeByte writer loc = some value)
    (hu : ∀ other v, candidate.view.writeByte other loc = some v → other = writer) : observation.output loc = value := by
  have hv := ho.agreement loc hd he
  cases hs : observation.source loc with
  | initial =>
    exact False.elim (ho.noStale loc hd he.1 writer value hw
      (by simpa only [hs] using (hm.coherence he.1).initialization loc writer value hw))
  | write other =>
    have hwrite : candidate.view.writeByte other loc = some (observation.output loc) := by simpa [hs,sourceByte] using hv
    have hi := hu other (observation.output loc) hwrite
    subst other
    exact Option.some.inj (hwrite.symm.trans hw)

theorem observer_unwritten {candidate initial rf co observation loc}
    (ho : ObserverConditions candidate initial rf co observation) (hd : loc ∈ observation.domain)
    (he : ObserverEligible candidate rf loc) (hn : ∀ writer, candidate.view.writeByte writer loc = none) :
    observation.output loc = initial loc := by
  have hv := ho.agreement loc hd he
  cases hs : observation.source loc with
  | initial => exact (Option.some.inj (by simpa [hs,sourceByte] using hv)).symm
  | write writer => simp [hs,sourceByte,hn] at hv

theorem observe_u32_write {candidate initial rf co observation writer base value}
    (hm : MemoryConditions candidate initial rf co) (ho : ObserverConditions candidate initial rf co observation)
    (hw : candidate.view.eventAt writer = some (.write base (Scalar.u32Bytes value)))
    (hd : ∀ offset, offset < 4 → base.add offset ∈ observation.domain)
    (he : ∀ offset, offset < 4 → ObserverEligible candidate rf (base.add offset))
    (hu : ∀ offset, offset < 4 → ∀ other v, candidate.view.writeByte other (base.add offset) = some v → other = writer) :
    Scalar.RepresentsU32 observation.output base value := by
  intro offset hb
  apply observer_unique_writer hm ho (hd offset hb) (he offset hb) (writer := writer)
  · simpa only [Ptx.Event.Candidate.writeByte,hw,Option.bind_some,Ptx.Event.Kind.writeByte]
      using Scalar.u32_payload_byte base value offset hb
  · exact hu offset hb

theorem unique_writers_observation {candidate initial rf domain} (hc : Complete candidate)
    (hg : ∀ loc ∈ domain, loc.space = .global)
    (hu : ∀ loc a b va vb, candidate.view.writeByte a loc = some va → candidate.view.writeByte b loc = some vb → a = b) :
    ObserverConditions candidate initial rf (InitialCo candidate.view)
      (selectedObservation candidate.view initial (writerSelector candidate.view) domain) := by
  refine ⟨hc,hg,?_,?_⟩
  · intro loc _ _
    cases hs : writerSelector candidate.view loc with
    | none => simp [selectedObservation,sourceByte,hs]
    | some writer => cases hw : candidate.view.writeByte writer loc <;> simp [selectedObservation,sourceByte,hs,hw]
  · intro loc _ _ writer value hw hco
    have hs := writer_selector_covers hu hw
    have he : (selectedObservation candidate.view initial (writerSelector candidate.view) domain).source loc = .write writer := by
      simp [selectedObservation,hs,hw]
    have hi := hco.1
    rw [he] at hi
    cases hi

def Triple (code : List Instr) (pre : Scalar.Launch → Prop) (domain : Scalar.Launch → List Location)
    (post : Scalar.Launch → Scalar.ByteMap → Prop) : Prop :=
  ∀ launch candidate rf co observation, pre launch → WellFormed code launch candidate → Complete candidate →
    MemoryConditions candidate launch.initial rf co → ObserverConditions candidate launch.initial rf co observation →
    observation.domain = domain launch → post launch observation.output

def Nonvacuous (code : List Instr) (pre : Scalar.Launch → Prop) (domain : Scalar.Launch → List Location) : Prop :=
  ∀ launch, pre launch → ∃ candidate rf co observation, WellFormed code launch candidate ∧ Complete candidate ∧
    MemoryConditions candidate launch.initial rf co ∧ ObserverConditions candidate launch.initial rf co observation ∧
    observation.domain = domain launch

end
end Ptx.Ordered
