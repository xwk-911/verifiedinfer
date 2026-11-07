import Ptx.Scalar.Origins

/-! Source-aware admission for mixed scalar programs. The shared graph and
observer rules are unchanged. Actual scalar execution supplies source PCs and
float-bank provenance; physical allocation and full ISA UB remain separate. -/
namespace Ptx.Scalar
open Ptx.ISA
noncomputable section

structure CheckedConditions (code : List Instr) (launch : Launch) (c : Candidate)
    (rf : Event.ReadsFrom) (co : Event.Coherence) : Prop where
  provenance : WellFormed code launch c
  barrierSources : SourceAligned code launch c
  memory : Event.GenericMemoryConditions c launch.initial rf co

def CheckedTriple (code : List Instr) (pre : Launch → Prop) (domain : Launch → List Location)
    (post : Launch → ByteMap → Prop) : Prop :=
  ∀ launch c rf co o, pre launch → CheckedConditions code launch c rf co →
    Event.ObserverConditions c launch.initial rf co o → o.domain = domain launch → post launch o.output

def CheckedNonvacuous (code : List Instr) (pre : Launch → Prop) (domain : Launch → List Location) : Prop :=
  ∀ launch, pre launch → ∃ c rf co o, CheckedConditions code launch c rf co ∧
    Event.ObserverConditions c launch.initial rf co o ∧ o.domain = domain launch

theorem triple_checked {code pre domain post} (hc : Triple code pre domain post) :
    CheckedTriple code pre domain post := by
  intro launch c rf co o hp hm ho hd
  exact hc launch c rf co o hp hm.provenance hm.memory ho hd

theorem checked_apply {code pre domain post launch c rf co o}
    (hc : CheckedTriple code pre domain post) (hp : pre launch)
    (hm : CheckedConditions code launch c rf co) (ho : Event.ObserverConditions c launch.initial rf co o)
    (hd : o.domain = domain launch) : post launch o.output := hc launch c rf co o hp hm ho hd

theorem checked_of_unique_sites {code launch c rf co}
    (hw : WellFormed code launch c) (hu : Scalar.uniqueBarrierSites code = true)
    (hm : Event.GenericMemoryConditions c launch.initial rf co) : CheckedConditions code launch c rf co :=
  ⟨hw,aligned_of_unique_sites hw hu,hm⟩

theorem nonvacuous_checked_of_unique_sites {code pre domain}
    (hu : Scalar.uniqueBarrierSites code = true) (hn : Nonvacuous code pre domain) :
    CheckedNonvacuous code pre domain := by
  intro launch hp
  obtain ⟨c,rf,co,o,hw,hm,ho,hd⟩ := hn launch hp
  exact ⟨c,rf,co,o,checked_of_unique_sites hw hu hm,ho,hd⟩

end
end Ptx.Scalar
