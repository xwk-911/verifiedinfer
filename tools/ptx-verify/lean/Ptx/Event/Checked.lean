import Ptx.Event.Origins
import Ptx.Event.Contracts

/-! Source-aware admission for the supported integer fragment. The graph-only
API remains a regression baseline. This interface additionally checks actual
source barrier PCs; it does not claim physical allocation or full SIMT/ISA UB
freedom. Existing universal graph contracts imply checked contracts. Checked
nonvacuity separately requires a source-aligned complete witness. -/
namespace Ptx.Event
open Ptx.ISA

structure CheckedConditions (code : List Instr) (launch : Launch) (c : Candidate)
    (rf : ReadsFrom) (co : Coherence) : Prop where
  provenance : c.WellFormed code launch
  barrierSources : c.SourceAligned code launch.params
  memory : GenericMemoryConditions c launch.initial rf co

def CheckedTriple (code : List Instr) (pre : Launch → Prop) (domain : Launch → List Location)
    (post : Launch → ByteMap → Prop) : Prop :=
  ∀ launch c rf co o, pre launch → CheckedConditions code launch c rf co →
    ObserverConditions c launch.initial rf co o → o.domain = domain launch → post launch o.output

def CheckedNonvacuous (code : List Instr) (pre : Launch → Prop) (domain : Launch → List Location) : Prop :=
  ∀ launch, pre launch → ∃ c rf co o, CheckedConditions code launch c rf co ∧
    ObserverConditions c launch.initial rf co o ∧ o.domain = domain launch

theorem triple_checked {code pre domain post} (hc : Triple code pre domain post) :
    CheckedTriple code pre domain post := by
  intro launch c rf co o hp hm ho hd
  exact hc launch c rf co o hp hm.provenance hm.memory ho hd

theorem checked_apply {code pre domain post launch c rf co o}
    (hc : CheckedTriple code pre domain post) (hp : pre launch)
    (hm : CheckedConditions code launch c rf co) (ho : ObserverConditions c launch.initial rf co o)
    (hd : o.domain = domain launch) : post launch o.output := hc launch c rf co o hp hm ho hd

theorem checked_of_unique_sites {code launch c rf co}
    (hw : c.WellFormed code launch) (hu : uniqueBarrierSites code = true)
    (hm : GenericMemoryConditions c launch.initial rf co) : CheckedConditions code launch c rf co :=
  ⟨hw,aligned_of_unique_sites hw hu,hm⟩

theorem nonvacuous_checked_of_unique_sites {code pre domain}
    (hu : uniqueBarrierSites code = true) (hn : Nonvacuous code pre domain) :
    CheckedNonvacuous code pre domain := by
  intro launch hp
  obtain ⟨c,rf,co,o,hw,hm,ho,hd⟩ := hn launch hp
  exact ⟨c,rf,co,o,checked_of_unique_sites hw hu hm,ho,hd⟩

end Ptx.Event
