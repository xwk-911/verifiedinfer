import Ptx.Event.Observation

/-! Independent contracts over arbitrary complete, provenance-checked candidates
and synchronized observations. The memory-model trust boundary is explicit.
Neither a contract nor a witness alone implies ISA UB freedom or termination.
-/
namespace Ptx.Event
open Ptx.ISA

def Triple (code : List Instr) (pre : Launch → Prop) (domain : Launch → List Location)
    (post : Launch → ByteMap → Prop) : Prop :=
  ∀ launch c rf co o, pre launch → c.WellFormed code launch →
    GenericMemoryConditions c launch.initial rf co →
    ObserverConditions c launch.initial rf co o → o.domain = domain launch → post launch o.output

def Nonvacuous (code : List Instr) (pre : Launch → Prop) (domain : Launch → List Location) : Prop :=
  ∀ launch, pre launch → ∃ c rf co o, c.WellFormed code launch ∧
    GenericMemoryConditions c launch.initial rf co ∧
    ObserverConditions c launch.initial rf co o ∧ o.domain = domain launch

theorem triple_apply {code pre domain post launch c rf co o}
    (hc : Triple code pre domain post) (hp : pre launch) (hw : c.WellFormed code launch)
    (hm : GenericMemoryConditions c launch.initial rf co)
    (ho : ObserverConditions c launch.initial rf co o) (hd : o.domain = domain launch) :
    post launch o.output := hc launch c rf co o hp hw hm ho hd

end Ptx.Event
