import Ptx.Kernels.AtomicDispatchWitness
import Ptx.Tests.AtomicDispatchOutput

/-! Both CTA orders have complete consistent actual-source executions and
permitted output/frame observations. These are Lean/model witnesses, not GPU runs.
-/
namespace Ptx.AtomicDispatchWitnessTests
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.AtomicDispatchTrace Ptx.AtomicDispatchEvent
open Ptx.AtomicDispatchTests Ptx.AtomicDispatchOutputTests
noncomputable section

theorem domain_global : ∀ loc ∈ domain, loc.space = .global := by
  intro loc hm
  obtain ⟨address,_,rfl⟩ := List.mem_map.mp hm
  rfl

theorem contract_nonvacuous : Scalar.Nonvacuous code (Pre cfg) (fun _ => domain) :=
  nonvacuous cfg domain domain_global

theorem both_orders_legal (reverse : Bool) : ∃ rf co o,
    Scalar.WellFormed code launch (canonical cfg (witnessValues reverse)) ∧
    (canonical cfg (witnessValues reverse)).Complete ∧
    GenericMemoryConditions (canonical cfg (witnessValues reverse)) initial rf co ∧
    ObserverConditions (canonical cfg (witnessValues reverse)) initial rf co o ∧ o.domain = domain := by
  obtain ⟨rf,co,o,hw,hm,ho,hdom⟩ := canonical_allowed cfg reverse pre domain domain_global
  exact ⟨rf,co,o,hw,ho.complete,hm,ho,hdom⟩

theorem both_orders_observe_outputs_and_frame (reverse : Bool) : ∃ rf co o,
    Scalar.WellFormed code launch (canonical cfg (witnessValues reverse)) ∧
    (canonical cfg (witnessValues reverse)).Complete ∧
    GenericMemoryConditions (canonical cfg (witnessValues reverse)) initial rf co ∧
    ObserverConditions (canonical cfg (witnessValues reverse)) initial rf co o ∧ o.domain = domain ∧
    Post cfg initial o.output domain ∧
    o.output ⟨.global,0⟩ = .bits (byte 2) ∧ o.output ⟨.global,64⟩ = .bits (byte 1) ∧
    o.output ⟨.global,128⟩ = .bits (byte 2) ∧ o.output ⟨.global,250⟩ = .bits (byte 165) := by
  obtain ⟨rf,co,o,hw,hd,hm,ho,hdom⟩ := both_orders_legal reverse
  have hwords := observed_words hw hm ho hdom
  exact ⟨rf,co,o,hw,hd,hm,ho,hdom,Scalar.triple_apply contract pre hw hm ho hdom,
    hwords.1,hwords.2.1,hwords.2.2,observed_frame hw hm ho hdom⟩

end
end Ptx.AtomicDispatchWitnessTests
