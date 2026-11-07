import Ptx.Kernels.ScalarSourceChecked
import Ptx.Tests.ScalarMatmulMemory
import Ptx.Tests.ScalarAttentionMemory
import Ptx.Tests.AtomicDispatchWitness
import Ptx.Tests.FloatMemory

/-! Source-aware complete witnesses for the existing generated scalar kernels.
These preserve their original outputs/frames and do not add an alignment premise
to inputs. They remain current-model proofs, not new GPU or IEEE experiments. -/
namespace Ptx.ScalarSourceCheckedTests
open Ptx.ISA Ptx.Event
noncomputable section

open Ptx.ScalarMatmulMemoryTests Ptx.ScalarMatmul in
theorem matmul_instance : ∃ c rf co o,
    Scalar.CheckedConditions code launch c rf co ∧ ObserverConditions c initial rf co o ∧ o.domain = domain ∧
    Scalar.readReal .f32 o.output (ScalarMatmulEvent.cLoc cfg 0 0) = some 12 ∧
    o.output ⟨.global,250⟩ = .bits (byte 165) := by
  obtain ⟨c,rf,co,o,hc,ho,hd⟩ := ScalarMatmulEvent.checked_nonvacuous cfg a b domain domain_global launch pre
  exact ⟨c,rf,co,o,hc,ho,hd,observed_cell hc.provenance hc.memory ho hd,observed_frame hc.provenance ho hd⟩

open Ptx.ScalarAttentionMemoryTests Ptx.ScalarAttention in
theorem attention_instance : ∃ c rf co o,
    Scalar.CheckedConditions code launch c rf co ∧ ObserverConditions c initial rf co o ∧ o.domain = domain ∧
    Scalar.readReal .f32 o.output (ScalarAttentionEvent.outputLoc cfg 0 0) = some 7 ∧
    o.output ⟨.global,500⟩ = .bits (byte 165) := by
  obtain ⟨c,rf,co,o,hc,ho,hd⟩ := ScalarAttentionEvent.checked_nonvacuous cfg q key value 1 domain domain_global launch pre
  exact ⟨c,rf,co,o,hc,ho,hd,observed_cell hc.provenance hc.memory ho hd,observed_frame hc.provenance ho hd⟩

open Ptx.ScalarAttentionMemoryTests Ptx.ScalarAttention in
theorem empty_attention_instance : ∃ c rf co o,
    Scalar.CheckedConditions code zeroLaunch c rf co ∧ ObserverConditions c initial rf co o ∧ o.domain = domain ∧
    Scalar.readReal .f32 o.output (ScalarAttentionEvent.outputLoc zeroCfg 0 0) = some 0 := by
  obtain ⟨c,rf,co,o,hc,ho,hd⟩ := ScalarAttentionEvent.checked_nonvacuous zeroCfg q key value 1 domain domain_global zeroLaunch zero_pre
  refine ⟨c,rf,co,o,hc,ho,hd,?_⟩
  have hs := Scalar.checked_apply (ScalarAttentionEvent.checked_correct zeroCfg q key value 1 domain zero_covers) zero_pre hc ho hd
  exact Scalar.represents_read (hs.1 0 0 (by decide) (by decide))

open Ptx.AtomicDispatchTrace Ptx.AtomicDispatchEvent Ptx.AtomicDispatchTests Ptx.AtomicDispatchOutputTests in
theorem atomic_both_orders (reverse : Bool) : ∃ rf co o,
    Scalar.CheckedConditions code launch (canonical cfg (witnessValues reverse)) rf co ∧
    ObserverConditions (canonical cfg (witnessValues reverse)) initial rf co o ∧ o.domain = domain ∧
    o.output ⟨.global,0⟩ = .bits (byte 2) ∧ o.output ⟨.global,64⟩ = .bits (byte 1) ∧
    o.output ⟨.global,128⟩ = .bits (byte 2) ∧ o.output ⟨.global,250⟩ = .bits (byte 165) := by
  obtain ⟨rf,co,o,hw,_,hm,ho,hd,_,hcounter,hx,hy,hframe⟩ :=
    AtomicDispatchWitnessTests.both_orders_observe_outputs_and_frame reverse
  exact ⟨rf,co,o,Scalar.checked_of_unique_sites hw checked_sites hm,ho,hd,hcounter,hx,hy,hframe⟩

theorem literal_instance : ∃ c rf co o,
    Scalar.CheckedConditions FloatLiteralsTrace.code (FloatLiteralsMemory.launch 64 FloatMemoryTests.initial) c rf co ∧
    ObserverConditions c FloatMemoryTests.initial rf co o ∧ o.domain = FloatLiteralsMemory.domain 64 ∧
    FloatLiteralsMemory.observedValue 64 o.output = some 9 := by
  have hp : FloatLiteralsUniversal.Pre 64 (FloatLiteralsMemory.launch 64 FloatMemoryTests.initial) := ⟨by decide,rfl,rfl⟩
  obtain ⟨c,rf,co,o,hc,ho,hd⟩ := FloatLiteralsUniversal.checked_nonvacuous 64 _ hp
  exact ⟨c,rf,co,o,hc,ho,hd,Scalar.checked_apply (FloatLiteralsUniversal.checked_correct 64) hp hc ho hd⟩

end
end Ptx.ScalarSourceCheckedTests
