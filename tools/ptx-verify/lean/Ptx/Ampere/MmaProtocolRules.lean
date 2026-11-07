import Ptx.Ampere.MmaProtocol

/-! Derive a returned MMA value from matrices represented by actual matched
source events. Kernel proofs must establish these input representations through
register execution and memory agreement; the interpreter accepts no input-matrix oracle.
-/
namespace Ptx.Ampere
open Ptx.ISA
noncomputable section

def SameMmaGroup (c : Candidate) (event : Ptx.Event.EventId) (call : MmaCall)
    (entry : Ptx.Event.EventId) (other : MmaCall) : Prop :=
  entry.thread.cta = event.thread.cta ∧ other.warp = call.warp ∧ other.ordinal = call.ordinal ∧
  other.pc = call.pc ∧ c.eventAt entry = some (.mmaEntry other)

theorem matched_mma_output {code launch c event call}
    (hm : MmaConditions code launch c) (he : c.eventAt event = some (.mmaReturn call))
    (a : Mma.ACoord → ℝ) (b : Mma.BCoord → ℝ) (acc : Mma.CCoord → ℝ)
    (ha : ∀ entry other, SameMmaGroup c event call entry other → ∀ slot,
      other.inputs.a slot = Mma.packA (Mma.gatherA a) (other.lane,slot))
    (hb : ∀ entry other, SameMmaGroup c event call entry other → ∀ slot,
      other.inputs.b slot = Mma.packB (Mma.gatherB b) (other.lane,slot))
    (hc : ∀ entry other, SameMmaGroup c event call entry other → ∀ slot,
      other.inputs.c slot = Mma.gatherC acc (other.lane,slot)) (slot : Fin 4) :
    call.output slot = Mma.gatherC (Mma.matrixStep a b acc) (call.lane,slot) := by
  obtain ⟨members,_,hself,hvalid,hresult⟩ := hm event call he
  have hgroup (lane : Mma.Lane) : SameMmaGroup c event call (members lane).entry (members lane).call := by
    have hp := hvalid lane
    exact ⟨(congrArg ThreadId.cta hp.1.1).trans hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.1,hp.2.2.2.2.2,hp.1.2.2.1⟩
  have hA : (fun p => (members p.1).call.inputs.a p.2) = Mma.packA (Mma.gatherA a) := by
    funext ⟨lane,reg⟩
    simpa only [(hvalid lane).2.1] using ha _ _ (hgroup lane) reg
  have hB : (fun p => (members p.1).call.inputs.b p.2) = Mma.packB (Mma.gatherB b) := by
    funext ⟨lane,reg⟩
    simpa only [(hvalid lane).2.1] using hb _ _ (hgroup lane) reg
  have hC : (fun p => (members p.1).call.inputs.c p.2) = Mma.gatherC acc := by
    funext ⟨lane,reg⟩
    simpa only [(hvalid lane).2.1] using hc _ _ (hgroup lane) reg
  have hv := hresult call.lane slot
  rw [hself,hA,hB,hC,Mma.packed_results_gather] at hv
  exact hv

end
end Ptx.Ampere
