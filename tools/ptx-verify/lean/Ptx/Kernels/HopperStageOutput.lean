import Ptx.Kernels.HopperStageAddressValues

/-! Actual four-store source suffix. These are emitted write events, not a
global observer/correctness theorem for arbitrary admitted executions. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def storedEvents (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) : List Wgmma.Event := [
  .base (.ampere (.ordinary (.write ⟨.global,wrap 64 (outFinal lane+0)⟩ (Symbolic.encode .f32 ((stageCall a b lane isLeader).output 0))))),
  .base (.ampere (.ordinary (.write ⟨.global,wrap 64 (outFinal lane+4)⟩ (Symbolic.encode .f32 ((stageCall a b lane isLeader).output 1))))),
  .base (.ampere (.ordinary (.write ⟨.global,wrap 64 (outFinal lane+256)⟩ (Symbolic.encode .f32 ((stageCall a b lane isLeader).output 2))))),
  .base (.ampere (.ordinary (.write ⟨.global,wrap 64 (outFinal lane+260)⟩ (Symbolic.encode .f32 ((stageCall a b lane isLeader).output 3))))),
  .base (.ampere (.ordinary (.barrierArrival 1 0))),
  .base (.ampere (.ordinary (.barrierReturn 1 0)))]++
  (if isLeader then [.base (.barrier ⟨⟨.shared .zero,0⟩,.inval⟩)] else [])
theorem actual_store_events (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) :
    (storeResult a b lane isLeader).2 = storedEvents a b lane isLeader := by cases isLeader <;> rfl

theorem actual_store_at (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) (slot : Wgmma.Slot) :
    (storeResult a b lane isLeader).2[slot.val]? = some (.base (.ampere (.ordinary
      (.write ⟨.global,wrap 64 (outFinal lane+storeOffset slot)⟩
        (Symbolic.encode .f32 ((stageCall a b lane isLeader).output slot)))))) := by
  rw [actual_store_events]
  rcases slot with ⟨s,hs⟩
  have hv : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by omega
  rcases hv with rfl | rfl | rfl | rfl <;> cases isLeader <;> simp [storedEvents,storeOffset]
theorem call_output_value (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (slot : Wgmma.Slot) :
    (calls a b lane).output slot = Wgmma.matrixStep a b (fun _ => 0) (Wgmma.cCoord (lane,slot)) := by
  have h := congrFun (tensor_result a b) (Wgmma.cCoord (lane,slot))
  simpa only [Wgmma.scatterC,Wgmma.c_owner_coord] using h
theorem actual_matrix_store (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (slot : Wgmma.Slot) :
    (storeResult a b lane (leader lane)).2[slot.val]? = some (.base (.ampere (.ordinary
      (.write ⟨.global,8192+4*(8*(Wgmma.cCoord (lane,slot)).1.val+(Wgmma.cCoord (lane,slot)).2.val)⟩
        (Symbolic.encode .f32 (Wgmma.matrixStep a b (fun _ => 0) (Wgmma.cCoord (lane,slot)))))))) := by
  rw [actual_store_at,actual_output_address]
  change some (Wgmma.Event.base (.ampere (.ordinary (.write _ (Symbolic.encode .f32 ((calls a b lane).output slot)))))) = _
  rw [call_output_value]

def storeId (lane : Wgmma.Lane) (slot : Wgmma.Slot) : Ptx.Event.EventId :=
  ⟨(ctx lane).id,middleLength (leader lane)+3+slot.val⟩
theorem actual_candidate_store (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (slot : Wgmma.Slot) :
    (candidate a b).eventAt (storeId lane slot) = some (.base (.ampere (.ordinary
      (.write ⟨.global,8192+4*(8*(Wgmma.cCoord (lane,slot)).1.val+(Wgmma.cCoord (lane,slot)).2.val)⟩
        (Symbolic.encode .f32 (Wgmma.matrixStep a b (fun _ => 0) (Wgmma.cCoord (lane,slot)))))))) := by
  change (candidate a b).eventAt ⟨(trace a b lane).id,middleLength (leader lane)+3+slot.val⟩ = _
  rw [Unified.eventAt_of_member (trace_ids_unique a b) (List.mem_ofFn.mpr ⟨lane,rfl⟩)]
  change (middleEvents a b lane (leader lane)++(nativeEvents a b lane (leader lane)++
    (storeResult a b lane (leader lane)).2))[middleLength (leader lane)+3+slot.val]? = _
  rw [List.getElem?_append_right (by rw [middle_length]; omega),middle_length]
  have hi : middleLength (leader lane)+3+slot.val-middleLength (leader lane) = 3+slot.val := by omega
  rw [hi,List.getElem?_append_right (by change 3 ≤ 3+slot.val; omega)]
  change (storeResult a b lane (leader lane)).2[3+slot.val-3]? = _
  rw [Nat.add_sub_cancel_left]
  exact actual_matrix_store a b lane slot

end
end Ptx.Kernels.HopperStage
