import Ptx.Kernels.HopperStageInputs
import Ptx.Hopper.TmaResourceErasure

/-! An exhaustive actual-source mbarrier history, including the two distinct
implicit TMA notifications and all 128 successful waits before invalidation.
Resource erasure is a proved check optimization, never source/memory admission.
-/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def gate : Location := ⟨.shared .zero,0⟩
def waitId (lane : Wgmma.Lane) : Ptx.Event.EventId := ⟨(ctx lane).id,if leader lane then 7 else 2⟩
def resourceHistory : List Tma.Entry := [
  ⟨.source (copyId 0).issue,.init 1⟩,
  ⟨.source (copyId 4).issue,.arriveExpectTx 2304⟩,
  ⟨.notification (copyId 5),.completeTx 2048⟩,
  ⟨.notification (copyId 6),.completeTx 256⟩]++
  List.ofFn (fun lane : Wgmma.Lane => (⟨.source (waitId lane),.tryWaitParity 0 true⟩ : Tma.Entry))++
  [⟨.source (copyId 18).issue,.inval⟩]
def histories (location : Location) : List Tma.Entry := if location = gate then resourceHistory else []
def resourceCandidate : Hopper.Candidate := Tma.ResourceErasure.candidate (candidate (fun _ => 0) (fun _ => 0)).view

theorem trace_resource_erasure (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    Tma.ResourceErasure.trace (trace a b lane).view =
      Tma.ResourceErasure.trace (trace (fun _ => 0) (fun _ => 0) lane).view := by
  unfold Tma.ResourceErasure.trace
  congr 1
  change ((middleEvents a b lane (leader lane)++(nativeEvents a b lane (leader lane)++
    (storeResult a b lane (leader lane)).2)).map Unified.eventView).map Tma.ResourceErasure.event =
    ((middleEvents (fun _ => 0) (fun _ => 0) lane (leader lane)++
      (nativeEvents (fun _ => 0) (fun _ => 0) lane (leader lane)++
        (storeResult (fun _ => 0) (fun _ => 0) lane (leader lane)).2)).map Unified.eventView).map Tma.ResourceErasure.event
  rw [actual_store_events,actual_store_events]
  cases leader lane <;> rfl
theorem candidate_resource_erasure (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    Tma.ResourceErasure.candidate (candidate a b).view = resourceCandidate := by
  apply congrArg Hopper.Candidate.mk
  simp only [Tma.ResourceErasure.candidate,resourceCandidate,Unified.Candidate.view,candidate,
    List.map_map,List.map_ofFn,Function.comp_def]
  exact congrArg List.ofFn (funext (trace_resource_erasure a b))
theorem history_unique : (resourceHistory.map Tma.Entry.origin).Nodup := by decide
theorem history_source_order : Tma.SourceOrder resourceHistory := by decide
theorem history_protocol : Mbarrier.run none (resourceHistory.map Tma.Entry.operation) = some none := by decide
theorem history_exhaustive : resourceHistory.Perm (Tma.inventory Tma.localShared resourceCandidate gate) := by decide
theorem stage_history_valid (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    Tma.HistoryValid Tma.localShared (candidate a b).view gate resourceHistory := by
  refine ⟨history_unique,?_,history_source_order,⟨none,history_protocol⟩⟩
  rw [← Tma.ResourceErasure.inventory_preserved,candidate_resource_erasure]
  exact history_exhaustive

end
end Ptx.Kernels.HopperStage
