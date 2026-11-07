import Ptx.Hopper.TmaRetryErasure
import Ptx.Hopper.TmaResourceErasure
import Ptx.Kernels.HopperDoubleBufferRetryResourceView
import Ptx.Tests.HopperCandidateCollective

/-! Source-matched one-tile histories with independent lane retries. Closed
checks use the proved resource-only erasure, never real state/payload equality.
Erased source candidates are not asserted source-produced or memory-admitted.
-/
namespace Ptx.HopperRetryHistoryTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev candidate := HopperCandidateCollectiveTests.candidate
abbrev family := HopperCandidateCollectiveTests.family
def sourceId (serial : Nat) : Ptx.Event.EventId := ⟨(ctx 1 0).id,serial⟩
def copyA : Tma.CopyId := ⟨sourceId 6⟩
def copyB : Tma.CopyId := ⟨sourceId 7⟩
def gate (slot : Stage) : Location := ⟨.shared .zero,barrierAddress slot⟩
def failedEntries : List Tma.Entry :=
  (List.ofFn (fun lane : Wgmma.Lane => lane)).flatMap (fun lane =>
    List.ofFn (fun attempt : Fin (HopperCandidateMemoryTests.schedule lane 0) =>
      (⟨.source ((family 0).failedWaitId 0 lane attempt.val),.tryWaitParity 0 false⟩ : Tma.Entry)))
def successfulEntries : List Tma.Entry := List.ofFn (fun lane : Wgmma.Lane =>
  (⟨.source ((family 0).waitId 0 lane),.tryWaitParity 0 true⟩ : Tma.Entry))
def history0 : List Tma.Entry :=
  [⟨.source (sourceId 0),.init 1⟩,⟨.source (sourceId 5),.arriveExpectTx 2304⟩]++failedEntries++
    [⟨.notification copyA,.completeTx 2048⟩,⟨.notification copyB,.completeTx 256⟩]++successfulEntries++
    [⟨.source (sourceId 21),.inval⟩]
def history1 : List Tma.Entry := [⟨.source (sourceId 1),.init 1⟩,⟨.source (sourceId 22),.inval⟩]
def resourceView (value : ℝ) : Hopper.Candidate := Tma.ResourceErasure.candidate (candidate value).view
def compactCandidate : Hopper.Candidate := ⟨List.ofFn (fun lane : Wgmma.Lane =>
  oneTileResourceTrace lane (HopperCandidateMemoryTests.schedule lane 0))⟩

theorem resource_view_exact (value : ℝ) : resourceView value = compactCandidate := by
  apply congrArg Hopper.Candidate.mk
  simp only [resourceView,Tma.ResourceErasure.candidate,Unified.Candidate.view,HopperCandidateMemoryTests.candidate,
    replyCandidate,List.map_map,List.map_ofFn,Function.comp_def,compactCandidate]
  exact congrArg List.ofFn (funext (fun lane => one_tile_resource_trace lane (HopperCandidateMemoryTests.replies value lane)
    (HopperCandidateMemoryTests.schedule lane) rfl rfl))

theorem resource_view_independent (value : ℝ) : resourceView value = resourceView 0 := by
  exact (resource_view_exact value).trans (resource_view_exact 0).symm

theorem retry_inventory_sizes : failedEntries.length = 127 ∧ successfulEntries.length = 128 ∧ history0.length = 260 := by decide

theorem resource_history_zero_valid : Tma.HistoryValid Tma.localShared (resourceView 0) (gate 0) history0 := by
  rw [resource_view_exact]
  exact ⟨by decide,by decide,by decide,⟨none,by decide⟩⟩
theorem resource_history_one_valid : Tma.HistoryValid Tma.localShared (resourceView 0) (gate 1) history1 := by
  rw [resource_view_exact]
  exact ⟨by decide,by decide,by decide,⟨none,by decide⟩⟩

theorem actual_history_zero_valid (value : ℝ) : Tma.HistoryValid Tma.localShared (candidate value).view (gate 0) history0 := by
  apply Tma.ResourceErasure.history_valid_preserved.mp
  change Tma.HistoryValid Tma.localShared (resourceView value) (gate 0) history0
  rw [resource_view_independent value]
  exact resource_history_zero_valid

theorem actual_history_one_valid (value : ℝ) : Tma.HistoryValid Tma.localShared (candidate value).view (gate 1) history1 := by
  apply Tma.ResourceErasure.history_valid_preserved.mp
  change Tma.HistoryValid Tma.localShared (resourceView value) (gate 1) history1
  rw [resource_view_independent value]
  exact resource_history_one_valid

def histories (loc : Location) : List Tma.Entry := if loc = gate 0 then history0 else if loc = gate 1 then history1 else []
def cluster : Access.ClusterScope := fun left right => left.cta = right.cta

theorem notice_a_at : history0[129]? = some ⟨.notification copyA,.completeTx 2048⟩ := by decide
theorem notice_b_at : history0[130]? = some ⟨.notification copyB,.completeTx 256⟩ := by decide
theorem successful_waits_at : ∀ lane : Wgmma.Lane,
    history0[131+lane.val]? = some ⟨.source ((family 0).waitId 0 lane),.tryWaitParity 0 true⟩ := by decide

theorem erased_a_observations : ∀ lane : Wgmma.Lane,
    Tma.observation (Tma.RetryErasure.erase history0) (Tma.RetryErasure.rank history0 129)
      (Tma.RetryErasure.rank history0 (131+lane.val)) = some (copyA,(family 0).waitId 0 lane) := by decide
theorem erased_b_observations : ∀ lane : Wgmma.Lane,
    Tma.observation (Tma.RetryErasure.erase history0) (Tma.RetryErasure.rank history0 130)
      (Tma.RetryErasure.rank history0 (131+lane.val)) = some (copyB,(family 0).waitId 0 lane) := by decide

end
end Ptx.HopperRetryHistoryTests
