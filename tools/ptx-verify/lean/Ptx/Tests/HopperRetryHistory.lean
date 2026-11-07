import Ptx.Tests.HopperRetryMetadata
import Ptx.Hopper.UnifiedOrder

/-! Actual completion/publication through retry erasure, retaining exhaustive
source histories; boundary tests distinguish protocol erasure from admission.
-/
namespace Ptx.HopperRetryHistoryTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem wait_id_independent (value : ℝ) (lane : Wgmma.Lane) : (family value).waitId 0 lane = (family 0).waitId 0 lane := by
  change replyWaitId 1 lane (HopperCandidateMemoryTests.replies value lane) (HopperCandidateMemoryTests.schedule lane) 0 =
    replyWaitId 1 lane (HopperCandidateMemoryTests.replies 0 lane) (HopperCandidateMemoryTests.schedule lane) 0
  unfold replyWaitId replyFailedWaitId replyTileStart
  simp only [replyLoopEvents,loopEvents,List.length_nil,Nat.add_zero]
  cases hl : Ptx.Kernels.HopperStage.leader lane <;> simp [replyInitialEvents,initializationEvents,replyInitialCopies,hl]

theorem actual_a_completion_observed (value : ℝ) (lane : Wgmma.Lane) :
    Access.CompletionObserved Tma.localShared (candidate value).view histories cluster copyA ((family value).waitId 0 lane) := by
  have ho := Tma.RetryErasure.observation_from_erased (actual_history_zero_valid value).protocol notice_a_at
    (successful_waits_at lane) (by omega) (erased_a_observations lane)
  refine ⟨rfl,gate 0,129,131+lane.val,rfl,?_,?_⟩
  · simpa only [histories,ite_true] using actual_history_zero_valid value
  · simpa only [histories,ite_true,wait_id_independent value lane] using ho

theorem actual_b_completion_observed (value : ℝ) (lane : Wgmma.Lane) :
    Access.CompletionObserved Tma.localShared (candidate value).view histories cluster copyB ((family value).waitId 0 lane) := by
  have ho := Tma.RetryErasure.observation_from_erased (actual_history_zero_valid value).protocol notice_b_at
    (successful_waits_at lane) (by omega) (erased_b_observations lane)
  refine ⟨rfl,gate 0,130,131+lane.val,rfl,?_,?_⟩
  · simpa only [histories,ite_true] using actual_history_zero_valid value
  · simpa only [histories,ite_true,wait_id_independent value lane] using ho

theorem actual_copy_a (value : ℝ) : Tma.copyAt (candidate value).view copyA =
    some (replyInitialA (HopperCandidateMemoryTests.replies value 0)) := by
  apply Tma.copyAt_iff.mpr
  apply Unified.view_tma_iff.mpr
  change (replyCandidate 1 (HopperCandidateMemoryTests.replies value) HopperCandidateMemoryTests.schedule).eventAt
    ⟨(replyTrace 1 (HopperCandidateMemoryTests.replies value) HopperCandidateMemoryTests.schedule 0).id,6⟩ = _
  rw [Unified.eventAt_of_member (reply_source_ids_unique 1 (HopperCandidateMemoryTests.replies value) HopperCandidateMemoryTests.schedule)
    (List.mem_ofFn.mpr ⟨(0 : Wgmma.Lane),rfl⟩)]
  rfl

theorem actual_copy_b (value : ℝ) : Tma.copyAt (candidate value).view copyB =
    some (replyInitialB (HopperCandidateMemoryTests.replies value 0)) := by
  apply Tma.copyAt_iff.mpr
  apply Unified.view_tma_iff.mpr
  change (replyCandidate 1 (HopperCandidateMemoryTests.replies value) HopperCandidateMemoryTests.schedule).eventAt
    ⟨(replyTrace 1 (HopperCandidateMemoryTests.replies value) HopperCandidateMemoryTests.schedule 0).id,7⟩ = _
  rw [Unified.eventAt_of_member (reply_source_ids_unique 1 (HopperCandidateMemoryTests.replies value) HopperCandidateMemoryTests.schedule)
    (List.mem_ofFn.mpr ⟨(0 : Wgmma.Lane),rfl⟩)]
  rfl

theorem actual_a_native_publication (value : ℝ) (p : Wgmma.ACoord) (part : Fin 2) :
    Unified.TmaReady Tma.localShared (candidate value) histories cluster copyA (Wgmma.aOffset (p,part)).val
      ((family value).mmaId 0 0) (.a p part) (Wgmma.operandLocation .zero ((family value).calls 0 0) (.a p part)) := by
  apply family_tma_ready_from_observation (family value)
    (HopperCandidateMemoryTests.heterogeneous_source_well_formed value (fun _ => .bits (byte 0))) 0 (by decide)
  · have hl : Wgmma.operandLocation .zero ((family value).calls 0 0) (.a p part) =
        ⟨.shared .zero,16+(Wgmma.aOffset (p,part)).val⟩ := by
      simp only [Wgmma.operandLocation,ReplySourceFamily.calls,reply_call_a,a_operand_address]
      rfl
    rw [hl]
    simp only [Tma.writeLocation,actual_copy_a,Option.bind_some]
    exact ite_eq_left (Wgmma.aOffset (p,part)).isLt
  · rfl
  · exact actual_a_completion_observed value

theorem actual_b_native_publication (value : ℝ) (p : Wgmma.BCoord) (part : Fin 2) :
    Unified.TmaReady Tma.localShared (candidate value) histories cluster copyB (Wgmma.bOffset (p,part)).val
      ((family value).mmaId 0 0) (.b p part) (Wgmma.operandLocation .zero ((family value).calls 0 0) (.b p part)) := by
  apply family_tma_ready_from_observation (family value)
    (HopperCandidateMemoryTests.heterogeneous_source_well_formed value (fun _ => .bits (byte 0))) 0 (by decide)
  · have hl : Wgmma.operandLocation .zero ((family value).calls 0 0) (.b p part) =
        ⟨.shared .zero,2064+(Wgmma.bOffset (p,part)).val⟩ := by
      simp only [Wgmma.operandLocation,ReplySourceFamily.calls,reply_call_b,b_operand_address]
      rfl
    rw [hl]
    simp only [Tma.writeLocation,actual_copy_b,Option.bind_some]
    exact ite_eq_left (Wgmma.bOffset (p,part)).isLt
  · rfl
  · exact actual_b_completion_observed value

def nativeProducer : Wgmma.OperandByte → Unified.Node
  | .a p part => .base (.tma (.write copyA (Wgmma.aOffset (p,part)).val))
  | .b p part => .base (.tma (.write copyB (Wgmma.bOffset (p,part)).val))

theorem actual_native_byte_order (value : ℝ) (operand : Wgmma.OperandByte) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor (candidate value) histories cluster
      (Wgmma.operandLocation .zero ((family value).calls 0 0) operand)
      (nativeProducer operand) (.wgmmaRead ((family value).mmaId 0 0) operand) := by
  apply Unified.native_published_byte_order
  cases operand with
  | a p part => exact actual_a_native_publication value p part
  | b p part => exact actual_b_native_publication value p part

theorem erased_protocol_admitted : Mbarrier.Admitted ((Tma.RetryErasure.erase history0).map Tma.Entry.operation) := by
  rw [Tma.RetryErasure.erased_operations]
  exact Mbarrier.Retries.admitted_erase (actual_history_zero_valid 0).protocol

def failedId : Ptx.Event.EventId := (family 0).failedWaitId 0 1 0
theorem erased_history_not_exhaustive (value : ℝ) :
    ¬Tma.HistoryValid Tma.localShared (candidate value).view (gate 0) (Tma.RetryErasure.erase history0) := by
  intro hv
  have hs : Tma.resourceAt Tma.localShared (candidate value).view (.source failedId) =
      some ⟨gate 0,.tryWaitParity 0 false⟩ := by
    apply Hopper.barrierAt_iff.mpr
    apply Unified.view_barrier_iff.mpr
    exact family_failed_wait_at (family value) (HopperCandidateMemoryTests.heterogeneous_source_well_formed value (fun _ => .bits (byte 0)))
      0 (by decide) 1 0 (by change 0 < 1; decide)
  have hm := Tma.history_complete hv hs
  have hk := (List.mem_filter.mp hm).2
  cases hk

theorem preinit_erasure_converse_rejected :
    Mbarrier.run none [.tryWaitParity 0 false,.init 1] = none ∧
      Mbarrier.run none (Mbarrier.Retries.erase [.tryWaitParity 0 false,.init 1]) = some (some (Mbarrier.initialized 1)) := by decide

theorem post_invalidation_erasure_converse_rejected :
    Mbarrier.run none [.init 1,.inval,.tryWaitParity 0 false] = none ∧
      Mbarrier.run none (Mbarrier.Retries.erase [.init 1,.inval,.tryWaitParity 0 false]) = some none := by decide

theorem completed_object_false_waits_stutter (parities : List Nat) :
    Mbarrier.run (some ⟨1,1,1,0,false⟩) (parities.map (fun p => .tryWaitParity p false)) = some (some ⟨1,1,1,0,false⟩) :=
  Mbarrier.Retries.run_failed_waits _ parities

end
end Ptx.HopperRetryHistoryTests
