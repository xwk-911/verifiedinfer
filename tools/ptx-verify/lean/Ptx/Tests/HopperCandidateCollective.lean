import Ptx.Kernels.HopperDoubleBufferCandidateCollective
import Ptx.Tests.HopperCandidateMemory
import Ptx.Tests.HopperKernelReconstruction

/-! Actual heterogeneous-retry source collectives, arbitrary captured matrix
values, failed-wait rejection and a complete two-tile producer with retries.
Source collective structure is distinct from resource/tensor/ISA admission. -/
namespace Ptx.HopperCandidateCollectiveTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev candidate := HopperCandidateMemoryTests.candidate
abbrev replies := HopperCandidateMemoryTests.replies
abbrev schedule := HopperCandidateMemoryTests.schedule
def family (value : ℝ) : ReplySourceFamily 1 (candidate value) := {
  replies := replies value
  schedules := schedule
  traces := replyTrace 1 (replies value) schedule
  members := fun lane => List.mem_ofFn.mpr ⟨lane,rfl⟩
  ids := fun _ => rfl
  oracles := fun _ => rfl
  events := fun _ => rfl
}

theorem actual_event_indices (value : ℝ) :
    ((family value).waitId 0 0).serial = 8 ∧ ((family value).waitId 0 1).serial = 3 ∧ ((family value).waitId 0 2).serial = 4 ∧
      ((family value).mmaId 0 0).serial = 10 ∧ ((family value).mmaId 0 1).serial = 5 ∧ ((family value).mmaId 0 2).serial = 6 := by
  change 8 = 8 ∧ 3 = 3 ∧ 4 = 4 ∧ 10 = 10 ∧ 5 = 5 ∧ 6 = 6
  decide

theorem actual_successful_wait (value : ℝ) (lane : Wgmma.Lane) :
    (candidate value).eventAt ((family value).waitId 0 lane) =
      some (waitEvent (ctx 1 lane) (barrierAddress (stage 0)) (expectedParity 0) true) :=
  family_wait_at (family value) (HopperCandidateMemoryTests.heterogeneous_source_well_formed value (fun _ => .bits (byte 0))) 0 (by decide) lane

theorem actual_failed_wait (value : ℝ) (attempt : Nat) (ha : attempt < 2) :
    (candidate value).eventAt ((family value).failedWaitId 0 2 attempt) =
      some (waitEvent (ctx 1 2) (barrierAddress (stage 0)) (expectedParity 0) false) :=
  family_failed_wait_at (family value) (HopperCandidateMemoryTests.heterogeneous_source_well_formed value (fun _ => .bits (byte 0))) 0 (by decide) 2 attempt ha

theorem actual_mma (value : ℝ) (lane : Wgmma.Lane) :
    (candidate value).eventAt ((family value).mmaId 0 lane) =
      some (.mma ((family value).marks 0 lane) ((family value).calls 0 lane)) :=
  family_mma_at (family value) (HopperCandidateMemoryTests.heterogeneous_source_well_formed value (fun _ => .bits (byte 0))) 0 (by decide) lane

theorem captured_output_remains_arbitrary (value : ℝ) (lane : Wgmma.Lane) (slot : Wgmma.Slot) :
    ((family value).calls 0 lane).output slot = value := rfl

theorem same_mark_despite_different_indices (value : ℝ) :
    ((family value).mmaId 0 0).serial ≠ ((family value).mmaId 0 1).serial ∧
      (family value).marks 0 0 = (family value).marks 0 1 := by
  constructor
  · change 10 ≠ 5; decide
  · change replyMark 1 0 (replies value 0) (schedule 0) 0 = replyMark 1 1 (replies value 1) (schedule 1) 0
    rw [reply_mark_value,reply_mark_value]

theorem heterogeneous_source_collective (value : ℝ) :
    Nonempty (Unified.Collective (candidate value) ((family value).mmaId 0 0)) :=
  ⟨familyCollective (family value) (HopperCandidateMemoryTests.heterogeneous_source_well_formed value (fun _ => .bits (byte 0))) 0 (by decide)⟩

theorem all_128_lanes_have_actual_calls (value : ℝ) (lane : Wgmma.Lane) :
    ∃ event mark call, (candidate value).eventAt event = some (.mma mark call) ∧ call.lane = lane :=
  Unified.collective_all_lanes_present
    (familyCollective (family value) (HopperCandidateMemoryTests.heterogeneous_source_well_formed value (fun _ => .bits (byte 0))) 0 (by decide)) lane

theorem actual_successful_wait_precedes_mma (value : ℝ) (lane : Wgmma.Lane) :
    Access.GenericAfter (candidate value).view ((family value).waitId 0 lane) ((family value).mmaId 0 lane) :=
  family_wait_before_mma (family value) (HopperCandidateMemoryTests.heterogeneous_source_well_formed value (fun _ => .bits (byte 0))) 0 (by decide) lane

theorem failed_wait_cannot_observe_copy (value : ℝ) (histories : Location → List Tma.Entry) (cluster : Access.ClusterScope)
    (copy : Tma.CopyId) (attempt : Nat) (ha : attempt < 2) :
    ¬Access.CompletionObserved Tma.localShared (candidate value).view histories cluster copy ((family value).failedWaitId 0 2 attempt) :=
  family_failed_wait_not_observed (family value) (HopperCandidateMemoryTests.heterogeneous_source_well_formed value (fun _ => .bits (byte 0))) 0 (by decide) 2 attempt ha

theorem false_reply_cannot_be_success (value : ℝ) :
    (candidate value).eventAt ((family value).failedWaitId 0 2 1) ≠
      some (waitEvent (ctx 1 2) (barrierAddress (stage 0)) (expectedParity 0) true) := by
  rw [actual_failed_wait value 1 (by decide)]
  intro h; cases h

theorem complete_candidate_reconstructs_family (value : ℝ) : Nonempty (ReplySourceFamily 1 (candidate value)) :=
  completed_candidate_reply_family (by decide) (by decide)
    (HopperCandidateMemoryTests.heterogeneous_source_well_formed value (fun _ => .bits (byte 0))) (HopperCandidateMemoryTests.heterogeneous_source_complete value)

theorem independent_data_every_tile_has_collective (a b tiles) (frame : Location → Symbolic.Byte) (hb : tiles ≤ 2^28)
    (tile : Nat) (ht : tile < tiles) : ∃ issue, Nonempty (Unified.Collective (dataCompleteCandidate a b tiles) issue) :=
  completed_candidate_has_collective hb (data_source_well_formed a b tiles frame hb) (data_candidate_local a b tiles hb) tile ht

theorem producer_three_failures_shift_success_and_mma :
    ∃ retries, retries 0 = 3 ∧ retries 1 = 0 ∧
      HopperKernelReconstructionTests.fullEvents[11]? = some (waitEvent (ctx 2 0) (barrierAddress (stage 0)) (expectedParity 0) true) ∧
      HopperKernelReconstructionTests.fullEvents[16]? = some (.mma (replyMark 2 0 HopperKernelReconstructionTests.retryReply retries 0)
        (replyCall 2 0 HopperKernelReconstructionTests.retryReply retries 0)) := by
  obtain ⟨retries,hzero,hone,_,_,hevents⟩ := HopperKernelReconstructionTests.full_producer_reconstructed
  have hw := reply_complete_wait_at 2 0 HopperKernelReconstructionTests.retryReply retries 0 (by decide)
  have hm := reply_complete_mma_at 2 0 HopperKernelReconstructionTests.retryReply retries 0 (by decide)
  have hiw : (replyWaitId 2 0 HopperKernelReconstructionTests.retryReply retries 0).serial = 11 := by
    change 8+retries 0 = 11
    omega
  have him : (replyMmaId 2 0 HopperKernelReconstructionTests.retryReply retries 0).serial = 16 := by
    change 8+retries 0+3+2 = 16
    omega
  rw [hiw,← hevents] at hw
  rw [him,← hevents] at hm
  exact ⟨retries,hzero,hone,hw,hm⟩

end
end Ptx.HopperCandidateCollectiveTests
