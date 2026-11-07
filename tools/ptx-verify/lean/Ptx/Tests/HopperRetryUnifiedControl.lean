import Ptx.Kernels.HopperDoubleBufferRetryUnifiedControl
import Ptx.Hopper.UnifiedMemoryControl
import Ptx.Tests.HopperRetryCtaControl
import Ptx.Tests.HopperRetryNativeControl

/-! Positive complete construct control on actual heterogeneous retry traces,
and negative mixed-graph paths. The fixture remains a negative full-memory
case; these checks never assume arbitrary captured tensor results are correct. -/
namespace Ptx.HopperRetryUnifiedControlTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev family := HopperRetryAdmissionTests.family
abbrev candidate := HopperRetryAdmissionTests.candidate
abbrev source := HopperRetryAdmissionTests.source_well_formed
abbrev zeroInitial := HopperRetryCtaControlTests.zeroInitial

theorem actual_native_ticks (value : ℝ) (tile : Fin 3) (lane : Wgmma.Lane) (index : Fin 4) :
    retryNativeTick (family value) ((family value).nativeId tile lane index) = 12+10*tile.val+index.val :=
  retry_actual_native_tick (family value) tile tile.isLt lane index

theorem actual_fence_before_mma (value : ℝ) (tile : Fin 3) (lane : Wgmma.Lane) :
    Hopper.ProgramOrder (candidate value).view ((family value).nativeId tile lane 0) ((family value).nativeId tile lane 1) := by
  refine ⟨?_,?_,rfl,?_⟩
  · exact (Unified.view_present_iff _ _).mpr (Unified.native_signature_present
      (retry_actual_native_signature (family value) (source value zeroInitial) tile tile.isLt lane 0))
  · exact (Unified.view_present_iff _ _).mpr (Unified.native_signature_present
      (retry_actual_native_signature (family value) (source value zeroInitial) tile tile.isLt lane 1))
  · dsimp [ReplySourceFamily.nativeId]
    omega

theorem actual_prearrival_gap (value : ℝ) (tile : Fin 3) (lane : Wgmma.Lane) :
    retrySourceRank (family value) ((family value).nativeId tile lane 0) < retryUnit (family value)*(1024*(13+10*tile.val)) := by
  have h := retry_before_native_clock_gap (family value) (source value zeroInitial) tile tile.isLt lane 1 (actual_fence_before_mma value tile lane)
  simpa only [Fin.val_one,show 12+10*tile.val+1 = 13+10*tile.val by omega] using h

theorem actual_native_arrival (value : ℝ) (tile : Fin 3) (lane : Wgmma.Lane) :
    Unified.ControlEdge HopperStage.block (candidate value) (retryHistories (family value))
      (.base (.source ((family value).nativeId tile lane 0))) (.arrival ((family value).nativeId tile lane 1)) :=
  Unified.native_arrival_edge (actual_fence_before_mma value tile lane) (by
    rw [retry_actual_native_signature (family value) (source value zeroInitial) tile tile.isLt lane 1]; rfl)

theorem actual_native_rendezvous (value : ℝ) (tile : Fin 3) (index : Fin 4) :
    Unified.ControlEdge HopperStage.block (candidate value) (retryHistories (family value))
      (.arrival ((family value).nativeId tile 0 index)) (.base (.source ((family value).nativeId tile 31 index))) :=
  Unified.native_rendezvous_edge (HopperRetryNativeControlTests.same_warp_matches_actual_instruction value tile index)

theorem actual_operand_issue (value : ℝ) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    Unified.ControlEdge HopperStage.block (candidate value) (retryHistories (family value))
      (.base (.source ((family value).mmaId tile 0))) (.operand ((family value).mmaId tile 0) operand) :=
  Unified.native_issue_edge (by rw [Unified.collective_representative (familyCollective (family value) (source value zeroInitial) tile tile.isLt)]; rfl)

theorem actual_native_finish (value : ℝ) (tile : Fin 3) (lane : Wgmma.Lane) (operand : Wgmma.OperandByte) :
    Unified.ControlEdge HopperStage.block (candidate value) (retryHistories (family value))
      (.operand ((family value).mmaId tile 0) operand) (.base (.source ((family value).nativeWaitId tile lane))) :=
  Unified.native_finish_edge (retry_native_completed (family value) (source value zeroInitial) (by decide) tile tile.isLt lane)

theorem positive_control_admission (value : ℝ) :
    Unified.ControlAdmitted HopperStage.block (candidate value) (retryHistories (family value)) :=
  retry_control_admitted (family value) (by decide) (by decide) (source value zeroInitial)

theorem reconstructed_control_witness (value : ℝ) :
    ∃ actual : ReplySourceFamily 3 (candidate value), Unified.ControlAdmitted HopperStage.block (candidate value) (retryHistories actual) :=
  completed_positive_control_admitted (by decide) (by decide) (source value zeroInitial) (HopperRetryAdmissionTests.source_complete value)

theorem positive_tma_and_control_components (value : ℝ) :
    Unified.TmaComponents code (completeLaunch 3 zeroInitial) (candidate value) Tma.localShared (dataMaps 3) (retryHistories (family value)) ∧
      Unified.ControlAdmitted HopperStage.block (candidate value) (retryHistories (family value)) :=
  ⟨HopperRetryCtaControlTests.positive_tma_components value,positive_control_admission value⟩

theorem actual_mixed_publication_path (value : ℝ) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    Ptx.Event.Path (Unified.ControlEdge HopperStage.block (candidate value) (retryHistories (family value)))
      (Unified.memoryControlNode (retryNativeProducer (family value) tile operand))
      (.operand ((family value).mmaId tile 0) operand) :=
  Unified.native_published_control_path (retry_native_publication (family value) (by decide) (source value zeroInitial)
    (HopperRetryAdmissionTests.actual_descriptor_admission value) tile tile.isLt operand)

theorem reverse_publication_path_rejected (value : ℝ) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    ¬Ptx.Event.Path (Unified.ControlEdge HopperStage.block (candidate value) (retryHistories (family value)))
      (.operand ((family value).mmaId tile 0) operand)
      (Unified.memoryControlNode (retryNativeProducer (family value) tile operand)) := by
  intro hp
  exact (positive_control_admission value).2 _ (.trans (actual_mixed_publication_path value tile operand) hp)

theorem wait_to_operand_path_rejected (value : ℝ) (tile : Fin 3) (lane : Wgmma.Lane) (operand : Wgmma.OperandByte) :
    ¬Ptx.Event.Path (Unified.ControlEdge HopperStage.block (candidate value) (retryHistories (family value)))
      (.base (.source ((family value).nativeWaitId tile lane))) (.operand ((family value).mmaId tile 0) operand) := by
  intro hp
  exact (positive_control_admission value).2 _ (.trans (.single (actual_native_finish value tile lane operand)) hp)

theorem return_to_native_arrival_path_rejected (value : ℝ) (tile : Fin 3) (index : Fin 4) :
    ¬Ptx.Event.Path (Unified.ControlEdge HopperStage.block (candidate value) (retryHistories (family value)))
      (.base (.source ((family value).nativeId tile 31 index))) (.arrival ((family value).nativeId tile 0 index)) := by
  intro hp
  exact (positive_control_admission value).2 _ (.trans (.single (actual_native_rendezvous value tile index)) hp)

end
end Ptx.HopperRetryUnifiedControlTests
