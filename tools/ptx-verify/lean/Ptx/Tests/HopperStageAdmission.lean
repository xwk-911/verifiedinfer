import Ptx.Kernels.HopperStageCompletion
import Ptx.Tests.HopperStage

/-! Actual single-stage resource/input component tests. These do not replace
the still-open combined weak-memory or arbitrary-candidate correctness proof. -/
namespace Ptx.HopperStageAdmissionTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels.HopperStage
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def frame : Location → Symbolic.Byte := fun _ => .bits (byte 165)
def input : Location → Symbolic.Byte := representedInitial WgmmaTensorTests.nonuniformA WgmmaTensorTests.nonuniformB frame
theorem last_a_input : input ⟨.global,67583⟩ = .realPart .f16 64 1 := by
  norm_num [input,representedInitial,Wgmma.tileByte,Wgmma.aByteOwner,WgmmaTensorTests.nonuniformA]
theorem last_b_input : input ⟨.global,69887⟩ = .realPart .f16 23 1 := by
  norm_num [input,representedInitial,Wgmma.tileByte,Wgmma.bByteOwner,WgmmaTensorTests.nonuniformB]
theorem untouched_initial_guard : input ⟨.global,10240⟩ = .bits (byte 165) := by rfl
theorem actual_input_resource_component :
    Unified.TmaComponents Generated.hopper_gemm_stage.program (launch input)
      (candidate WgmmaTensorTests.nonuniformA WgmmaTensorTests.nonuniformB) Tma.localShared maps histories :=
  stage_tma_components _ _ frame
theorem full_history_size : resourceHistory.length = 133 := by decide
theorem last_peer_observes_b : Tma.observation resourceHistory 3 131 = some (copyId 6,waitId 127) := each_wait_observes_b 127

def droppedNotice (serial : Nat) : List Tma.Entry := resourceHistory.filter (fun entry => entry.origin != .notification (copyId serial))
def earlyInvalidation : List Tma.Entry := resourceHistory.take 5++[⟨.source (copyId 18).issue,.inval⟩]++
  (resourceHistory.drop 5).take 127
theorem missing_a_notice_rejected : (Mbarrier.run none ((droppedNotice 5).map Tma.Entry.operation)).isSome = false := by decide
theorem missing_b_notice_rejected : (Mbarrier.run none ((droppedNotice 6).map Tma.Entry.operation)).isSome = false := by decide
theorem early_invalidation_keeps_inventory : earlyInvalidation.Perm resourceHistory := by decide
theorem early_invalidation_keeps_source_order : Tma.SourceOrder earlyInvalidation := by decide
theorem early_invalidation_rejected : (Mbarrier.run none (earlyInvalidation.map Tma.Entry.operation)).isSome = false := by decide

end
end Ptx.HopperStageAdmissionTests
