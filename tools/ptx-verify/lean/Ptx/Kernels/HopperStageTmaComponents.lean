import Ptx.Kernels.HopperStageControl

/-! Independent source/resource/control/input components for arbitrary A/B.
The coupled WGMMA memory/causality graph and global observer are not admitted
by this bundle. It is not the full GEMM Pre or its correctness theorem. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section

theorem control_internal_order {left right} (he : Tma.InternalEdge resourceCandidate left right) :
    controlRank left < controlRank right := by
  cases he <;> dsimp only [controlRank] <;> omega
theorem histories_rank_pairwise (location : Location) :
    ((histories location).map Tma.Entry.origin).Pairwise (fun a b => controlRank a.node < controlRank b.node) := by
  unfold histories
  split
  · exact history_rank_pairwise
  · simp
theorem control_resource_order {left right} (he : Tma.ResourceEdge histories left right) :
    controlRank left < controlRank right := Tma.resource_edge_rank_of_pairwise histories_rank_pairwise he
theorem resource_control_acyclic : Tma.ControlAcyclic resourceCandidate histories :=
  Tma.control_acyclic_of_rank controlRank (fun _ _ => control_program_order)
    (fun _ _ => control_cta_order) (fun _ _ => control_internal_order) (fun _ _ => control_resource_order)
theorem stage_control_acyclic (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    Tma.ControlAcyclic (candidate a b).view histories := by
  apply (Tma.ResourceErasure.control_acyclic_preserved (candidate a b).view histories).mp
  rw [candidate_resource_erasure]
  exact resource_control_acyclic
theorem stage_tma_components (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame) :
    Unified.TmaComponents Generated.hopper_gemm_stage.program (launch (representedInitial a b frame))
      (candidate a b) Tma.localShared maps histories :=
  ⟨source_well_formed a b _,source_complete a b,stage_descriptor_agreement a b,
    stage_payload_agreement a b frame,stage_all_histories_valid a b,stage_control_acyclic a b⟩
theorem stage_checked_components (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame) :
    Unified.TmaComponents Generated.hopper_gemm_stage.program (launch (representedInitial a b frame))
        (candidate a b) Tma.localShared maps histories ∧
      Unified.SchedulesAdmitted block (candidate a b) ∧
      Wgmma.TensorConditions .zero (calls a b) (transferView a b) :=
  ⟨stage_tma_components a b frame,stage_schedules_admitted a b,tensor_component a b⟩

end
end Ptx.Kernels.HopperStage
