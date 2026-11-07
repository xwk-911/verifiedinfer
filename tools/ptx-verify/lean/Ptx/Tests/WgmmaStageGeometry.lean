import Ptx.Generated.HopperGemmStage
import Ptx.Hopper.WgmmaStorage

/-! Geometry and checked source data for the new single-stage target. These
are not source execution, resource/memory admission or GEMM correctness. -/
namespace Ptx.WgmmaStageGeometryTests
open Ptx.ISA Ptx.Hopper
noncomputable section

def block : Dim3 := ⟨4,8,4⟩
def tid (lane : Wgmma.Lane) : Dim3 := ⟨lane.val%4,(lane.val%32)/4,lane.val/32⟩
def offset (lane : Wgmma.Lane) (slot : Wgmma.Slot) : Nat :=
  4*(8*(16*(tid lane).z+(tid lane).y)+2*(tid lane).x)+256*(slot.val/2)+4*(slot.val%2)
theorem all_lanes_within (lane : Wgmma.Lane) : (tid lane).Within block := by
  have := lane.isLt
  dsimp [tid,block,Dim3.Within]
  omega
theorem actual_linear_lane (lane : Wgmma.Lane) : (tid lane).linear block = lane.val := by
  have := lane.isLt
  dsimp [tid,block,Dim3.linear]
  omega
theorem source_store_matches_layout (lane : Wgmma.Lane) (slot : Wgmma.Slot) :
    offset lane slot = 4*(8*(Wgmma.cCoord (lane,slot)).1.val+(Wgmma.cCoord (lane,slot)).2.val) := by
  dsimp [offset,tid,Wgmma.cCoord]
  omega
theorem output_bounds (lane : Wgmma.Lane) (slot : Wgmma.Slot) : offset lane slot < 2048 ∧ offset lane slot%4 = 0 := by
  rw [source_store_matches_layout]
  have := (Wgmma.cCoord (lane,slot)).1.isLt
  have := (Wgmma.cCoord (lane,slot)).2.isLt
  omega
theorem output_unique {left right : Wgmma.Lane × Wgmma.Slot}
    (h : offset left.1 left.2 = offset right.1 right.2) : left = right := by
  rw [source_store_matches_layout,source_store_matches_layout] at h
  change 4*(8*(Wgmma.cCoord left).1.val+(Wgmma.cCoord left).2.val) =
    4*(8*(Wgmma.cCoord right).1.val+(Wgmma.cCoord right).2.val) at h
  apply Wgmma.c_unique_owner
  apply Prod.ext <;> apply Fin.ext
  all_goals
    have := (Wgmma.cCoord left).1.isLt
    have := (Wgmma.cCoord left).2.isLt
    have := (Wgmma.cCoord right).1.isLt
    have := (Wgmma.cCoord right).2.isLt
    omega
theorem output_covered (row : Fin 64) (col : Fin 8) :
    ∃ lane slot, offset lane slot = 4*(8*row.val+col.val) := by
  refine ⟨(Wgmma.cOwner (row,col)).1,(Wgmma.cOwner (row,col)).2,?_⟩
  rw [source_store_matches_layout]
  simp only [Prod.mk.eta,Wgmma.c_coord_owner]
theorem shifted_descriptor_profiles : Wgmma.MatrixDescriptor.Packed 68720001025 ∧ Wgmma.MatrixDescriptor.Packed 68720001153 := by decide
theorem source_transfer_and_wait_sites :
    Generated.hopper_gemm_stage.program.length = 47 ∧
    (Generated.hopper_gemm_stage.program[23]?.map (fun i => match i with | .arriveExpectTx _ (.imm n) => n | _ => 0)) = some 2304 ∧
    (Generated.hopper_gemm_stage.program[26]?.map (fun i => match i with | .tryWaitParity _ _ _ => true | _ => false)) = some true ∧
    (Generated.hopper_gemm_stage.program[29]?.map (fun i => match i with | .wgmma (.mma _ _ _ _) => true | _ => false)) = some true := by decide

end
end Ptx.WgmmaStageGeometryTests
