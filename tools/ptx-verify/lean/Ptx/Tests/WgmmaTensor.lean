import Ptx.Hopper.WgmmaTensor
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin

namespace Ptx.WgmmaTensorTests
open Ptx.ISA Ptx.Hopper.Wgmma
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

theorem first_lane_layout : (List.ofFn (fun slot : Slot => cCoord (0,slot))) = [(0,0),(0,1),(8,0),(8,1)] := by decide
theorem warp_boundaries : cCoord (31,3) = (15,7) ∧ cCoord (32,0) = (16,0) ∧
    cCoord (64,0) = (32,0) ∧ cCoord (96,0) = (48,0) ∧ cCoord (127,3) = (63,7) := by decide
theorem packed_address_samples :
    aAddress (MatrixDescriptor.decode packedA) (0,8) 0 = 128 ∧
    aAddress (MatrixDescriptor.decode packedA) (1,0) 0 = 16 ∧
    aAddress (MatrixDescriptor.decode packedA) (8,0) 0 = 256 ∧
    aAddress (MatrixDescriptor.decode packedA) (63,15) 1 = 2047 ∧
    bAddress (MatrixDescriptor.decode packedB) (0,1) 0 = 2064 ∧
    bAddress (MatrixDescriptor.decode packedB) (8,0) 0 = 2176 ∧
    bAddress (MatrixDescriptor.decode packedB) (15,7) 1 = 2303 := by decide
theorem old_probe_has_overlapping_a :
    aAddress (MatrixDescriptor.decode 34359803904) (0,8) 0 = aAddress (MatrixDescriptor.decode 34359803904) (1,0) 0 := by decide
theorem old_probe_has_overlapping_b :
    bAddress (MatrixDescriptor.decode 34359804032) (8,0) 0 = bAddress (MatrixDescriptor.decode 34359804032) (0,1) 0 := by decide
theorem old_probe_outside_packed_profile : ¬MatrixDescriptor.Packed 34359803904 ∧ ¬MatrixDescriptor.Packed 34359804032 := by decide
theorem unsupported_descriptor_bits :
    ¬MatrixDescriptor.Canonical (packedA+2^14) ∧
    ¬MatrixDescriptor.Canonical (packedA+2^30) ∧
    ¬MatrixDescriptor.Canonical (packedA+2^46) ∧
    ¬MatrixDescriptor.Canonical (packedA+2^49) ∧
    ¬MatrixDescriptor.Canonical (packedA+2^62) ∧
    ¬MatrixDescriptor.Canonical (packedA+2^64) := by decide

def onesA : ACoord → ℝ := fun _ => 1
def onesB : BCoord → ℝ := fun _ => 1
def zeroC : Lane × Slot → ℝ := fun _ => 0
def good : Lane → Call := tensorCalls zeroC onesA onesB
def bad : Lane → Call := fun lane => {good lane with output := fun _ => 0}
def memory : Location → Symbolic.Byte := tileMemory .zero onesA onesB
theorem independent_tensor_witness : TensorConditions .zero good memory := tensor_component_witness .zero zeroC onesA onesB
theorem concrete_instruction_result : (good 127).output 3 = 16 := by
  norm_num [good,tensorCalls,results,gatherC,matrixStep,scatterC,zeroC,onesA,onesB]
theorem bad_reply_preserves_cohort : Cohort bad :=
  ⟨fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩
theorem bad_reply_preserves_read_agreement : ∀ lane, InputAgreement .zero (bad lane) memory :=
  fun _ => packed_agreement .zero _ onesA onesB rfl rfl (fun _ => rfl)
theorem bad_reply_rejected : ¬TensorConditions .zero bad memory := by
  intro h
  have hh := congrFun (tensor_correct h (packed_storage .zero (bad 0) onesA onesB rfl rfl)) (0,0)
  norm_num [scatterC,bad,good,tensorCalls,matrixStep,onesA,onesB,zeroC] at hh
theorem integer_replies_not_f16 (call : Call) (a : ACoord → ℝ) (b : BCoord → ℝ) :
    ¬InputValues {call with operandBytes := fun _ => .bits (byte 0)} a b := by
  intro h
  have hh := h.1 (0,0) 0
  cases hh

def nonuniformA (p : ACoord) : ℝ := if p.2.val = p.1.val%16 then (p.1.val+1 : Nat) else 0
def nonuniformB (p : BCoord) : ℝ := (p.1.val+p.2.val+1 : Nat)
def nonuniformC (p : CCoord) : ℝ := (1000*p.1.val+p.2.val : Nat)
theorem nonuniform_full_component :
    TensorConditions .zero (tensorCalls (gatherC nonuniformC) nonuniformA nonuniformB)
      (tileMemory .zero nonuniformA nonuniformB) := tensor_component_witness .zero _ _ _
theorem nonuniform_last_output :
    (tensorCalls (gatherC nonuniformC) nonuniformA nonuniformB 127).output 3 = 64479 := by
  norm_num [tensorCalls,results,gatherC,scatterC,cCoord,cOwner,matrixStep,
    nonuniformA,nonuniformB,nonuniformC,Fin.sum_univ_succ]

end
end Ptx.WgmmaTensorTests
