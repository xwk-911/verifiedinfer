import Ptx.Kernels.HopperStageCollective

/-! Source-matched tensor components for the complete stage execution. The
abstract post-transfer view is shifted to actual shared offsets 16/2064.
Actual TMA payloads and representative WGMMA byte replies agree with this
view. This is not full resource, RF/coherence/proxy, allocation/lifetime or
global observer admission, and does not identify arbitrary launch.initial
with the chosen global input matrices. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def transferView (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (location : Location) : Symbolic.Byte :=
  Wgmma.tileMemory .zero a b ⟨location.space,location.address-16⟩
theorem shifted_a_profile : Wgmma.MatrixDescriptor.Packed 68720001025 := by decide
theorem shifted_b_profile : Wgmma.MatrixDescriptor.Packed 68720001153 := by decide
theorem shifted_a_base : (Wgmma.MatrixDescriptor.decode 68720001025).base = 16 := by decide
theorem shifted_b_base : (Wgmma.MatrixDescriptor.decode 68720001153).base = 2064 := by decide
theorem transfer_storage (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (call : Wgmma.Call)
    (ha : call.a = 68720001025) (hb : call.b = 68720001153) :
    Wgmma.MatrixStorage .zero call (transferView a b) a b := by
  constructor
  · intro p byte
    change transferView a b ⟨.shared .zero,Wgmma.aAddress (Wgmma.MatrixDescriptor.decode call.a) p byte⟩ = _
    rw [ha,Wgmma.packed_a_address shifted_a_profile,shifted_a_base]
    simpa only [transferView,Wgmma.tileMemory,ite_true,Nat.add_sub_cancel_left] using Wgmma.tile_byte_a a b p byte
  · intro p byte
    change transferView a b ⟨.shared .zero,Wgmma.bAddress (Wgmma.MatrixDescriptor.decode call.b) p byte⟩ = _
    rw [hb,Wgmma.packed_b_address shifted_b_profile,shifted_b_base]
    have hh : 2064+(Wgmma.bOffset (p,byte)).val-16 = 2048+(Wgmma.bOffset (p,byte)).val := by omega
    simpa only [transferView,Wgmma.tileMemory,ite_true,hh] using Wgmma.tile_byte_b a b p byte
theorem transfer_agreement (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    Wgmma.InputAgreement .zero (calls a b lane) (transferView a b) := by
  have hm := transfer_storage a b (calls a b lane) rfl rfl
  intro operand
  cases operand with
  | a p byte => exact (Wgmma.payload_a a b p byte).trans (hm.1 p byte).symm
  | b p byte => exact (Wgmma.payload_b a b p byte).trans (hm.2 p byte).symm
theorem accumulator_zero : accumulatorInput = (fun _ => 0) := by
  funext slot
  simp only [accumulatorInput,zeroLiteral,Scalar.F32Literal.zero_value,ite_self]
theorem tensor_component (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    Wgmma.TensorConditions .zero (calls a b) (transferView a b) := by
  refine ⟨calls_cohort a b,shifted_a_profile,shifted_b_profile,transfer_agreement a b,?_⟩
  refine ⟨a,b,fun _ => ⟨Wgmma.payload_a a b,Wgmma.payload_b a b⟩,?_⟩
  intro p
  change Wgmma.results a b (fun _ => 0) p = Wgmma.results a b (fun q => accumulatorInput q.2) p
  rw [accumulator_zero]
theorem tensor_result (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    Wgmma.scatterC (fun p => (calls a b p.1).output p.2) = Wgmma.matrixStep a b (fun _ => 0) := by
  apply Wgmma.tensor_correct_accumulator (cta := .zero) (calls := calls a b) (memory := transferView a b)
    (a := a) (b := b) (c := fun _ => 0) (tensor_component a b) (transfer_storage a b (calls a b 0) rfl rfl)
  intro p
  change accumulatorInput p.2 = 0
  rw [accumulator_zero]

theorem transfer_a_payload (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (offset : Fin 2048) :
    (aPayload a)[offset.val]? = some (transferView a b ⟨.shared .zero,16+offset.val⟩) := by
  simp only [aPayload,List.getElem?_ofFn,dite_eq_left offset.isLt]
  have hh := Wgmma.tile_byte_a a b (Wgmma.aByteOwner offset).1 (Wgmma.aByteOwner offset).2
  change Wgmma.tileByte a b (Wgmma.aOffset (Wgmma.aByteOwner offset)).val = _ at hh
  rw [Wgmma.a_offset_owner] at hh
  simp only [transferView,Wgmma.tileMemory,ite_true,Nat.add_sub_cancel_left]
  rw [hh]
theorem transfer_b_payload (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (offset : Fin 256) :
    (bPayload b)[offset.val]? = some (transferView a b ⟨.shared .zero,2064+offset.val⟩) := by
  simp only [bPayload,List.getElem?_ofFn,dite_eq_left offset.isLt]
  have hh := Wgmma.tile_byte_b a b (Wgmma.bByteOwner offset).1 (Wgmma.bByteOwner offset).2
  change Wgmma.tileByte a b (2048+(Wgmma.bOffset (Wgmma.bByteOwner offset)).val) = _ at hh
  rw [Wgmma.b_offset_owner] at hh
  have hs : 2064+offset.val-16 = 2048+offset.val := by omega
  simp only [transferView,Wgmma.tileMemory,ite_true,hs]
  rw [hh]

def copyId (serial : Nat) : Tma.CopyId := ⟨⟨(ctx 0).id,serial⟩⟩
def copyA (a : Wgmma.ACoord → ℝ) : TmaCopy := ⟨4096,aView,⟨0,0⟩,16,0,0,aPayload a⟩
def copyB (b : Wgmma.BCoord → ℝ) : TmaCopy := ⟨4224,bView,⟨0,0⟩,2064,0,2,bPayload b⟩
theorem actual_copy_a (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) : Tma.copyAt (candidate a b).view (copyId 5) = some (copyA a) := by
  apply Tma.copyAt_iff.mpr
  apply Unified.view_tma_iff.mpr
  change (candidate a b).eventAt ⟨(trace a b 0).id,5⟩ = _
  rw [Unified.eventAt_of_member (trace_ids_unique a b) (List.mem_ofFn.mpr ⟨(0 : Wgmma.Lane),rfl⟩)]
  change (middleEvents a b 0 true++_)[5]? = _
  rw [List.getElem?_append_left (by rw [middle_length]; decide)]
  rfl
theorem actual_copy_b (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) : Tma.copyAt (candidate a b).view (copyId 6) = some (copyB b) := by
  apply Tma.copyAt_iff.mpr
  apply Unified.view_tma_iff.mpr
  change (candidate a b).eventAt ⟨(trace a b 0).id,6⟩ = _
  rw [Unified.eventAt_of_member (trace_ids_unique a b) (List.mem_ofFn.mpr ⟨(0 : Wgmma.Lane),rfl⟩)]
  change (middleEvents a b 0 true++_)[6]? = _
  rw [List.getElem?_append_left (by rw [middle_length]; decide)]
  rfl
theorem source_and_tensor_components (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (initial : Location → Symbolic.Byte) :
    Unified.WellFormed Generated.hopper_gemm_stage.program (launch initial) (candidate a b) ∧
    Unified.Complete (candidate a b) ∧
    Wgmma.TensorConditions .zero (calls a b) (transferView a b) ∧
    Tma.copyAt (candidate a b).view (copyId 5) = some (copyA a) ∧
    Tma.copyAt (candidate a b).view (copyId 6) = some (copyB b) :=
  ⟨source_well_formed a b initial,source_complete a b,tensor_component a b,actual_copy_a a b,actual_copy_b a b⟩

end
end Ptx.Kernels.HopperStage
