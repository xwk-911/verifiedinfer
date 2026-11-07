import Ptx.Hopper.WgmmaStorage

/-! Exact-real semantics of the fixed shared/shared WGMMA instruction. Typed
input fragments must agree with descriptor-derived shared reads; arbitrary
matrix replies are not admitted. A separate witness constructs replies from
inputs. These conditions are a tensor component, not full source/SIMT, weak
memory/RF, proxy-publication, allocation/lifetime or runtime admission. -/
namespace Ptx.Hopper.Wgmma
open Ptx.ISA
noncomputable section

structure Cohort (calls : Lane → Call) : Prop where
  lane : ∀ lane, (calls lane).lane = lane
  a : ∀ lane, (calls lane).a = (calls 0).a
  b : ∀ lane, (calls lane).b = (calls 0).b
  d : ∀ lane, (calls lane).d.names = (calls 0).d.names
  ordinal : ∀ lane, (calls lane).ordinal = (calls 0).ordinal
  group : ∀ lane, (calls lane).group = (calls 0).group
structure TensorConditions (cta : Dim3) (calls : Lane → Call) (memory : Location → Symbolic.Byte) : Prop where
  cohort : Cohort calls
  aProfile : MatrixDescriptor.Packed (calls 0).a
  bProfile : MatrixDescriptor.Packed (calls 0).b
  agreement : ∀ lane, InputAgreement cta (calls lane) memory
  tensor : ∃ a b, (∀ lane, InputValues (calls lane) a b) ∧
    Arithmetic a b (fun p => (calls p.1).input p.2) (fun p => (calls p.1).output p.2)

theorem tensor_correct {cta calls memory a b}
    (h : TensorConditions cta calls memory) (hm : MatrixStorage cta (calls 0) memory a b) :
    scatterC (fun p => (calls p.1).output p.2) = matrixStep a b (scatterC (fun p => (calls p.1).input p.2)) := by
  obtain ⟨aa,bb,hv,harith⟩ := h.tensor
  obtain ⟨ha,hb⟩ := input_values_unique (hv 0) (input_values_of_memory (h.agreement 0) hm)
  rw [ha,hb] at harith
  have he : (fun p => (calls p.1).output p.2) = results a b (fun p => (calls p.1).input p.2) := funext harith
  rw [he]
  exact scatter_gather_c _
theorem tensor_correct_accumulator {cta calls memory a b c}
    (h : TensorConditions cta calls memory) (hm : MatrixStorage cta (calls 0) memory a b)
    (hc : ∀ p, (calls p.1).input p.2 = gatherC c p) :
    scatterC (fun p => (calls p.1).output p.2) = matrixStep a b c := by
  rw [tensor_correct h hm,funext hc,scatter_gather_c]

def tensorCalls (input : Lane × Slot → ℝ) (a : ACoord → ℝ) (b : BCoord → ℝ) : Lane → Call := fun lane => {
  ordinal := 0
  group := 0
  lane := lane
  d := ⟨"%d0","%d1","%d2","%d3"⟩
  a := packedA
  b := packedB
  scaleD := true
  input := fun slot => input (lane,slot)
  output := fun slot => results a b input (lane,slot)
  query := 0
  operandBytes := payload a b
}
theorem tensor_calls_cohort (input a b) : Cohort (tensorCalls input a b) :=
  ⟨fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩
theorem tensor_component_witness (cta : Dim3) (input : Lane × Slot → ℝ) (a : ACoord → ℝ) (b : BCoord → ℝ) :
    TensorConditions cta (tensorCalls input a b) (tileMemory cta a b) := {
  cohort := tensor_calls_cohort input a b
  aProfile := packed_a_profile
  bProfile := packed_b_profile
  agreement := fun _ => packed_agreement cta _ a b rfl rfl (fun _ => rfl)
  tensor := ⟨a,b,fun _ => ⟨payload_a a b,payload_b a b⟩,fun _ => rfl⟩
}
theorem tensor_witness_result (cta : Dim3) (a : ACoord → ℝ) (b : BCoord → ℝ) (c : CCoord → ℝ) :
    scatterC (fun p => (tensorCalls (gatherC c) a b p.1).output p.2) = matrixStep a b c :=
  tensor_correct_accumulator (tensor_component_witness cta (gatherC c) a b)
    (packed_storage cta _ a b rfl rfl) (fun _ => rfl)

end
end Ptx.Hopper.Wgmma
