import Ptx.Hopper.WgmmaIssueRules
import Ptx.Tests.WgmmaProtocol
import Ptx.Tests.WgmmaTensor

/-! Actual generated source beforeMma and MMA event, parameterized by arbitrary
real A/B. The oracle replies have an independently constructed packed shared
view and satisfy the tensor component. This does NOT initialize the PTX
probe's shared arrays or provide a complete combined memory/RF execution.
Required full GEMM admission/correctness/nonvacuity remains separate. -/
namespace Ptx.WgmmaTensorSourceTests
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def ctx (lane : Wgmma.Lane) : Scalar.Context := {
  id := ⟨.zero,⟨lane.val,0,0⟩⟩,params := [("OUT",8192)],block := ⟨128,1,1⟩
}
def zeroInput (slot : Wgmma.Slot) : ℝ :=
  if slot.val = 0 then WgmmaProtocolTests.zero.value else if slot.val = 1 then WgmmaProtocolTests.zero.value
  else if slot.val = 2 then WgmmaProtocolTests.zero.value else WgmmaProtocolTests.zero.value
theorem zero_input_value : zeroInput = (fun _ => 0) := by
  funext slot
  simp only [zeroInput,WgmmaProtocolTests.zero,Scalar.F32Literal.zero_value,ite_self]
def oracle (lane : Wgmma.Lane) (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) : Wgmma.Oracle := {
  WgmmaProtocolTests.oracle with
  matrix := fun _ slot => Wgmma.results a b (fun _ => 0) (lane,slot)
  operands := fun _ => Wgmma.payload a b
}
def beforeMma (lane : Wgmma.Lane) : Wgmma.State :=
  ((Wgmma.run (ctx lane) WgmmaProtocolTests.oracle Generated.wgmma_probe.program 11 {}).toOption.getD ({},[])).1
def headEvents (lane : Wgmma.Lane) : List Wgmma.Event := [.fence ⟨10,0,lane.val/128⟩]
def call (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) : Wgmma.Call :=
  Wgmma.makeCall (ctx lane) (beforeMma lane) (oracle lane a b) WgmmaProtocolTests.d Wgmma.packedA Wgmma.packedB true zeroInput

theorem actual_prefix (lane : Wgmma.Lane) (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    Wgmma.run (ctx lane) (oracle lane a b) Generated.wgmma_probe.program 11 {} = .ok (beforeMma lane,headEvents lane) := by rfl
theorem actual_mma_step (lane : Wgmma.Lane) (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    Wgmma.step (ctx lane) (oracle lane a b) Generated.wgmma_probe.program (beforeMma lane) =
      .ok (Wgmma.issueState (beforeMma lane) (call a b lane),[.mma (Wgmma.mark (ctx lane) (beforeMma lane)) (call a b lane)]) := by
  exact Wgmma.mma_execute (ctx := ctx lane) (oracle := oracle lane a b)
    (code := Generated.wgmma_probe.program) (s := beforeMma lane) (d := WgmmaProtocolTests.d)
    (a := "%a") (b := "%b") (scaleD := .imm 1) (pa := Wgmma.packedA) (pb := Wgmma.packedB)
    (scale := 1) (input := zeroInput) rfl rfl rfl (by decide) rfl rfl rfl rfl rfl
theorem actual_issued_prefix (lane : Wgmma.Lane) (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    Wgmma.run (ctx lane) (oracle lane a b) Generated.wgmma_probe.program 12 {} =
      .ok (Wgmma.issueState (beforeMma lane) (call a b lane),
        headEvents lane++[.mma (Wgmma.mark (ctx lane) (beforeMma lane)) (call a b lane)]) := by
  rw [show 12 = 11+1 by rfl,Wgmma.run_add,actual_prefix]
  simp only [Except.bind,Wgmma.run,actual_mma_step,List.append_nil]
theorem actual_issue_pc (lane : Wgmma.Lane) : (Wgmma.mark (ctx lane) (beforeMma lane)).pc = 11 := by rfl
theorem actual_operand_reply (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (operand : Wgmma.OperandByte) :
    (call a b lane).operandBytes operand.index = Wgmma.payload a b operand.index := by rfl

theorem actual_cohort (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) : Wgmma.Cohort (call a b) := by
  refine ⟨?_,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩
  intro lane
  apply Fin.ext
  exact Nat.mod_eq_of_lt lane.isLt
theorem actual_tensor_component (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    Wgmma.TensorConditions .zero (call a b) (Wgmma.tileMemory .zero a b) := by
  refine ⟨actual_cohort a b,Wgmma.packed_a_profile,Wgmma.packed_b_profile,?_,?_⟩
  · intro lane
    exact Wgmma.packed_agreement .zero (call a b lane) a b rfl rfl (fun _ => rfl)
  · refine ⟨a,b,fun _ => ⟨Wgmma.payload_a a b,Wgmma.payload_b a b⟩,?_⟩
    intro p
    change Wgmma.results a b (fun _ => 0) p = Wgmma.results a b (fun q => zeroInput q.2) p
    rw [zero_input_value]
theorem actual_tensor_result (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    Wgmma.scatterC (fun p => (call a b p.1).output p.2) = Wgmma.matrixStep a b (fun _ => 0) := by
  apply Wgmma.tensor_correct_accumulator (cta := .zero) (calls := call a b)
    (memory := Wgmma.tileMemory .zero a b) (a := a) (b := b) (c := fun _ => 0) (actual_tensor_component a b)
    (Wgmma.packed_storage .zero (call a b 0) a b rfl rfl)
  intro p
  change zeroInput p.2 = 0
  rw [zero_input_value]

end
end Ptx.WgmmaTensorSourceTests
