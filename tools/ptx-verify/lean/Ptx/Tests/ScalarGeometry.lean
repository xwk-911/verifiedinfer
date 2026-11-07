import Ptx.Scalar.Rules
import Ptx.Scalar.Execution
import Ptx.Scalar.Geometry

/-! Geometry is execution input, not an oracle choice or a unit-block assumption.
These checks do not imply physical GPU launch bounds. -/
namespace Ptx.ScalarGeometryTests
open Ptx.ISA Ptx.Scalar

def sizeCode : List Scalar.Instr := [.readSpecial "%sx" (.ntid .x),.integer .ret]
def sizeFinal (ctx : Scalar.Context) : Scalar.State := {
  core := {thread := {pc := 1,status := .done,regs := [("%sx",wrap 32 ctx.block.x)]}}
}

theorem size_run (ctx : Scalar.Context) (oracle : Scalar.Oracle) :
    Scalar.run ctx oracle sizeCode 2 {} = .ok (sizeFinal ctx,[]) := rfl

def ctx : Scalar.Context := {id := ⟨⟨2,3,0⟩,⟨4,5,0⟩⟩,block := ⟨8,16,1⟩}
def shape : Geometry := ⟨⟨3,4,1⟩,ctx.block⟩

theorem coordinates :
    SpecialRegister.value (.ctaid .x) ctx = 2 ∧ SpecialRegister.value (.ctaid .y) ctx = 3 ∧
    SpecialRegister.value (.tid .y) ctx = 5 ∧ SpecialRegister.value (.ntid .x) ctx = 8 ∧
    SpecialRegister.value (.ntid .y) ctx = 16 ∧ row ctx.block ctx.id = 53 ∧ col ctx.block ctx.id = 20 := by decide

theorem unique_coordinates {a b : ThreadId} (ha : a.Valid shape) (hb : b.Valid shape)
    (hr : row ctx.block a = row ctx.block b) (hc : col ctx.block a = col ctx.block b) : a = b :=
  output_coordinates_injective rfl rfl ha hb hr hc

def forgedSize : Scalar.ThreadTrace := {
  id := ⟨.zero,.zero⟩
  oracle := fun _ => .integer 0
  count := 2
  final := (sizeFinal {id := ⟨.zero,.zero⟩}).core
  events := []
}

theorem unit_size_produced : Scalar.Produced sizeCode [] forgedSize := ⟨[],rfl⟩

theorem wrong_launch_size_rejected : ¬ Scalar.Produced sizeCode [] forgedSize ⟨2,1,1⟩ := by
  rintro ⟨floats,h⟩
  simp only [forgedSize] at h
  rw [size_run] at h
  have hs := congrArg (fun result : Scalar.State × List Scalar.Kind => lookup "%sx" result.1.core.thread.regs)
    (Except.ok.inj h)
  norm_num [sizeFinal,forgedSize,lookup,wrap,Dim3.one] at hs

theorem wrong_launch_candidate_rejected (initial : Scalar.ByteMap) :
    ¬ Scalar.WellFormed sizeCode ⟨⟨.one,⟨2,1,1⟩⟩,[],initial⟩ ⟨[forgedSize]⟩ := by
  intro hw
  exact wrong_launch_size_rejected (hw.2.2.1 forgedSize (by simp)).2

theorem special_float_destination_rejected :
    ¬ Scalar.InstructionTyped [("%f",.floating .f32)] [] 1 (.readSpecial "%f" (.ntid .x)) := by decide

end Ptx.ScalarGeometryTests
