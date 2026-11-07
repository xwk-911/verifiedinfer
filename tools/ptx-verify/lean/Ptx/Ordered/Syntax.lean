import Ptx.Scalar.Syntax
import Ptx.ISA.Scope

/-! Fixed generic-proxy global u32 loads/stores with explicit order and scope.
Scalar slots keep their PCs and existing interpretation. Fences, ordered atomics
and composition with shuffle/async/tensor operations are not represented here. -/
namespace Ptx.Ordered
open Ptx.ISA
noncomputable section

inductive ReadOrder | relaxed | acquire deriving Repr, DecidableEq
inductive WriteOrder | relaxed | release deriving Repr, DecidableEq
inductive Instr
  | scalar (instruction : Scalar.Instr)
  | load (order : ReadOrder) (scope : Scope) (dst : String) (address : Address)
  | store (order : WriteOrder) (scope : Scope) (address : Address) (value : Operand)

def InstructionTyped (registers : Scalar.RegisterDeclarations) (parameters : ParameterDeclarations)
    (length : Nat) : Instr → Prop
  | .scalar instruction => Scalar.InstructionTyped registers parameters length instruction
  | .load _ _ dst address => RegisterFits (Scalar.integerDeclarations registers) 32 dst ∧
      AddressTyped (Scalar.integerDeclarations registers) address
  | .store _ _ address value => AddressTyped (Scalar.integerDeclarations registers) address ∧
      OperandTyped (Scalar.integerDeclarations registers) 32 value
instance (registers parameters length instruction) : Decidable (InstructionTyped registers parameters length instruction) := by
  cases instruction <;> simp only [InstructionTyped] <;> infer_instance

def ProgramTyped (sm : Nat) (registers : Scalar.RegisterDeclarations) (parameters : ParameterDeclarations)
    (code : List Instr) : Prop :=
  70 ≤ sm ∧ Scalar.ProgramTyped registers parameters (code.map fun instruction => match instruction with
    | .scalar plain => plain
    | .load _ _ dst address => .integer (.load .global dst address)
    | .store _ _ address value => .integer (.store .global address value)) ∧
    ∀ instruction ∈ code, InstructionTyped registers parameters code.length instruction
instance (sm registers parameters code) : Decidable (ProgramTyped sm registers parameters code) := by
  unfold ProgramTyped; infer_instance

structure CheckedProgram where
  targetSM : Nat
  registers : Scalar.RegisterDeclarations
  parameters : ParameterDeclarations
  code : List Instr
  valid : ProgramTyped targetSM registers parameters code

theorem CheckedProgram.instruction_typed (program : CheckedProgram) {instruction}
    (hi : instruction ∈ program.code) :
    InstructionTyped program.registers program.parameters program.code.length instruction := program.valid.2.2 instruction hi

/-- Fetch aid for the local scalar computation only. The ordered interpreter
always preserves the original slot's order/scope on every emitted event. -/
def scalarSlot : Instr → Scalar.Instr
  | .scalar instruction => instruction
  | .load _ _ dst address => .integer (.load .global dst address)
  | .store _ _ address value => .integer (.store .global address value)
def scalarSkeleton (code : List Instr) : List Scalar.Instr := code.map scalarSlot

theorem scalar_delegate_fetch (code : List Instr) (pc : Nat) :
    (scalarSkeleton code)[pc]? = (code[pc]?).map scalarSlot := by simp [scalarSkeleton]

end
end Ptx.Ordered
