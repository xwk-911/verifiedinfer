import Ptx.Hopper.WgmmaSyntax

/-! Explicit PTX 8.0 / sm_90a backend. The initial extension retains five fixed
CTA-local layout-v0 mbarrier forms. Unsupported qualifiers, returned arrival
state tokens, cluster forms and optional wait operands are not erased. -/
namespace Ptx.Hopper
open Ptx.ISA
noncomputable section

inductive Target | sm90a deriving Repr, DecidableEq
inductive Instr
  | wgmma (instruction : Wgmma.Instr)
  | ampere (instruction : Ampere.Instr)
  | tmaLoad2D (dst : Address) (descriptor x y : Operand) (barrier : Address)
  | proxyFenceAsyncShared
  | mbarrierInit (address : Address) (count : Operand)
  | mbarrierInval (address : Address)
  | arriveExpectTx (address : Address) (count : Operand)
  | completeTx (address : Address) (count : Operand)
  | tryWaitParity (dst : String) (address : Address) (parity : Operand)

def InstructionTyped (registers : Scalar.RegisterDeclarations) (parameters : ParameterDeclarations) (length : Nat) : Instr → Prop
  | .wgmma i => Wgmma.InstructionTyped registers i
  | .ampere i => Ampere.InstructionTyped registers parameters length i
  | .tmaLoad2D dst descriptor x y barrier => AddressTyped (Scalar.integerDeclarations registers) dst ∧
      OperandTyped (Scalar.integerDeclarations registers) 64 descriptor ∧
      OperandTyped (Scalar.integerDeclarations registers) 32 x ∧ OperandTyped (Scalar.integerDeclarations registers) 32 y ∧
      AddressTyped (Scalar.integerDeclarations registers) barrier
  | .proxyFenceAsyncShared => True
  | .mbarrierInit address count | .arriveExpectTx address count | .completeTx address count =>
      AddressTyped (Scalar.integerDeclarations registers) address ∧ OperandTyped (Scalar.integerDeclarations registers) 32 count
  | .mbarrierInval address => AddressTyped (Scalar.integerDeclarations registers) address
  | .tryWaitParity dst address parity => RegisterFits (Scalar.integerDeclarations registers) 1 dst ∧
      AddressTyped (Scalar.integerDeclarations registers) address ∧ OperandTyped (Scalar.integerDeclarations registers) 32 parity
instance (registers parameters length instruction) : Decidable (InstructionTyped registers parameters length instruction) := by
  cases instruction <;> simp only [InstructionTyped] <;> infer_instance

def ProgramTyped (sm : Nat) (registers : Scalar.RegisterDeclarations) (parameters : ParameterDeclarations) (code : List Instr) : Prop :=
  sm = 90 ∧ (registers.map Prod.fst).Nodup ∧ (parameters.map Prod.fst).Nodup ∧
  (∀ p ∈ parameters, SupportedWidth p.2) ∧ code ≠ [] ∧
  ∀ instruction ∈ code, InstructionTyped registers parameters code.length instruction
instance (sm registers parameters code) : Decidable (ProgramTyped sm registers parameters code) := by
  unfold ProgramTyped; infer_instance

structure CheckedProgram where
  target : Target := .sm90a
  targetSM : Nat
  registers : Scalar.RegisterDeclarations
  parameters : ParameterDeclarations
  code : List Instr
  valid : ProgramTyped targetSM registers parameters code

theorem CheckedProgram.instruction_typed (p : CheckedProgram) {i : Instr} (hi : i ∈ p.code) :
    InstructionTyped p.registers p.parameters p.code.length i := p.valid.2.2.2.2.2 i hi

/-- Retain all branch PCs when delegating embedded Ampere instructions. The
placeholder slots are never executed by that interpreter. -/
def ampereSkeleton (code : List Instr) : List Ampere.Instr := code.map (fun i => match i with
  | .ampere instruction => instruction
  | _ => .scalar (.integer .ret))
theorem ampereSkeleton_slot {code : List Instr} {pc : Nat} {i : Ampere.Instr} (hi : code[pc]? = some (.ampere i)) :
    (ampereSkeleton code)[pc]? = some i := by simp [ampereSkeleton,List.getElem?_map,hi]

end
end Ptx.Hopper
