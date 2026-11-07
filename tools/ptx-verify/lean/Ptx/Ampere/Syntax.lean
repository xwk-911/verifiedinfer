import Ptx.Scalar.Syntax
import Ptx.Ampere.MmaSyntax

/-! Explicit Ampere extension. Non-bulk copies carry cache hint, addresses and
byte width; unsupported optional copy operands are rejected by the frontend.
Scalar instructions retain their original PC in the extended program. -/
namespace Ptx.Ampere
open Ptx.ISA
noncomputable section

inductive CopyCache | ca | cg deriving Repr, DecidableEq
inductive Instr
  | scalar (instruction : Scalar.Instr)
  | copy (cache : CopyCache) (dst src : Address) (bytes : Nat)
  | commit
  | wait (keep : Nat)
  | waitAll
  | loadWord32 (space : Ptx.Space) (dst : String) (address : Address)
  | mma (d a : Registers4) (b : Registers2) (c : Registers4)

def CopySize (cache : CopyCache) (bytes : Nat) : Prop :=
  (bytes = 4 ∨ bytes = 8 ∨ bytes = 16) ∧ (cache = .cg → bytes = 16)
instance (cache bytes) : Decidable (CopySize cache bytes) := by unfold CopySize; infer_instance

def InstructionTyped (registers : Scalar.RegisterDeclarations) (parameters : ParameterDeclarations) (length : Nat) : Instr → Prop
  | .scalar i => Scalar.InstructionTyped registers parameters length i
  | .copy cache dst src bytes => CopySize cache bytes ∧
      AddressTyped (Scalar.integerDeclarations registers) dst ∧ AddressTyped (Scalar.integerDeclarations registers) src
  | .commit | .waitAll => True
  | .wait keep => keep < 8
  | .loadWord32 _ dst address => PackedRegister registers dst ∧ AddressTyped (Scalar.integerDeclarations registers) address
  | .mma d a b c => MmaTyped registers d a b c
instance (registers parameters length instruction) : Decidable (InstructionTyped registers parameters length instruction) := by
  cases instruction <;> simp only [InstructionTyped] <;> infer_instance

def ProgramTyped (sm : Nat) (registers : Scalar.RegisterDeclarations) (parameters : ParameterDeclarations) (code : List Instr) : Prop :=
  80 ≤ sm ∧ (registers.map Prod.fst).Nodup ∧ (parameters.map Prod.fst).Nodup ∧
  (∀ p ∈ parameters, SupportedWidth p.2) ∧ code ≠ [] ∧
  ∀ instruction ∈ code, InstructionTyped registers parameters code.length instruction
instance (sm registers parameters code) : Decidable (ProgramTyped sm registers parameters code) := by
  unfold ProgramTyped; infer_instance

structure CheckedProgram where
  targetSM : Nat
  registers : Scalar.RegisterDeclarations
  parameters : ParameterDeclarations
  code : List Instr
  valid : ProgramTyped targetSM registers parameters code

theorem CheckedProgram.instruction_typed (p : CheckedProgram) {i : Instr} (hi : i ∈ p.code) :
    InstructionTyped p.registers p.parameters p.code.length i := p.valid.2.2.2.2.2 i hi

/-- Placeholders are never executed by the extended interpreter. Keeping slots
preserves scalar branch PCs; this is not an erasure of asynchronous semantics. -/
def scalarSkeleton (code : List Instr) : List Scalar.Instr := code.map (fun i => match i with
  | .scalar instruction => instruction
  | _ => .integer .ret)

theorem scalarSkeleton_slot {code : List Instr} {pc : Nat} {i : Scalar.Instr} (hi : code[pc]? = some (.scalar i)) :
    (scalarSkeleton code)[pc]? = some i := by simp [scalarSkeleton,List.getElem?_map,hi]

end
end Ptx.Ampere
