import Ptx.Ampere.Syntax

/-! Fixed shared/shared m64n8k16 f32/f16/f16 form, scales +1/+1 and no
transpose. Other shapes, register-A and scaling modes are not erased. -/
namespace Ptx.Hopper.Wgmma
open Ptx.ISA
noncomputable section

/-- Opaque slots in a legacy component view. These tags introduce no memory
access, proxy fence, resource notification or completion edge. Rich WGMMA
events and ledger completion remain in the unified source candidate. -/
inductive SourceTag | fence | mma | commit | wait deriving Repr, DecidableEq

inductive Instr
  | fence
  | commit
  | wait (keep : Nat)
  | mma (d : Ampere.Registers4) (a b : String) (scaleD : Ptx.Operand)

def InstructionTyped (registers : Scalar.RegisterDeclarations) : Instr → Prop
  | .fence | .commit => True
  | .wait keep => keep < 8
  | .mma d a b scaleD => d.names.Nodup ∧
      (∀ name ∈ d.names, Scalar.FloatRegisterFits registers .f32 name) ∧
      RegisterFits (Scalar.integerDeclarations registers) 64 a ∧
      RegisterFits (Scalar.integerDeclarations registers) 64 b ∧
      OperandTyped (Scalar.integerDeclarations registers) 1 scaleD
instance (registers instruction) : Decidable (InstructionTyped registers instruction) := by
  cases instruction <;> simp only [InstructionTyped] <;> infer_instance

end
end Ptx.Hopper.Wgmma
