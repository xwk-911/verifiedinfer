import Ptx.Ampere.MmaPacked
import Ptx.Scalar.Syntax

/-! Fixed register arities for mma.sync.aligned.m16n8k16.row.col.f32.f16.f16.f32.
Register vectors are program data; outputs may alias accumulator inputs. -/
namespace Ptx.Ampere
open Ptx.ISA
noncomputable section

structure Registers2 where
  r0 : String
  r1 : String
  deriving Repr, DecidableEq
structure Registers4 where
  r0 : String
  r1 : String
  r2 : String
  r3 : String
  deriving Repr, DecidableEq
def Registers2.names (r : Registers2) : List String := [r.r0,r.r1]
def Registers4.names (r : Registers4) : List String := [r.r0,r.r1,r.r2,r.r3]
def Registers2.get (r : Registers2) (i : Fin 2) : String := if i.val = 0 then r.r0 else r.r1
def Registers4.get (r : Registers4) (i : Fin 4) : String :=
  if i.val = 0 then r.r0 else if i.val = 1 then r.r1 else if i.val = 2 then r.r2 else r.r3

inductive Word32
  | integer (value : Nat)
  | packed (value : PackedF16)
def Word32.encode : Word32 → List Symbolic.Byte
  | .integer value => (encodeU32 (wrap 32 value)).map Symbolic.Byte.bits
  | .packed value => value.encode
@[simp] theorem Word32.encode_size (value : Word32) : value.encode.length = 4 := by
  cases value <;> simp [encode]

def PackedRegister (registers : Scalar.RegisterDeclarations) (name : String) : Prop :=
  declarationLookup name registers = some (.integer .b32)
instance (registers name) : Decidable (PackedRegister registers name) := by unfold PackedRegister; infer_instance
def MmaTyped (registers : Scalar.RegisterDeclarations) (d a : Registers4) (b : Registers2) (c : Registers4) : Prop :=
  d.names.Nodup ∧ (∀ name ∈ d.names, Scalar.FloatRegisterFits registers .f32 name) ∧
  (∀ name ∈ a.names, PackedRegister registers name) ∧ (∀ name ∈ b.names, PackedRegister registers name) ∧
  ∀ name ∈ c.names, Scalar.FloatRegisterFits registers .f32 name
instance (registers d a b c) : Decidable (MmaTyped registers d a b c) := by unfold MmaTyped; infer_instance

end
end Ptx.Ampere
