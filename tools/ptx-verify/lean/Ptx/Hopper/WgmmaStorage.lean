import Ptx.Hopper.WgmmaInputs

/-! Independent symbolic packed shared view: A at 0..2047, B at 2048..2303.
This view witnesses operand agreement for arbitrary real matrices; it does not
initialize a GPU launch's shared storage. A kernel must derive the same view
from actual writes/TMA, ordering, lifetime and admitted read-from choices. -/
namespace Ptx.Hopper.Wgmma
open Ptx.ISA
noncomputable section

def packedA : Nat := 68720001024
def packedB : Nat := 68720001152
theorem packed_a_profile : MatrixDescriptor.Packed packedA := by decide
theorem packed_b_profile : MatrixDescriptor.Packed packedB := by decide
theorem packed_a_base : (MatrixDescriptor.decode packedA).base = 0 := by decide
theorem packed_b_base : (MatrixDescriptor.decode packedB).base = 2048 := by decide

def MatrixStorage (cta : Dim3) (call : Call) (memory : Location → Symbolic.Byte)
    (a : ACoord → ℝ) (b : BCoord → ℝ) : Prop :=
  (∀ p byte, memory (operandLocation cta call (.a p byte)) = .realPart .f16 (a p) byte.val) ∧
  (∀ p byte, memory (operandLocation cta call (.b p byte)) = .realPart .f16 (b p) byte.val)
theorem input_values_of_memory {cta call memory a b} (h : InputAgreement cta call memory)
    (hm : MatrixStorage cta call memory a b) : InputValues call a b :=
  ⟨fun p byte => (h (.a p byte)).trans (hm.1 p byte),
   fun p byte => (h (.b p byte)).trans (hm.2 p byte)⟩
theorem input_values_unique {call a b a' b'} (h : InputValues call a b) (h' : InputValues call a' b') : a = a' ∧ b = b' := by
  constructor
  · funext p
    exact Option.some.inj ((input_a_decodes h p).symm.trans (input_a_decodes h' p))
  · funext p
    exact Option.some.inj ((input_b_decodes h p).symm.trans (input_b_decodes h' p))

def tileByte (a : ACoord → ℝ) (b : BCoord → ℝ) (address : Nat) : Symbolic.Byte :=
  if ha : address < 2048 then
    let p := aByteOwner ⟨address,ha⟩
    .realPart .f16 (a p.1) p.2.val
  else if hb : address < 2304 then
    let p := bByteOwner ⟨address-2048,by omega⟩
    .realPart .f16 (b p.1) p.2.val
  else .bits (byte 0)
def tileMemory (cta : Dim3) (a : ACoord → ℝ) (b : BCoord → ℝ) (location : Location) : Symbolic.Byte :=
  if location.space = .shared cta then tileByte a b location.address else .bits (byte 0)
theorem tile_byte_a (a : ACoord → ℝ) (b : BCoord → ℝ) (p : ACoord) (byte : Fin 2) :
    tileByte a b (aOffset (p,byte)).val = .realPart .f16 (a p) byte.val := by
  rw [tileByte,dite_eq_left (aOffset (p,byte)).isLt]
  change Symbolic.Byte.realPart .f16 (a (aByteOwner (aOffset (p,byte))).1) (aByteOwner (aOffset (p,byte))).2.val = _
  rw [a_owner_offset]
theorem tile_byte_b (a : ACoord → ℝ) (b : BCoord → ℝ) (p : BCoord) (byte : Fin 2) :
    tileByte a b (2048+(bOffset (p,byte)).val) = .realPart .f16 (b p) byte.val := by
  have h0 : ¬2048+(bOffset (p,byte)).val < 2048 := by omega
  have h1 : 2048+(bOffset (p,byte)).val < 2304 := by have := (bOffset (p,byte)).isLt; omega
  rw [tileByte,dite_eq_right h0,dite_eq_left h1]
  simp only [Nat.add_sub_cancel_left]
  change Symbolic.Byte.realPart .f16 (b (bByteOwner (bOffset (p,byte))).1) (bByteOwner (bOffset (p,byte))).2.val = _
  rw [b_owner_offset]
theorem packed_storage (cta : Dim3) (call : Call) (a : ACoord → ℝ) (b : BCoord → ℝ)
    (ha : call.a = packedA) (hb : call.b = packedB) : MatrixStorage cta call (tileMemory cta a b) a b := by
  constructor
  · intro p byte
    change tileMemory cta a b ⟨.shared cta,aAddress (MatrixDescriptor.decode call.a) p byte⟩ = _
    rw [ha,packed_a_address packed_a_profile,packed_a_base,Nat.zero_add]
    simpa only [tileMemory,ite_true] using tile_byte_a a b p byte
  · intro p byte
    change tileMemory cta a b ⟨.shared cta,bAddress (MatrixDescriptor.decode call.b) p byte⟩ = _
    rw [hb,packed_b_address packed_b_profile,packed_b_base]
    simpa only [tileMemory,ite_true] using tile_byte_b a b p byte
theorem packed_agreement (cta : Dim3) (call : Call) (a : ACoord → ℝ) (b : BCoord → ℝ)
    (ha : call.a = packedA) (hb : call.b = packedB)
    (hp : ∀ index, call.operandBytes index = payload a b index) : InputAgreement cta call (tileMemory cta a b) := by
  have hm := packed_storage cta call a b ha hb
  intro operand
  cases operand with
  | a p byte => exact (hp _).trans ((payload_a a b p byte).trans (hm.1 p byte).symm)
  | b p byte => exact (hp _).trans ((payload_b a b p byte).trans (hm.2 p byte).symm)

theorem packed_arenas_disjoint (p : ACoord) (q : BCoord) (x y : Fin 2) :
    aAddress (MatrixDescriptor.decode packedA) p x ≠ bAddress (MatrixDescriptor.decode packedB) q y := by
  rw [packed_a_address packed_a_profile,packed_b_address packed_b_profile,packed_a_base,packed_b_base]
  have := (aOffset (p,x)).isLt
  omega
theorem packed_a_bounds (p : ACoord) (x : Fin 2) : aAddress (MatrixDescriptor.decode packedA) p x < 2048 := by
  rw [packed_a_address packed_a_profile,packed_a_base,Nat.zero_add]
  exact (aOffset (p,x)).isLt
theorem packed_b_bounds (p : BCoord) (x : Fin 2) :
    2048 ≤ bAddress (MatrixDescriptor.decode packedB) p x ∧ bAddress (MatrixDescriptor.decode packedB) p x < 2304 := by
  rw [packed_b_address packed_b_profile,packed_b_base]
  have := (bOffset (p,x)).isLt
  omega

end
end Ptx.Hopper.Wgmma
