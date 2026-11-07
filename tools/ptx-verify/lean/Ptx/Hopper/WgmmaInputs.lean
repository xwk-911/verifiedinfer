import Ptx.Hopper.WgmmaDescriptor
import Ptx.Hopper.WgmmaThread

/-! Source-captured logical operand byte replies and their descriptor-derived
shared locations. One collective operation has 2048 A and 256 B byte reads.
They use the async proxy and one warpgroup operation identity, not 128 distinct
memory agents. Uniform/source participation and full combined memory admission
must be established separately before using a representative lane's inventory.
These definitions do not publish/initialize shared memory or admit an RF map.
-/
namespace Ptx.Hopper.Wgmma
open Ptx.ISA
noncomputable section

inductive OperandByte
  | a (coord : ACoord) (byte : Fin 2)
  | b (coord : BCoord) (byte : Fin 2)
  deriving Repr, DecidableEq
def OperandByte.index : OperandByte → Nat
  | .a p byte => 32*p.1.val+2*p.2.val+byte.val
  | .b p byte => 2048+16*p.1.val+2*p.2.val+byte.val
theorem operand_index_bounded (operand : OperandByte) : operand.index < 2304 := by
  cases operand with
  | a p byte => dsimp [OperandByte.index]; have := p.1.isLt; have := p.2.isLt; have := byte.isLt; omega
  | b p byte => dsimp [OperandByte.index]; have := p.1.isLt; have := p.2.isLt; have := byte.isLt; omega
theorem operand_index_covered (index : Fin 2304) : ∃ operand : OperandByte, operand.index = index.val := by
  by_cases ha : index.val < 2048
  · refine ⟨.a (⟨index.val/32,by omega⟩,⟨(index.val/2)%16,Nat.mod_lt _ (by decide)⟩)
      ⟨index.val%2,Nat.mod_lt _ (by decide)⟩,?_⟩
    dsimp [OperandByte.index]
    omega
  · have hb := index.isLt
    refine ⟨.b (⟨(index.val-2048)/16,by omega⟩,⟨((index.val-2048)/2)%8,Nat.mod_lt _ (by decide)⟩)
      ⟨(index.val-2048)%2,Nat.mod_lt _ (by decide)⟩,?_⟩
    dsimp [OperandByte.index]
    omega
theorem operand_index_unique : Function.Injective OperandByte.index := by
  intro left right he
  cases left with
  | a p byte =>
    cases right with
    | a q other =>
      have hp := p.1.isLt; have hk := p.2.isLt; have hb := byte.isLt
      have hq := q.1.isLt; have hj := q.2.isLt; have hc := other.isLt
      have hrow : p.1 = q.1 := Fin.ext (by dsimp [OperandByte.index] at he; omega)
      have hcol : p.2 = q.2 := Fin.ext (by dsimp [OperandByte.index] at he; omega)
      have hbyte : byte = other := Fin.ext (by dsimp [OperandByte.index] at he; omega)
      cases Prod.ext hrow hcol
      cases hbyte
      rfl
    | b q other => dsimp [OperandByte.index] at he; have := p.1.isLt; have := p.2.isLt; have := byte.isLt; omega
  | b p byte =>
    cases right with
    | a q other => dsimp [OperandByte.index] at he; have := q.1.isLt; have := q.2.isLt; have := other.isLt; omega
    | b q other =>
      have hp := p.1.isLt; have hk := p.2.isLt; have hb := byte.isLt
      have hq := q.1.isLt; have hj := q.2.isLt; have hc := other.isLt
      have hrow : p.1 = q.1 := Fin.ext (by dsimp [OperandByte.index] at he; omega)
      have hcol : p.2 = q.2 := Fin.ext (by dsimp [OperandByte.index] at he; omega)
      have hbyte : byte = other := Fin.ext (by dsimp [OperandByte.index] at he; omega)
      cases Prod.ext hrow hcol
      cases hbyte
      rfl

structure OperationId where
  cta : Dim3
  warpgroup : Nat
  ordinal : Nat
  pc : Nat
  deriving Repr, DecidableEq
structure ReadId where
  operation : OperationId
  operand : OperandByte
  deriving Repr, DecidableEq
def operationId (cta : Dim3) (mark : Mark) (call : Call) : OperationId :=
  ⟨cta,mark.warpgroup,call.ordinal,mark.pc⟩
def readProxy : Tma.Proxy := .async
def operandLocation (cta : Dim3) (call : Call) : OperandByte → Location
  | .a p byte => ⟨.shared cta,aAddress (MatrixDescriptor.decode call.a) p byte⟩
  | .b p byte => ⟨.shared cta,bAddress (MatrixDescriptor.decode call.b) p byte⟩
def operandKind (cta : Dim3) (call : Call) (operand : OperandByte) : Scalar.Kind :=
  .read (operandLocation cta call operand) [call.operandBytes operand.index]
def InputAgreement (cta : Dim3) (call : Call) (memory : Location → Symbolic.Byte) : Prop :=
  ∀ operand, call.operandBytes operand.index = memory (operandLocation cta call operand)
def InputValues (call : Call) (a : ACoord → ℝ) (b : BCoord → ℝ) : Prop :=
  (∀ p byte, call.operandBytes (OperandByte.a p byte).index = .realPart .f16 (a p) byte.val) ∧
  (∀ p byte, call.operandBytes (OperandByte.b p byte).index = .realPart .f16 (b p) byte.val)
def aBytes (call : Call) (p : ACoord) : List Symbolic.Byte :=
  [call.operandBytes (OperandByte.a p 0).index,call.operandBytes (OperandByte.a p 1).index]
def bBytes (call : Call) (p : BCoord) : List Symbolic.Byte :=
  [call.operandBytes (OperandByte.b p 0).index,call.operandBytes (OperandByte.b p 1).index]
theorem input_a_decodes {call a b} (h : InputValues call a b) (p : ACoord) :
    Symbolic.decode .f16 (aBytes call p) = some (a p) := by
  have he : aBytes call p = Symbolic.encode .f16 (a p) := by
    simp only [aBytes,h.1 p 0,h.1 p 1,Symbolic.encode,Symbolic.Format.bytes]
    rfl
  rw [he,Symbolic.decode_encode]
theorem input_b_decodes {call a b} (h : InputValues call a b) (p : BCoord) :
    Symbolic.decode .f16 (bBytes call p) = some (b p) := by
  have he : bBytes call p = Symbolic.encode .f16 (b p) := by
    simp only [bBytes,h.2 p 0,h.2 p 1,Symbolic.encode,Symbolic.Format.bytes]
    rfl
  rw [he,Symbolic.decode_encode]

def payload (a : ACoord → ℝ) (b : BCoord → ℝ) (index : Nat) : Symbolic.Byte :=
  if ha : index < 2048 then
    .realPart .f16 (a (⟨index/32,by omega⟩,⟨(index/2)%16,Nat.mod_lt _ (by decide)⟩)) (index%2)
  else if hb : index < 2304 then
    .realPart .f16 (b (⟨(index-2048)/16,by omega⟩,⟨((index-2048)/2)%8,Nat.mod_lt _ (by decide)⟩)) ((index-2048)%2)
  else .bits (byte 0)
theorem payload_a (a : ACoord → ℝ) (b : BCoord → ℝ) (p : ACoord) (byte : Fin 2) :
    payload a b (OperandByte.a p byte).index = .realPart .f16 (a p) byte.val := by
  have hr := p.1.isLt; have hc := p.2.isLt; have hb := byte.isLt
  have h : (OperandByte.a p byte).index < 2048 := by dsimp [OperandByte.index]; omega
  rw [payload,dite_eq_left h]
  have hrow : (OperandByte.a p byte).index/32 = p.1.val := by dsimp [OperandByte.index]; omega
  have hcol : ((OperandByte.a p byte).index/2)%16 = p.2.val := by dsimp [OperandByte.index]; omega
  have hbyte : (OperandByte.a p byte).index%2 = byte.val := by dsimp [OperandByte.index]; omega
  simp only [hrow,hcol,hbyte,Fin.eta,Prod.mk.eta]
theorem payload_b (a : ACoord → ℝ) (b : BCoord → ℝ) (p : BCoord) (byte : Fin 2) :
    payload a b (OperandByte.b p byte).index = .realPart .f16 (b p) byte.val := by
  have hr := p.1.isLt; have hc := p.2.isLt; have hb := byte.isLt
  have h0 : ¬(OperandByte.b p byte).index < 2048 := by dsimp [OperandByte.index]; omega
  have h : (OperandByte.b p byte).index < 2304 := operand_index_bounded _
  rw [payload,dite_eq_right h0,dite_eq_left h]
  have hrow : ((OperandByte.b p byte).index-2048)/16 = p.1.val := by dsimp [OperandByte.index]; omega
  have hcol : (((OperandByte.b p byte).index-2048)/2)%8 = p.2.val := by dsimp [OperandByte.index]; omega
  have hbyte : ((OperandByte.b p byte).index-2048)%2 = byte.val := by dsimp [OperandByte.index]; omega
  simp only [hrow,hcol,hbyte,Fin.eta,Prod.mk.eta]
theorem payload_input_values (call : Call) (a : ACoord → ℝ) (b : BCoord → ℝ) :
    InputValues {call with operandBytes := payload a b} a b := ⟨payload_a a b,payload_b a b⟩
theorem source_operand_query (ctx s oracle d pa pb useD input) (operand : OperandByte) :
    (makeCall ctx s oracle d pa pb useD input).operandBytes operand.index = oracle.operands s.base.scalar.core.queries operand.index := rfl
theorem source_operand_kind (ctx s oracle d pa pb useD input operand) :
    operandKind ctx.id.cta (makeCall ctx s oracle d pa pb useD input) operand =
      .read (operandLocation ctx.id.cta (makeCall ctx s oracle d pa pb useD input) operand)
        [oracle.operands s.base.scalar.core.queries operand.index] := rfl

end
end Ptx.Hopper.Wgmma
