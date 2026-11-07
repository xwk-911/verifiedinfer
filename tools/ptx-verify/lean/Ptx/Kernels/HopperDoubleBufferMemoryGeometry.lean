import Ptx.Kernels.HopperDoubleBufferMemoryInventory

/-! Actual tensor-write regions and inversion at a native operand byte.
Slot identity is recovered from physical addresses; repeated writes in that
slot retain distinct source-copy identities. No unique-writer assumption is
made across K tiles. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem data_tensor_write_region {a b tiles id offset loc} (hb : tiles ≤ 2^28)
    (hl : Tma.writeLocation Tma.localShared (dataCompleteCandidate a b tiles).view id offset = some loc) :
    ∃ tile < tiles,
      (id = dataCopyAId a b tiles tile ∧ offset < 2048 ∧ loc = ⟨.shared .zero,aBase (stage tile)+offset⟩) ∨
      (id = dataCopyBId a b tiles tile ∧ offset < 256 ∧ loc = ⟨.shared .zero,bBase (stage tile)+offset⟩) := by
  cases hc : Tma.copyAt (dataCompleteCandidate a b tiles).view id with
  | none => simp only [Tma.writeLocation,hc,Option.bind_none] at hl; cases hl
  | some copy =>
    obtain ⟨tile,ht,hcopy⟩ := data_all_source_copies a b tiles hb id copy hc
    refine ⟨tile,ht,?_⟩
    rcases hcopy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [Tma.writeLocation,data_source_copy_a a b tiles tile ht hb] at hl
      change (if offset < 2048 then some ⟨.shared .zero,aBase (stage tile)+offset⟩ else none) = some loc at hl
      split at hl
      · exact Or.inl ⟨rfl,by assumption,(Option.some.inj hl).symm⟩
      · cases hl
    · rw [Tma.writeLocation,data_source_copy_b a b tiles tile ht hb] at hl
      change (if offset < 256 then some ⟨.shared .zero,bBase (stage tile)+offset⟩ else none) = some loc at hl
      split at hl
      · exact Or.inr ⟨rfl,by assumption,(Option.some.inj hl).symm⟩
      · cases hl

theorem a_region_unique (left right : Stage) (i j : Nat) (hi : i < 2048) (hj : j < 2048)
    (he : aBase left+i = aBase right+j) : left = right ∧ i = j := by
  have hl := left.isLt
  have hr := right.isLt
  simp only [aBase] at he
  exact ⟨Fin.ext (by omega),by omega⟩
theorem b_region_unique (left right : Stage) (i j : Nat) (hi : i < 256) (hj : j < 256)
    (he : bBase left+i = bBase right+j) : left = right ∧ i = j := by
  have hl := left.isLt
  have hr := right.isLt
  simp only [bBase] at he
  exact ⟨Fin.ext (by omega),by omega⟩
theorem a_b_regions_disjoint (left right : Stage) (i j : Nat) (hi : i < 2048) (hj : j < 256) :
    aBase left+i ≠ bBase right+j := by
  have hl := left.isLt
  have hr := right.isLt
  simp only [aBase,bBase]
  omega

theorem data_native_a_location (a b tiles tile) (p : Wgmma.ACoord) (byte : Fin 2) :
    dataNativeLocation a b tiles tile (.a p byte) = ⟨.shared .zero,aBase (stage tile)+(Wgmma.aOffset (p,byte)).val⟩ := by
  simp only [dataNativeLocation,Wgmma.operandLocation,data_call_a,a_operand_address]
theorem data_native_b_location (a b tiles tile) (p : Wgmma.BCoord) (byte : Fin 2) :
    dataNativeLocation a b tiles tile (.b p byte) = ⟨.shared .zero,bBase (stage tile)+(Wgmma.bOffset (p,byte)).val⟩ := by
  simp only [dataNativeLocation,Wgmma.operandLocation,data_call_b,b_operand_address]

theorem data_native_writer_case {a b tiles tile operand writer value} (hb : tiles ≤ 2^28)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      writer (dataNativeLocation a b tiles tile operand) = some value) :
    ∃ source < tiles, stage source = stage tile ∧ writer = dataNativeProducer a b tiles source operand := by
  have hs : (dataNativeLocation a b tiles tile operand).space = .shared .zero := by cases operand <;> rfl
  obtain ⟨id,offset,rfl,hl⟩ := data_shared_writer_is_tensor hs hw
  obtain ⟨source,ht,hregion⟩ := data_tensor_write_region hb hl
  refine ⟨source,ht,?_⟩
  cases operand with
  | a p byte =>
    rw [data_native_a_location] at hregion
    rcases hregion with ⟨rfl,ho,he⟩ | ⟨rfl,ho,he⟩
    · have ha := congrArg Location.address he
      have hx := a_region_unique (stage tile) (stage source) (Wgmma.aOffset (p,byte)).val offset (Wgmma.aOffset (p,byte)).isLt ho ha
      rw [← hx.2]
      exact ⟨hx.1.symm,rfl⟩
    · exact (a_b_regions_disjoint (stage tile) (stage source) _ _ (Wgmma.aOffset (p,byte)).isLt ho (congrArg Location.address he)).elim
  | b p byte =>
    rw [data_native_b_location] at hregion
    rcases hregion with ⟨rfl,ho,he⟩ | ⟨rfl,ho,he⟩
    · exact (a_b_regions_disjoint (stage source) (stage tile) _ _ ho (Wgmma.bOffset (p,byte)).isLt (congrArg Location.address he).symm).elim
    · have ha := congrArg Location.address he
      have hx := b_region_unique (stage tile) (stage source) (Wgmma.bOffset (p,byte)).val offset (Wgmma.bOffset (p,byte)).isLt ho ha
      rw [← hx.2]
      exact ⟨hx.1.symm,rfl⟩

theorem data_native_producer_write (a b tiles tile) (ht : tile < tiles) (hb : tiles ≤ 2^28) (operand : Wgmma.OperandByte) :
    Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataNativeProducer a b tiles tile operand) (dataNativeLocation a b tiles tile operand) =
      some ((dataIterationCall a b tiles tile 0).operandBytes operand.index) := by
  cases operand with
  | a p byte =>
    apply Access.tensor_write (descriptor := Access.globalDescriptor) (data_operand_a_transfer a b tiles tile 0 ht hb p byte).1
    exact (data_operand_a_transfer a b tiles tile 0 ht hb p byte).2
  | b p byte =>
    apply Access.tensor_write (descriptor := Access.globalDescriptor) (data_operand_b_transfer a b tiles tile 0 ht hb p byte).1
    exact (data_operand_b_transfer a b tiles tile 0 ht hb p byte).2

theorem same_slot_round_gap (left right : Nat) (hl : left < right) (hs : stage left = stage right) : left+2 ≤ right := by
  have he := congrArg Fin.val hs
  simp only [stage] at he
  omega

end
end Ptx.Kernels.HopperDoubleBuffer
