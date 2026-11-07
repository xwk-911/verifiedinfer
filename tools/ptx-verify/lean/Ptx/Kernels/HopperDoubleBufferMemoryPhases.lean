import Ptx.Kernels.HopperDoubleBufferMemoryGeometry

/-! Per-byte ordering of all repeated writers around each native read. Older
same-slot writers precede the current producer; later writers follow native
completion. This does not construct or assume an RF/co witness. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem data_native_same_slot_location (a b tiles left right) (hs : stage left = stage right) (operand : Wgmma.OperandByte) :
    dataNativeLocation a b tiles left operand = dataNativeLocation a b tiles right operand := by
  cases operand <;> simp only [data_native_a_location,data_native_b_location,hs]

theorem data_native_writes_order (a b tiles left right) (hr : right < tiles) (hl : left < right)
    (hs : stage left = stage right) (hb : tiles ≤ 2^28) (operand : Wgmma.OperandByte) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster (dataNativeLocation a b tiles left operand)
      (dataNativeProducer a b tiles left operand) (dataNativeProducer a b tiles right operand) :=
  .trans (data_native_byte_order a b tiles left (by omega) hb operand)
    (data_native_reuse_byte_order a b tiles left right hr (same_slot_round_gap left right hl hs) hs.symm hb operand)

theorem data_native_read_byte (a b tiles tile) (ht : tile < tiles) (operand : Wgmma.OperandByte) :
    Unified.readByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataNativeRead a b tiles tile operand) (dataNativeLocation a b tiles tile operand) =
      some ((dataIterationCall a b tiles tile 0).operandBytes operand.index) :=
  Unified.native_read_byte (data_collective_representative a b tiles tile ht)

theorem data_native_writer_phase {a b tiles tile operand writer value} (ht : tile < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      writer (dataNativeLocation a b tiles tile operand) = some value) :
    writer = dataNativeProducer a b tiles tile operand ∨
      Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
        (dataHistories a b tiles) dataCluster (dataNativeLocation a b tiles tile operand)
        writer (dataNativeProducer a b tiles tile operand) ∨
      Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
        (dataHistories a b tiles) dataCluster (dataNativeLocation a b tiles tile operand)
        (dataNativeRead a b tiles tile operand) writer := by
  obtain ⟨source,hs,hslot,rfl⟩ := data_native_writer_case hb hw
  rcases lt_trichotomy source tile with hold | rfl | hnext
  · right; left
    have ho := data_native_writes_order a b tiles source tile ht hold hslot hb operand
    rwa [data_native_same_slot_location a b tiles source tile hslot operand] at ho
  · exact Or.inl rfl
  · right; right
    exact data_native_reuse_byte_order a b tiles tile source hs (same_slot_round_gap tile source hnext hslot.symm) hslot hb operand

theorem data_native_writer_read_order {a b tiles tile operand writer value} (ht : tile < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      writer (dataNativeLocation a b tiles tile operand) = some value) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
        (dataHistories a b tiles) dataCluster (dataNativeLocation a b tiles tile operand)
        writer (dataNativeRead a b tiles tile operand) ∨
      Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
        (dataHistories a b tiles) dataCluster (dataNativeLocation a b tiles tile operand)
        (dataNativeRead a b tiles tile operand) writer := by
  rcases data_native_writer_phase ht hb hw with rfl | hold | hnext
  · exact Or.inl (data_native_byte_order a b tiles tile ht hb operand)
  · exact Or.inl (.trans hold (data_native_byte_order a b tiles tile ht hb operand))
  · exact Or.inr hnext

theorem data_native_writers_comparable {a b tiles tile operand left right lv rv} (hb : tiles ≤ 2^28)
    (hl : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      left (dataNativeLocation a b tiles tile operand) = some lv)
    (hr : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      right (dataNativeLocation a b tiles tile operand) = some rv) :
    left = right ∨
      Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
        (dataHistories a b tiles) dataCluster (dataNativeLocation a b tiles tile operand) left right ∨
      Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
        (dataHistories a b tiles) dataCluster (dataNativeLocation a b tiles tile operand) right left := by
  obtain ⟨lt,hlt,hls,rfl⟩ := data_native_writer_case hb hl
  obtain ⟨rt,hrt,hrs,rfl⟩ := data_native_writer_case hb hr
  have hslot : stage lt = stage rt := hls.trans hrs.symm
  rcases lt_trichotomy lt rt with hold | rfl | hnext
  · right; left
    have ho := data_native_writes_order a b tiles lt rt hrt hold hslot hb operand
    rwa [data_native_same_slot_location a b tiles lt tile hls operand] at ho
  · exact Or.inl rfl
  · right; right
    have ho := data_native_writes_order a b tiles rt lt hlt hnext hslot.symm hb operand
    rwa [data_native_same_slot_location a b tiles rt tile hrs operand] at ho

end
end Ptx.Kernels.HopperDoubleBuffer
