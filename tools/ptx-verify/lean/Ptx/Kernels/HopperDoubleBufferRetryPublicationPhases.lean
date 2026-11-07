import Ptx.Kernels.HopperDoubleBufferRetryPublicationInterface

/-! Per-byte writer phase order parameterized by proved native publication.
The interface is derived from admitted arbitrary histories at the public entry. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem publication_native_writes_order {tiles initial candidate} {histories : Location → List Tma.Entry} (family : ReplySourceFamily tiles candidate) (hpub : NativePublicationFacts family histories)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (left right : Nat) (hlt : left < right) (hr : right < tiles) (hs : stage left = stage right) (operand : Wgmma.OperandByte) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor candidate histories dataCluster
      (retryNativeLocation family left operand) (retryNativeProducer family left operand) (retryNativeProducer family right operand) :=
  .trans (hpub left (by omega) operand)
    (history_native_reuse_byte_order family hw hd hb left right hlt hr hs operand)

theorem publication_native_writer_phase {tiles initial candidate} {histories : Location → List Tma.Entry} (family : ReplySourceFamily tiles candidate) (hpub : NativePublicationFacts family histories)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28) {tile operand writer value} (ht : tile < tiles)
    (he : Unified.writeByte Tma.localShared Access.globalDescriptor candidate writer (retryNativeLocation family tile operand) = some value) :
    writer = retryNativeProducer family tile operand ∨
      Unified.ByteOrder Tma.localShared Access.globalDescriptor candidate histories dataCluster
        (retryNativeLocation family tile operand) writer (retryNativeProducer family tile operand) ∨
      Unified.ByteOrder Tma.localShared Access.globalDescriptor candidate histories dataCluster
        (retryNativeLocation family tile operand) (retryNativeRead family tile operand) writer := by
  obtain ⟨source,hp,hslot,rfl⟩ := retry_native_writer_case family (by omega) hw hc hd hb he
  rcases lt_trichotomy source tile with hold | rfl | hnext
  · right; left
    have ho := publication_native_writes_order family hpub hw hd hb source tile hold ht hslot operand
    rwa [retry_native_location_same_stage family source tile hslot operand] at ho
  · exact Or.inl rfl
  · right; right
    exact history_native_reuse_byte_order family hw hd hb tile source hnext hp hslot.symm operand

theorem publication_native_writer_read_order {tiles initial candidate} {histories : Location → List Tma.Entry} (family : ReplySourceFamily tiles candidate) (hpub : NativePublicationFacts family histories)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28) {tile operand writer value} (ht : tile < tiles)
    (he : Unified.writeByte Tma.localShared Access.globalDescriptor candidate writer (retryNativeLocation family tile operand) = some value) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor candidate histories dataCluster
      (retryNativeLocation family tile operand) writer (retryNativeRead family tile operand) ∨
    Unified.ByteOrder Tma.localShared Access.globalDescriptor candidate histories dataCluster
      (retryNativeLocation family tile operand) (retryNativeRead family tile operand) writer := by
  rcases publication_native_writer_phase family hpub hw hc hd hb ht he with rfl | hold | hnext
  · exact Or.inl (hpub tile ht operand)
  · exact Or.inl (.trans hold (hpub tile ht operand))
  · exact Or.inr hnext

theorem publication_native_writers_comparable {tiles initial candidate} {histories : Location → List Tma.Entry} (family : ReplySourceFamily tiles candidate) (hpub : NativePublicationFacts family histories) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28) {tile operand left right lv rv}
    (hl : Unified.writeByte Tma.localShared Access.globalDescriptor candidate left (retryNativeLocation family tile operand) = some lv)
    (hr : Unified.writeByte Tma.localShared Access.globalDescriptor candidate right (retryNativeLocation family tile operand) = some rv) :
    left = right ∨
      Unified.ByteOrder Tma.localShared Access.globalDescriptor candidate histories dataCluster (retryNativeLocation family tile operand) left right ∨
      Unified.ByteOrder Tma.localShared Access.globalDescriptor candidate histories dataCluster (retryNativeLocation family tile operand) right left := by
  obtain ⟨lt,hlt,hls,rfl⟩ := retry_native_writer_case family ht hw hc hd hb hl
  obtain ⟨rt,hrt,hrs,rfl⟩ := retry_native_writer_case family ht hw hc hd hb hr
  have hslot : stage lt = stage rt := hls.trans hrs.symm
  rcases lt_trichotomy lt rt with hold | rfl | hnext
  · right; left
    have ho := publication_native_writes_order family hpub hw hd hb lt rt hold hrt hslot operand
    rwa [retry_native_location_same_stage family lt tile hls operand] at ho
  · exact Or.inl rfl
  · right; right
    have ho := publication_native_writes_order family hpub hw hd hb rt lt hnext hlt hslot.symm operand
    rwa [retry_native_location_same_stage family rt tile hrs operand] at ho

end
end Ptx.Kernels.HopperDoubleBuffer
