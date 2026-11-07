import Ptx.Kernels.HopperDoubleBufferMemoryPhases

/-! Repeated native reads are untainted at their byte, with arbitrary RF.
Given the full memory conditions and no mixed-size race, the existing phase
writer rule forces RF to the current actual TMA producer. These hypotheses
are explicit: this is not an independent complete memory-existence witness. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem data_native_not_tainted (a b tiles tile) (ht : tile < tiles) (hb : tiles ≤ 2^28)
    (rf : Unified.ReadsFrom) (operand : Wgmma.OperandByte) :
    ¬Unified.Tainted Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster rf (dataNativeRead a b tiles tile operand) (dataNativeLocation a b tiles tile operand) := by
  rintro (⟨writer,hw,hrace⟩ | ⟨left,right,hl,hr,hrace⟩)
  · obtain ⟨value,hvalue⟩ := Option.isSome_iff_exists.mp hw
    rcases data_native_writer_read_order ht hb hvalue with hbefore | hafter
    · exact hrace.notBackward (Unified.byte_order_causal hrace.right hrace.left hbefore)
    · exact hrace.notForward (Unified.byte_order_causal hrace.left hrace.right hafter)
  · obtain ⟨lv,hlv⟩ := Option.isSome_iff_exists.mp hl
    obtain ⟨rv,hrv⟩ := Option.isSome_iff_exists.mp hr
    rcases data_native_writers_comparable hb hlv hrv with rfl | hbefore | hafter
    · exact hrace.notStrong (Unified.write_self_strong hlv)
    · exact hrace.notForward (Unified.byte_order_causal hrace.left hrace.right hbefore)
    · exact hrace.notBackward (Unified.byte_order_causal hrace.right hrace.left hafter)

theorem data_native_eligible {a b tiles tile rf} (ht : tile < tiles) (hb : tiles ≤ 2^28)
    (hm : ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster rf) (operand : Wgmma.OperandByte) :
    Unified.Eligible Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster rf (dataNativeRead a b tiles tile operand) (dataNativeLocation a b tiles tile operand) :=
  ⟨hm,data_native_not_tainted a b tiles tile ht hb rf operand⟩

theorem data_native_reads_from_current {a b tiles tile initial rf co} (ht : tile < tiles) (hb : tiles ≤ 2^28)
    (hc : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      initial rf co (dataHistories a b tiles) dataCluster)
    (hm : ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster rf) (operand : Wgmma.OperandByte) :
    rf (dataNativeRead a b tiles tile operand) (dataNativeLocation a b tiles tile operand) =
      some (dataNativeProducer a b tiles tile operand) := by
  have hw := data_native_producer_write a b tiles tile ht hb operand
  have hr := data_native_read_byte a b tiles tile ht operand
  apply Unified.phase_writer_source hc (data_native_eligible ht hb hm operand) hw hr
    (data_native_byte_order a b tiles tile ht hb operand)
  intro other value hother
  rcases data_native_writer_phase ht hb hother with he | hbefore | hafter
  · exact Or.inl he
  · exact Or.inr (Or.inl (Unified.byte_order_causal (.inr (by rw [hother]; rfl)) (.inr (by rw [hw]; rfl)) hbefore))
  · exact Or.inr (Or.inr (Unified.byte_order_causal (.inl (by rw [hr]; rfl)) (.inr (by rw [hother]; rfl)) hafter))

theorem data_native_stale_source_rejected {a b tiles tile old initial rf co} (ht : tile < tiles)
    (hold : old < tile) (hs : stage old = stage tile) (hb : tiles ≤ 2^28)
    (hc : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      initial rf co (dataHistories a b tiles) dataCluster)
    (hm : ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster rf) (operand : Wgmma.OperandByte) :
    rf (dataNativeRead a b tiles tile operand) (dataNativeLocation a b tiles tile operand) ≠
      some (dataNativeProducer a b tiles old operand) := by
  have hw := data_native_producer_write a b tiles tile ht hb operand
  have ho := data_native_producer_write a b tiles old (by omega) hb operand
  have hr := data_native_read_byte a b tiles tile ht operand
  have hbefore := data_native_writes_order a b tiles old tile ht hold hs hb operand
  rw [data_native_same_slot_location a b tiles old tile hs operand] at ho hbefore
  have hco := (hc.coherence hm).causality _ _ _ _ _ ho hw
    (Unified.byte_order_causal (.inr (by rw [ho]; rfl)) (.inr (by rw [hw]; rfl)) hbefore)
  have hp := Unified.byte_order_causal (rf := rf) (.inr (by rw [hw]; rfl)) (.inl (by rw [hr]; rfl))
    (data_native_byte_order a b tiles tile ht hb operand)
  intro hsource
  exact hc.noStale hm _ _ _ _ _ hw hr hp (hsource ▸ hco)

theorem data_native_future_source_rejected {a b tiles tile next initial rf co} (hn : next < tiles)
    (hle : tile+2 ≤ next) (hs : stage next = stage tile) (hb : tiles ≤ 2^28)
    (hc : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      initial rf co (dataHistories a b tiles) dataCluster)
    (hm : ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster rf) (operand : Wgmma.OperandByte) :
    rf (dataNativeRead a b tiles tile operand) (dataNativeLocation a b tiles tile operand) ≠
      some (dataNativeProducer a b tiles next operand) := by
  have hw := data_native_producer_write a b tiles next hn hb operand
  have hr := data_native_read_byte a b tiles tile (by omega) operand
  rw [data_native_same_slot_location a b tiles next tile hs operand] at hw
  exact hc.noFuture hm _ _ _ _ _ hr hw
    (Unified.byte_order_causal (.inl (by rw [hr]; rfl)) (.inr (by rw [hw]; rfl))
      (data_native_reuse_byte_order a b tiles tile next hn hle hs hb operand))

theorem data_repeated_initial_co_rejected (a b tiles left right) (hr : right < tiles) (hl : left < right)
    (hs : stage left = stage right) (hb : tiles ≤ 2^28) (rf : Unified.ReadsFrom) (operand : Wgmma.OperandByte) :
    ¬Unified.Coherent Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster rf
      (Unified.InitialCo Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)) := by
  intro hc
  have hw := data_native_producer_write a b tiles left (by omega) hb operand
  have hn := data_native_producer_write a b tiles right hr hb operand
  rw [data_native_same_slot_location a b tiles right left hs.symm operand] at hn
  have horder := data_native_writes_order a b tiles left right hr hl hs hb operand
  have hco := hc.causality _ _ _ _ _ hw hn
    (Unified.byte_order_causal (.inr (by rw [hw]; rfl)) (.inr (by rw [hn]; rfl)) horder)
  cases hco.1

end
end Ptx.Kernels.HopperDoubleBuffer
