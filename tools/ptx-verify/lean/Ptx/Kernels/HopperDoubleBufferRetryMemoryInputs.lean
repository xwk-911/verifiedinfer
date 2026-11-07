import Ptx.Kernels.HopperDoubleBufferRetryMemoryPhases

/-! Native RF closure for arbitrary completed retry candidates under the
existing full memory conditions. Mixed-size exclusion and per-byte eligibility
are derived. This does not construct a memory witness or arithmetic proof. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_native_not_tainted {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28) (tile : Nat) (ht : tile < tiles)
    (rf : Unified.ReadsFrom) (operand : Wgmma.OperandByte) :
    ¬Unified.Tainted Tma.localShared Access.globalDescriptor candidate (retryHistories family) dataCluster rf
      (retryNativeRead family tile operand) (retryNativeLocation family tile operand) := by
  rintro (⟨writer,hwriter,hrace⟩ | ⟨left,right,hl,hr,hrace⟩)
  · obtain ⟨value,hvalue⟩ := Option.isSome_iff_exists.mp hwriter
    rcases retry_native_writer_read_order family hw hc hd hb ht hvalue with hbefore | hafter
    · exact hrace.notBackward (Unified.byte_order_causal hrace.right hrace.left hbefore)
    · exact hrace.notForward (Unified.byte_order_causal hrace.left hrace.right hafter)
  · obtain ⟨lv,hlv⟩ := Option.isSome_iff_exists.mp hl
    obtain ⟨rv,hrv⟩ := Option.isSome_iff_exists.mp hr
    rcases retry_native_writers_comparable family (by omega) hw hc hd hb hlv hrv with rfl | hbefore | hafter
    · exact hrace.notStrong (Unified.write_self_strong hlv)
    · exact hrace.notForward (Unified.byte_order_causal hrace.left hrace.right hbefore)
    · exact hrace.notBackward (Unified.byte_order_causal hrace.right hrace.left hafter)

theorem retry_native_eligible {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28) (tile : Nat) (ht : tile < tiles)
    (rf : Unified.ReadsFrom) (operand : Wgmma.OperandByte) :
    Unified.Eligible Tma.localShared Access.globalDescriptor candidate (retryHistories family) dataCluster rf
      (retryNativeRead family tile operand) (retryNativeLocation family tile operand) :=
  ⟨candidate_no_mixed_size_race hb hw hc hd,retry_native_not_tainted family hw hc hd hb tile ht rf operand⟩

theorem retry_native_reads_from_current {tiles sourceInitial candidate initial rf co} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co (retryHistories family) dataCluster)
    (tile : Nat) (ht : tile < tiles) (operand : Wgmma.OperandByte) :
    rf (retryNativeRead family tile operand) (retryNativeLocation family tile operand) = some (retryNativeProducer family tile operand) := by
  obtain ⟨actual,hwrite⟩ := retry_native_producer_present family (by omega) hw hd tile ht operand
  have hread := retry_native_read_byte family hw tile ht operand
  apply Unified.phase_writer_source hm (retry_native_eligible family hw hc hd hb tile ht rf operand) hwrite hread
    (retry_native_byte_order family (by omega) hw hd tile ht operand)
  intro other value hother
  rcases retry_native_writer_phase family hw hc hd hb ht hother with he | hbefore | hafter
  · exact Or.inl he
  · exact Or.inr (Or.inl (Unified.byte_order_causal (.inr (by rw [hother]; rfl)) (.inr (by rw [hwrite]; rfl)) hbefore))
  · exact Or.inr (Or.inr (Unified.byte_order_causal (.inl (by rw [hread]; rfl)) (.inr (by rw [hother]; rfl)) hafter))

theorem retry_native_current_write_value {tiles sourceInitial candidate initial rf co} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co (retryHistories family) dataCluster)
    (tile : Nat) (ht : tile < tiles) (operand : Wgmma.OperandByte) :
    Unified.writeByte Tma.localShared Access.globalDescriptor candidate (retryNativeProducer family tile operand) (retryNativeLocation family tile operand) =
      some ((family.calls tile 0).operandBytes operand.index) :=
  Unified.write_read_value hm.agreement (retry_native_eligible family hw hc hd hb tile ht rf operand)
    (retry_native_read_byte family hw tile ht operand) (retry_native_reads_from_current family hw hc hd hb hm tile ht operand)

theorem retry_native_stale_source_rejected {tiles sourceInitial candidate initial rf co} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co (retryHistories family) dataCluster)
    (tile old : Nat) (ht : tile < tiles) (hold : old < tile) (hs : stage old = stage tile) (operand : Wgmma.OperandByte) :
    rf (retryNativeRead family tile operand) (retryNativeLocation family tile operand) ≠ some (retryNativeProducer family old operand) := by
  obtain ⟨current,hwCurrent⟩ := retry_native_producer_present family (by omega) hw hd tile ht operand
  obtain ⟨previous,hwPrevious⟩ := retry_native_producer_present family (by omega) hw hd old (by omega) operand
  have hbefore := retry_native_writes_order family hw hd hb old tile hold ht hs operand
  rw [retry_native_location_same_stage family old tile hs operand] at hwPrevious hbefore
  have hmix := candidate_no_mixed_size_race (histories := retryHistories family) (cluster := dataCluster) (rf := rf) hb hw hc hd
  have hco := (hm.coherence hmix).causality _ _ _ _ _ hwPrevious hwCurrent
    (Unified.byte_order_causal (.inr (by rw [hwPrevious]; rfl)) (.inr (by rw [hwCurrent]; rfl)) hbefore)
  have hp := Unified.byte_order_causal (rf := rf) (.inr (by rw [hwCurrent]; rfl))
    (.inl (by rw [retry_native_read_byte family hw tile ht operand]; rfl)) (retry_native_byte_order family (by omega) hw hd tile ht operand)
  intro hsource
  exact hm.noStale hmix _ _ _ _ _ hwCurrent (retry_native_read_byte family hw tile ht operand) hp (hsource ▸ hco)

theorem retry_native_future_source_rejected {tiles sourceInitial candidate initial rf co} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co (retryHistories family) dataCluster)
    (tile next : Nat) (hn : next < tiles) (hlt : tile < next) (hs : stage tile = stage next) (operand : Wgmma.OperandByte) :
    rf (retryNativeRead family tile operand) (retryNativeLocation family tile operand) ≠ some (retryNativeProducer family next operand) := by
  obtain ⟨future,hwrite⟩ := retry_native_producer_present family (by omega) hw hd next hn operand
  have hread := retry_native_read_byte family hw tile (by omega) operand
  rw [retry_native_location_same_stage family next tile hs.symm operand] at hwrite
  have hmix := candidate_no_mixed_size_race (histories := retryHistories family) (cluster := dataCluster) (rf := rf) hb hw hc hd
  exact hm.noFuture hmix _ _ _ _ _ hread hwrite
    (Unified.byte_order_causal (.inl (by rw [hread]; rfl)) (.inr (by rw [hwrite]; rfl))
      (retry_native_reuse_byte_order family hw hd hb tile next hlt hn hs operand))

theorem retry_repeated_initial_co_rejected {tiles sourceInitial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (left right : Nat) (hlt : left < right) (hr : right < tiles) (hs : stage left = stage right)
    (rf : Unified.ReadsFrom) (operand : Wgmma.OperandByte) :
    ¬Unified.Coherent Tma.localShared Access.globalDescriptor candidate (retryHistories family) dataCluster rf
      (Unified.InitialCo Tma.localShared Access.globalDescriptor candidate) := by
  intro hc
  obtain ⟨lv,hl⟩ := retry_native_producer_present family (by omega) hw hd left (by omega) operand
  obtain ⟨rv,hrv⟩ := retry_native_producer_present family (by omega) hw hd right hr operand
  rw [retry_native_location_same_stage family right left hs.symm operand] at hrv
  have horder := retry_native_writes_order family hw hd hb left right hlt hr hs operand
  have hco := hc.causality _ _ _ _ _ hl hrv
    (Unified.byte_order_causal (.inr (by rw [hl]; rfl)) (.inr (by rw [hrv]; rfl)) horder)
  cases hco.1

end
end Ptx.Kernels.HopperDoubleBuffer
