import Ptx.Kernels.HopperDoubleBufferRetryNativeCompletion
import Ptx.Hopper.UnifiedOrder

/-! Reused-byte order through the actual producer lane's native wait and its
subsequent TMA issues. No wait is inserted into the kernel. These byte edges
do not prove all-lane CTA/native control legality, RF/co or full admission. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_same_slot_gap {left right : Nat} (hlt : left < right) (hs : stage left = stage right) : left+2 ≤ right := by
  have hh := congrArg Fin.val hs
  dsimp [stage] at hh
  omega

theorem retry_native_location_same_stage {tiles candidate} (family : ReplySourceFamily tiles candidate) (left right : Nat)
    (hs : stage left = stage right) (operand : Wgmma.OperandByte) :
    retryNativeLocation family left operand = retryNativeLocation family right operand := by
  cases operand with
  | a p part => simp only [retryNativeLocation,ReplySourceFamily.calls,reply_operand_a_location,hs]
  | b p part => simp only [retryNativeLocation,ReplySourceFamily.calls,reply_operand_b_location,hs]

theorem retry_native_wait_before_later_copy_serial {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile next : Nat)
    (hg : tile+2 ≤ next) :
    (family.nativeWaitId tile 0).serial < (family.copyAId next).issue.serial ∧
      (family.nativeWaitId tile 0).serial < (family.copyBId next).issue.serial := by
  have hu : (family.nativeWaitId tile 0).serial < replyTileStart tiles 0 (family.replies 0) (family.schedules 0) (tile+1) := by
    simp only [ReplySourceFamily.nativeWaitId,replyNativeWaitId,reply_tile_start_succ]
    omega
  cases next with
  | zero => omega
  | succ next =>
    have hm := (reply_tile_start_strict_mono tiles 0 (family.replies 0) (family.schedules 0)).monotone (show tile+1 ≤ next by omega)
    simp only [ReplySourceFamily.copyAId,ReplySourceFamily.copyBId,replyCopyAId,replyCopyBId,replyPrefetchId]
    omega

theorem retry_native_wait_before_copy_a {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hb : tiles ≤ 2^28)
    (tile next : Nat) (hg : tile+2 ≤ next) (hn : next < tiles) :
    Access.GenericAfter candidate.view (family.nativeWaitId tile 0) (family.copyAId next).issue := by
  apply Access.generic_program_after
  refine ⟨?_,?_,?_,(retry_native_wait_before_later_copy_serial family tile next hg).1⟩
  · simp only [Hopper.Candidate.Present,Unified.view_eventAt,family_native_wait_at family hw hb tile (by omega) 0,
      Option.map_some,Option.isSome_some]
  · have he := Tma.copyAt_iff.mp (family_copy_a_at family hw next hn)
    simp only [Hopper.Candidate.Present,he,Option.isSome_some]
  · cases next <;> rfl

theorem retry_native_wait_before_copy_b {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hb : tiles ≤ 2^28)
    (tile next : Nat) (hg : tile+2 ≤ next) (hn : next < tiles) :
    Access.GenericAfter candidate.view (family.nativeWaitId tile 0) (family.copyBId next).issue := by
  apply Access.generic_program_after
  refine ⟨?_,?_,?_,(retry_native_wait_before_later_copy_serial family tile next hg).2⟩
  · simp only [Hopper.Candidate.Present,Unified.view_eventAt,family_native_wait_at family hw hb tile (by omega) 0,
      Option.map_some,Option.isSome_some]
  · have he := Tma.copyAt_iff.mp (family_copy_b_at family hw next hn)
    simp only [Hopper.Candidate.Present,he,Option.isSome_some]
  · cases next <;> rfl

theorem retry_native_reuse {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (tile next : Nat) (hlt : tile < next) (hn : next < tiles) (hs : stage tile = stage next) (operand : Wgmma.OperandByte) :
    Unified.NativeReuse Tma.localShared candidate (retryNativeLocation family tile operand)
      (retryNativeRead family tile operand) (retryNativeProducer family next operand) := by
  have hg := retry_same_slot_gap hlt hs
  cases operand with
  | a p part =>
    have hl := retry_operand_a_transfer family hw hd next hn 0 p part
    have he := retry_native_location_same_stage family tile next hs (.a p part)
    simp only [retryNativeLocation] at he
    rw [← he] at hl
    exact ⟨family.nativeWaitId tile 0,retry_native_completed family hw hb tile (by omega) 0,
      retry_native_wait_before_copy_a family hw hb tile next hg hn,hl,family.marks tile 0,family.calls tile 0,
      Unified.collective_representative (familyCollective family hw tile (by omega)),rfl⟩
  | b p part =>
    have hl := retry_operand_b_transfer family hw hd next hn 0 p part
    have he := retry_native_location_same_stage family tile next hs (.b p part)
    simp only [retryNativeLocation] at he
    rw [← he] at hl
    exact ⟨family.nativeWaitId tile 0,retry_native_completed family hw hb tile (by omega) 0,
      retry_native_wait_before_copy_b family hw hb tile next hg hn,hl,family.marks tile 0,family.calls tile 0,
      Unified.collective_representative (familyCollective family hw tile (by omega)),rfl⟩

theorem retry_native_reuse_byte_order {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (tile next : Nat) (hlt : tile < next) (hn : next < tiles) (hs : stage tile = stage next) (operand : Wgmma.OperandByte) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor candidate (retryHistories family) dataCluster
      (retryNativeLocation family tile operand) (retryNativeRead family tile operand) (retryNativeProducer family next operand) :=
  Unified.native_reuse_byte_order (retry_native_reuse family hw hd hb tile next hlt hn hs operand)

theorem retry_mbarrier_is_not_native_completion {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (tile : Nat) (ht : tile < tiles)
    (lane : Wgmma.Lane) (issue : Ptx.Event.EventId) : ¬Unified.WgmmaCompletedAt candidate issue (family.waitId tile lane) := by
  intro hc
  obtain ⟨mark,groups,keep,before,after,query,he,_⟩ := Unified.completed_has_actual_wait hc
  rw [family_wait_at family hw tile ht lane] at he
  cases he

end
end Ptx.Kernels.HopperDoubleBuffer
