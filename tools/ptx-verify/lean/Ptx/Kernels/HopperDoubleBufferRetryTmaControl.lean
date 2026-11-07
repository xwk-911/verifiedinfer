import Ptx.Kernels.HopperDoubleBufferRetryResourceRanks
import Ptx.Kernels.HopperDoubleBufferRetryMemoryGeometry

/-! TMA control ranks for actual arbitrary-retry copies. Notification ranks
are indexed by the uniquely recovered source tile/operand role and occur
after failed waits. Default ranks for absent copies cannot justify actual
implicit edges. This is control-only, not byte visibility or full admission. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def retryNoticeClock {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (operandB : Bool) : Nat :=
  retryUnit family*(1024*(7+10*tile)+(if operandB then 896 else 768))
def retryNotificationRank {tiles candidate} (family : ReplySourceFamily tiles candidate) (copy : Tma.CopyId) : Nat :=
  if ha : ∃ tile < tiles, copy = family.copyAId tile then retryNoticeClock family (Classical.choose ha) false
  else if hb : ∃ tile < tiles, copy = family.copyBId tile then retryNoticeClock family (Classical.choose hb) true
  else 0
def retryTmaRank {tiles candidate} (family : ReplySourceFamily tiles candidate) : Tma.Node → Nat
  | .source id => retrySourceRank family id
  | .descriptor copy => retrySourceRank family copy.issue+retryUnit family*128
  | .read copy _ => retrySourceRank family copy.issue+retryUnit family*256
  | .write copy _ => retrySourceRank family copy.issue+retryUnit family*384
  | .notify copy => retryNotificationRank family copy

theorem retry_notification_a_rank {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles) :
    retryNotificationRank family (family.copyAId tile) = retryNoticeClock family tile false := by
  have ha : ∃ actual < tiles, family.copyAId tile = family.copyAId actual := ⟨tile,ht,rfl⟩
  rw [retryNotificationRank,dif_pos ha]
  have hi : Classical.choose ha = tile := (family_copy_a_tile_injective family (Classical.choose_spec ha).2).symm
  rw [hi]

theorem retry_notification_b_rank {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles) :
    retryNotificationRank family (family.copyBId tile) = retryNoticeClock family tile true := by
  have hna : ¬∃ actual < tiles, family.copyBId tile = family.copyAId actual := by
    rintro ⟨actual,ha,he⟩
    exact retry_copy_roles_disjoint family actual tile ha ht he.symm
  have hb : ∃ actual < tiles, family.copyBId tile = family.copyBId actual := ⟨tile,ht,rfl⟩
  rw [retryNotificationRank,dif_neg hna,dif_pos hb]
  have hi : Classical.choose hb = tile := (family_copy_b_tile_injective family (Classical.choose_spec hb).2).symm
  rw [hi]

theorem retry_failed_before_notice {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles)
    (lane : Wgmma.Lane) (attempt : Nat) (ha : attempt < family.schedules lane tile) :
    retryFailedClock family tile lane attempt < retryNoticeClock family tile false := by
  apply (retry_failed_clock_bounds family tile ht lane attempt ha).2.trans
  change retryUnit family*(1024*(7+10*tile)+129) < retryUnit family*(1024*(7+10*tile)+768)
  exact Nat.mul_lt_mul_of_pos_left (by omega) (retry_unit_pos family)

theorem retry_notice_a_before_b {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) :
    retryNoticeClock family tile false < retryNoticeClock family tile true := by
  change retryUnit family*(1024*(7+10*tile)+768) < retryUnit family*(1024*(7+10*tile)+896)
  exact Nat.mul_lt_mul_of_pos_left (by omega) (retry_unit_pos family)

theorem retry_notice_before_success {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane) :
    retryNoticeClock family tile true < retryClock family (8+10*tile) lane := by
  change retryUnit family*(1024*(7+10*tile)+896) < retryUnit family*(1024*(8+10*tile)+lane.val)
  exact Nat.mul_lt_mul_of_pos_left (by omega) (retry_unit_pos family)

theorem retry_copy_a_before_notice {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles) :
    retryTmaRank family (.write (family.copyAId tile) 0) < retryTmaRank family (.notify (family.copyAId tile)) := by
  rw [retryTmaRank,retryTmaRank,retry_copy_a_source_rank family tile ht,retry_notification_a_rank family tile ht]
  unfold retryNoticeClock
  rw [← Nat.mul_add]
  apply Nat.mul_lt_mul_of_pos_left _ (retry_unit_pos family)
  unfold copyASerial
  split_ifs <;> omega

theorem retry_copy_b_before_notice {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles) :
    retryTmaRank family (.write (family.copyBId tile) 0) < retryTmaRank family (.notify (family.copyBId tile)) := by
  rw [retryTmaRank,retryTmaRank,retry_copy_b_source_rank family tile ht,retry_notification_b_rank family tile ht]
  unfold retryNoticeClock
  rw [← Nat.mul_add]
  apply Nat.mul_lt_mul_of_pos_left _ (retry_unit_pos family)
  unfold copyBSerial
  split_ifs <;> omega

theorem retry_tma_program_order {tiles initial candidate left right} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (he : Tma.ProgramOrder candidate.view left right) :
    retryTmaRank family left < retryTmaRank family right := by
  cases left <;> cases right <;> try exact False.elim he
  exact retry_source_program_order family hw he

theorem retry_tma_internal_order {tiles initial candidate left right} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (he : Tma.InternalEdge candidate.view left right) :
    retryTmaRank family left < retryTmaRank family right := by
  have hu := retry_unit_pos family
  cases he with
  | issue _ => dsimp [retryTmaRank]; omega
  | descriptorRead _ => dsimp [retryTmaRank]; omega
  | descriptorWrite _ => dsimp [retryTmaRank]; omega
  | data _ => dsimp [retryTmaRank]; omega
  | @complete id offset hp =>
    obtain ⟨copy,hcopy,_⟩ := Tma.write_has_copy hp
    obtain ⟨tile,hlt,hrole | hrole⟩ := retry_all_source_copies family ht hw id copy hcopy
    · rw [hrole.1]
      exact retry_copy_a_before_notice family tile hlt
    · rw [hrole.1]
      exact retry_copy_b_before_notice family tile hlt

end
end Ptx.Kernels.HopperDoubleBuffer
