import Ptx.Kernels.HopperDoubleBufferRetryResourceMembership

/-! Source-ID separation across arbitrary retries. These are metadata identity
rules, not memory-order or control-acyclicity assumptions. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem reply_tile_start_strict_mono (tiles lane reply retries) :
    StrictMono (replyTileStart tiles lane reply retries) := by
  apply strictMono_nat_of_lt_succ
  intro tile
  rw [reply_tile_start_succ]
  omega

theorem reply_wait_interval (tiles lane reply retries tile attempt) (ha : attempt ≤ retries tile) :
    replyTileStart tiles lane reply retries tile ≤ (replyFailedWaitId tiles lane reply retries tile attempt).serial ∧
    (replyFailedWaitId tiles lane reply retries tile attempt).serial < replyTileStart tiles lane reply retries (tile+1) := by
  simp only [replyFailedWaitId,reply_tile_start_succ]
  omega

theorem reply_waits_separated (tiles lane reply retries left right a b) (ht : left < right) (ha : a ≤ retries left) :
    (replyFailedWaitId tiles lane reply retries left a).serial < (replyFailedWaitId tiles lane reply retries right b).serial := by
  have hx := (reply_wait_interval tiles lane reply retries left a ha).2
  have hm := (reply_tile_start_strict_mono tiles lane reply retries).monotone (show left+1 ≤ right by omega)
  simp only [replyFailedWaitId] at *
  omega

theorem family_wait_endpoint_injective {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (left right : Nat) (a b : Wgmma.Lane) (i j : Nat) (hi : i ≤ family.schedules a left) (hj : j ≤ family.schedules b right)
    (he : family.failedWaitId left a i = family.failedWaitId right b j) : left = right ∧ a = b ∧ i = j := by
  have hl : (ctx tiles a).id = (ctx tiles b).id := congrArg Ptx.Event.EventId.thread he
  have hab : a = b := resource_ctx_injective tiles hl
  subst b
  have hs := congrArg Ptx.Event.EventId.serial he
  have ht : left = right := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hh := reply_waits_separated tiles a (family.replies a) (family.schedules a) left right i j hlt hi
      change (family.failedWaitId left a i).serial < (family.failedWaitId right a j).serial at hh
      omega
    · have hh := reply_waits_separated tiles a (family.replies a) (family.schedules a) right left j i hgt hj
      change (family.failedWaitId right a j).serial < (family.failedWaitId left a i).serial at hh
      omega
  subst right
  have hij : i = j := by
    change replyTileStart tiles a (family.replies a) (family.schedules a) left+i =
      replyTileStart tiles a (family.replies a) (family.schedules a) left+j at hs
    omega
  exact ⟨rfl,rfl,hij⟩

theorem reply_expect_serial_strict_mono (tiles reply retries) :
    StrictMono (fun tile => (replyExpectId tiles reply retries tile).serial) := by
  apply strictMono_nat_of_lt_succ
  intro tile
  cases tile with
  | zero =>
    change 5 < 8+retries 0+1+0
    omega
  | succ tile =>
    simp only [replyExpectId,replyPrefetchId,reply_tile_start_succ]
    omega

theorem reply_copy_a_serial_strict_mono (tiles reply retries) :
    StrictMono (fun tile => (replyCopyAId tiles reply retries tile).issue.serial) := by
  apply strictMono_nat_of_lt_succ
  intro tile
  cases tile with
  | zero =>
    change 6 < 8+retries 0+1+1
    omega
  | succ tile =>
    simp only [replyCopyAId,replyPrefetchId,reply_tile_start_succ]
    omega

theorem reply_copy_b_serial_strict_mono (tiles reply retries) :
    StrictMono (fun tile => (replyCopyBId tiles reply retries tile).issue.serial) := by
  apply strictMono_nat_of_lt_succ
  intro tile
  cases tile with
  | zero =>
    change 7 < 8+retries 0+1+2
    omega
  | succ tile =>
    simp only [replyCopyBId,replyPrefetchId,reply_tile_start_succ]
    omega

theorem family_expect_tile_injective {tiles candidate} (family : ReplySourceFamily tiles candidate) {left right : Nat}
    (he : family.expectId left = family.expectId right) : left = right :=
  (reply_expect_serial_strict_mono tiles (family.replies 0) (family.schedules 0)).injective (congrArg Ptx.Event.EventId.serial he)
theorem family_copy_a_tile_injective {tiles candidate} (family : ReplySourceFamily tiles candidate) {left right : Nat}
    (he : family.copyAId left = family.copyAId right) : left = right :=
  (reply_copy_a_serial_strict_mono tiles (family.replies 0) (family.schedules 0)).injective (congrArg (fun id : Tma.CopyId => id.issue.serial) he)
theorem family_copy_b_tile_injective {tiles candidate} (family : ReplySourceFamily tiles candidate) {left right : Nat}
    (he : family.copyBId left = family.copyBId right) : left = right :=
  (reply_copy_b_serial_strict_mono tiles (family.replies 0) (family.schedules 0)).injective (congrArg (fun id : Tma.CopyId => id.issue.serial) he)

end
end Ptx.Kernels.HopperDoubleBuffer
