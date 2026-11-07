import Ptx.Kernels.HopperDoubleBufferReplyPrefetch
import Ptx.Kernels.HopperDoubleBufferResourceEndpoints

/-! Actual initialization/invalidation endpoints for rich source families.
These identify source resources without assuming resource-history admission. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def ReplySourceFamily.initId {tiles candidate} (_family : ReplySourceFamily tiles candidate) (slot : Stage) : Ptx.Event.EventId :=
  ⟨(ctx tiles 0).id,slot.val⟩
def ReplySourceFamily.invalId {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot : Stage) : Ptx.Event.EventId :=
  ⟨(ctx tiles 0).id,replyTileStart tiles 0 (family.replies 0) (family.schedules 0) tiles+6+slot.val⟩

theorem reply_complete_inval_at (tiles reply retries slot) :
    (replyPositiveEvents tiles 0 reply retries)[replyTileStart tiles 0 reply retries tiles+6+slot.val]? =
      some (.base (.barrier ⟨dataGate slot,.inval⟩)) := by
  simp only [replyPositiveEvents,← List.append_assoc]
  change ((replyInitialEvents 0 reply++replyLoopEvents tiles 0 reply retries tiles)++_)[_]? = _
  rw [List.getElem?_append_right (by simp only [List.length_append]; unfold replyTileStart; omega)]
  rw [show replyTileStart tiles 0 reply retries tiles+6+slot.val-
    (replyInitialEvents 0 reply++replyLoopEvents tiles 0 reply retries tiles).length = 6+slot.val by
      simp only [List.length_append,replyTileStart]; omega]
  fin_cases slot <;> rfl

theorem family_init_at {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (slot : Stage) :
    Tma.resourceAt Tma.localShared candidate.view (.source (family.initId slot)) = some ⟨dataGate slot,.init 1⟩ := by
  have he := family_event_at family hw 0 slot.val _
    (reply_complete_initial_at tiles 0 (family.replies 0) (family.schedules 0) slot.val
      (.base (.barrier ⟨dataGate slot,.init 1⟩)) (by fin_cases slot <;> rfl))
  exact Hopper.barrierAt_iff.mpr (Unified.view_barrier_iff.mpr he)

theorem family_inval_at {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (slot : Stage) :
    Tma.resourceAt Tma.localShared candidate.view (.source (family.invalId slot)) = some ⟨dataGate slot,.inval⟩ :=
  Hopper.barrierAt_iff.mpr (Unified.view_barrier_iff.mpr (family_event_at family hw 0 _ _
    (reply_complete_inval_at tiles (family.replies 0) (family.schedules 0) slot)))

theorem reply_copy_a_barrier (tiles reply retries tile) :
    (replyCopyA tiles reply retries tile).barrier = barrierAddress (stage tile) := by
  cases tile <;> rfl
theorem reply_copy_b_barrier (tiles reply retries tile) :
    (replyCopyB tiles reply retries tile).barrier = barrierAddress (stage tile) := by
  cases tile <;> rfl
theorem reply_copy_a_descriptor_address (tiles reply retries tile) :
    (replyCopyA tiles reply retries tile).descriptorAddress = 4096 := by
  cases tile <;> rfl
theorem reply_copy_b_descriptor_address (tiles reply retries tile) :
    (replyCopyB tiles reply retries tile).descriptorAddress = 4224 := by
  cases tile <;> rfl

theorem family_notification_a {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (tile : Nat) (ht : tile < tiles) :
    Tma.resourceAt Tma.localShared candidate.view (.notification (family.copyAId tile)) =
      some ⟨dataGate (stage tile),.completeTx 2048⟩ := by
  have he := family_copy_a_at family hw tile ht
  have hm := hd _ _ he
  rw [reply_copy_a_descriptor_address] at hm
  have hv : (replyCopyA tiles (family.replies 0) (family.schedules 0) tile).descriptor = aView 65536 tiles := by
    simpa only [dataMaps,ite_true,show ¬(4096 = 4224) from by decide,ite_false,Option.some.injEq] using hm.symm
  have hid : (family.copyAId tile).issue.thread = (ctx tiles 0).id := by cases tile <;> rfl
  simp only [Tma.resourceAt,Tma.notification,he,Option.map_some,hv,reply_copy_a_barrier,Tma.localShared,hid,dataGate]
  rfl

theorem family_notification_b {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (tile : Nat) (ht : tile < tiles) :
    Tma.resourceAt Tma.localShared candidate.view (.notification (family.copyBId tile)) =
      some ⟨dataGate (stage tile),.completeTx 256⟩ := by
  have he := family_copy_b_at family hw tile ht
  have hm := hd _ _ he
  rw [reply_copy_b_descriptor_address] at hm
  have hv : (replyCopyB tiles (family.replies 0) (family.schedules 0) tile).descriptor = bView (dataBBase tiles) tiles := by
    simpa only [dataMaps,show ¬(4224 = 4096) from by decide,ite_false,ite_true,Option.some.injEq] using hm.symm
  have hid : (family.copyBId tile).issue.thread = (ctx tiles 0).id := by cases tile <;> rfl
  simp only [Tma.resourceAt,Tma.notification,he,Option.map_some,hv,reply_copy_b_barrier,Tma.localShared,hid,dataGate]
  rfl

end
end Ptx.Kernels.HopperDoubleBuffer
