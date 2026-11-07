import Ptx.Kernels.HopperDoubleBufferRetryResourceAdmission

/-! Byte locations of actual TMA writers and native operand descriptors with
arbitrary captured replies/retries. No operand-value/RF agreement is assumed. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem reply_copy_a_destination (tiles reply retries tile) :
    (replyCopyA tiles reply retries tile).destination = aBase (stage tile) := by cases tile <;> rfl
theorem reply_copy_b_destination (tiles reply retries tile) :
    (replyCopyB tiles reply retries tile).destination = bBase (stage tile) := by cases tile <;> rfl

theorem family_copy_a_descriptor {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (tile : Nat) (ht : tile < tiles) :
    (replyCopyA tiles (family.replies 0) (family.schedules 0) tile).descriptor = aView 65536 tiles := by
  have hm := hd _ _ (family_copy_a_at family hw tile ht)
  rw [reply_copy_a_descriptor_address] at hm
  simpa only [dataMaps,ite_true,Option.some.injEq] using hm.symm

theorem family_copy_b_descriptor {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (tile : Nat) (ht : tile < tiles) :
    (replyCopyB tiles (family.replies 0) (family.schedules 0) tile).descriptor = bView (dataBBase tiles) tiles := by
  have hm := hd _ _ (family_copy_b_at family hw tile ht)
  rw [reply_copy_b_descriptor_address] at hm
  simpa only [dataMaps,show ¬(4224 = 4096) from by decide,ite_false,ite_true,Option.some.injEq] using hm.symm

theorem retry_transfer_a_location {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (tile : Nat) (ht : tile < tiles) (offset : Fin 2048) :
    Tma.writeLocation Tma.localShared candidate.view (family.copyAId tile) offset.val =
      some ⟨.shared .zero,aBase (stage tile)+offset.val⟩ := by
  rw [Tma.writeLocation,family_copy_a_at family hw tile ht]
  simp only [Option.bind_some,family_copy_a_descriptor family hw hd tile ht,reply_copy_a_destination]
  change (if offset.val < 2048 then some ((Tma.localShared (family.copyAId tile).issue.thread (aBase (stage tile))).add offset.val) else none) = _
  rw [ite_eq_left offset.isLt]
  cases tile <;> rfl

theorem retry_transfer_b_location {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (tile : Nat) (ht : tile < tiles) (offset : Fin 256) :
    Tma.writeLocation Tma.localShared candidate.view (family.copyBId tile) offset.val =
      some ⟨.shared .zero,bBase (stage tile)+offset.val⟩ := by
  rw [Tma.writeLocation,family_copy_b_at family hw tile ht]
  simp only [Option.bind_some,family_copy_b_descriptor family hw hd tile ht,reply_copy_b_destination]
  change (if offset.val < 256 then some ((Tma.localShared (family.copyBId tile).issue.thread (bBase (stage tile))).add offset.val) else none) = _
  rw [ite_eq_left offset.isLt]
  cases tile <;> rfl

theorem reply_operand_a_location (tiles lane reply retries tile) (p : Wgmma.ACoord) (part : Fin 2) :
    Wgmma.operandLocation .zero (replyCall tiles lane reply retries tile) (.a p part) =
      ⟨.shared .zero,aBase (stage tile)+(Wgmma.aOffset (p,part)).val⟩ := by
  simp only [Wgmma.operandLocation,reply_call_a,a_operand_address]

theorem reply_operand_b_location (tiles lane reply retries tile) (p : Wgmma.BCoord) (part : Fin 2) :
    Wgmma.operandLocation .zero (replyCall tiles lane reply retries tile) (.b p part) =
      ⟨.shared .zero,bBase (stage tile)+(Wgmma.bOffset (p,part)).val⟩ := by
  simp only [Wgmma.operandLocation,reply_call_b,b_operand_address]

theorem retry_operand_a_transfer {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (tile : Nat) (ht : tile < tiles)
    (lane : Wgmma.Lane) (p : Wgmma.ACoord) (part : Fin 2) :
    Tma.writeLocation Tma.localShared candidate.view (family.copyAId tile) (Wgmma.aOffset (p,part)).val =
      some (Wgmma.operandLocation .zero (family.calls tile lane) (.a p part)) := by
  rw [show Wgmma.operandLocation .zero (family.calls tile lane) (.a p part) = _ from
    reply_operand_a_location tiles lane (family.replies lane) (family.schedules lane) tile p part]
  exact retry_transfer_a_location family hw hd tile ht _

theorem retry_operand_b_transfer {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (tile : Nat) (ht : tile < tiles)
    (lane : Wgmma.Lane) (p : Wgmma.BCoord) (part : Fin 2) :
    Tma.writeLocation Tma.localShared candidate.view (family.copyBId tile) (Wgmma.bOffset (p,part)).val =
      some (Wgmma.operandLocation .zero (family.calls tile lane) (.b p part)) := by
  rw [show Wgmma.operandLocation .zero (family.calls tile lane) (.b p part) = _ from
    reply_operand_b_location tiles lane (family.replies lane) (family.schedules lane) tile p part]
  exact retry_transfer_b_location family hw hd tile ht _

end
end Ptx.Kernels.HopperDoubleBuffer
