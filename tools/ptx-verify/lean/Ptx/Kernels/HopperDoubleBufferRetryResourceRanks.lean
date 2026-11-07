import Ptx.Kernels.HopperDoubleBufferRetrySourceRank
import Ptx.Kernels.HopperDoubleBufferRetryResourceAdmission

/-! Actual source ranks for resource expectations, copy issues and endpoints.
These bridge the retry-aware source clock to resource identities without
assuming a chosen notification order or altering source synchronization. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_initial_source_rank {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane)
    (index : Fin (if HopperStage.leader lane then 8 else 2)) :
    retrySourceRank family ⟨(ctx tiles lane).id,index.val⟩ =
      retryClock family (index.val+(if HopperStage.leader lane then 0 else 3)) lane := by
  have hl : retryRankLane ⟨(ctx tiles lane).id,index.val⟩ = lane := retry_rank_lane_of_thread (tiles := tiles) rfl
  unfold retrySourceRank
  rw [hl]
  have hi : index.val < (retryInitialClocks family lane).length := by simpa only [retryInitialClocks,List.length_ofFn] using index.isLt
  change ((retrySourceClocks family lane)[index.val]?).getD 0 = _
  rw [retrySourceClocks,List.getElem?_append_left (by simp only [List.length_append]; omega),List.getElem?_append_left hi,
    List.getElem?_eq_getElem hi]
  simp only [retryInitialClocks,List.getElem_ofFn,Option.getD_some]

theorem retry_output_source_rank {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane)
    (index : Fin (if HopperStage.leader lane then 8 else 6)) :
    retrySourceRank family ⟨(ctx tiles lane).id,replyTileStart tiles lane (family.replies lane) (family.schedules lane) tiles+index.val⟩ =
      retryClock family (8+10*tiles+index.val) lane := by
  have hl : retryRankLane ⟨(ctx tiles lane).id,replyTileStart tiles lane (family.replies lane) (family.schedules lane) tiles+index.val⟩ = lane :=
    retry_rank_lane_of_thread (tiles := tiles) rfl
  have hp : replyTileStart tiles lane (family.replies lane) (family.schedules lane) tiles =
      (retryInitialClocks family lane++retryLoopClocks family lane tiles).length := by
    rw [List.length_append,retry_initial_clocks_length,retry_loop_clocks_length]
    rfl
  unfold retrySourceRank
  rw [hl]
  change ((retrySourceClocks family lane)[replyTileStart tiles lane (family.replies lane) (family.schedules lane) tiles+index.val]?).getD 0 = _
  rw [retrySourceClocks,hp,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
  rw [List.getElem?_eq_getElem (by simpa only [retryOutputClocks,List.length_ofFn] using index.isLt)]
  simp only [retryOutputClocks,List.getElem_ofFn,Option.getD_some]

theorem retry_prefetch_source_rank {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (hn : tile+1 < tiles) (index : Fin 3) :
    retrySourceRank family (replyPrefetchId tiles (family.replies 0) (family.schedules 0) tile index.val) =
      retryClock family (9+10*tile+index.val) 0 := by
  have hp : preludeEventCount tile tiles (HopperStage.leader 0) = 3 := by simp [preludeEventCount,needsPrefetch,hn,HopperStage.leader]
  have he : (retryIterationClocks family tile 0)[family.schedules 0 tile+1+index.val]? =
      some (retryClock family (9+10*tile+index.val) 0) := by
    simp only [retryIterationClocks,List.append_assoc]
    rw [List.getElem?_append_right (by simp only [retryFailedClocks,List.length_ofFn]; omega)]
    simp only [retryFailedClocks,List.length_ofFn]
    rw [List.getElem?_append_right (by simp only [List.length_cons,List.length_nil]; omega)]
    simp only [List.length_cons,List.length_nil]
    rw [show family.schedules 0 tile+1+index.val-family.schedules 0 tile-1 = index.val by omega]
    rw [List.getElem?_append_left (by simpa only [retryPreludeClocks,List.length_ofFn,hp] using index.isLt)]
    rw [List.getElem?_eq_getElem (by simpa only [retryPreludeClocks,List.length_ofFn,hp] using index.isLt)]
    simp only [retryPreludeClocks,List.getElem_ofFn]
  have hr := retry_source_iteration_clock family 0 tile _ _ (by omega) he
  have hl : retryRankLane (replyPrefetchId tiles (family.replies 0) (family.schedules 0) tile index.val) = 0 :=
    retry_rank_lane_of_thread (tiles := tiles) rfl
  unfold retrySourceRank
  rw [hl]
  change ((retrySourceClocks family 0)[replyTileStart tiles 0 (family.replies 0) (family.schedules 0) tile+
    family.schedules 0 tile+1+index.val]?).getD 0 = _
  rw [show replyTileStart tiles 0 (family.replies 0) (family.schedules 0) tile+family.schedules 0 tile+1+index.val =
    replyTileStart tiles 0 (family.replies 0) (family.schedules 0) tile+(family.schedules 0 tile+1+index.val) by omega,hr]
  rfl

theorem retry_expect_source_rank {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles) :
    retrySourceRank family (family.expectId tile) = retryUnit family*(1024*expectSerial tile) := by
  cases tile with
  | zero => exact retry_initial_source_rank family 0 5
  | succ tile =>
    have he := retry_prefetch_source_rank family tile ht 0
    change retrySourceRank family (family.expectId (tile+1)) = _ at he
    rw [he]
    dsimp [retryClock,expectSerial]
    congr 1
    omega

theorem retry_copy_a_source_rank {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles) :
    retrySourceRank family (family.copyAId tile).issue = retryUnit family*(1024*copyASerial tile) := by
  cases tile with
  | zero => exact retry_initial_source_rank family 0 6
  | succ tile =>
    have he := retry_prefetch_source_rank family tile ht 1
    change retrySourceRank family (family.copyAId (tile+1)).issue = _ at he
    rw [he]
    dsimp [retryClock,copyASerial]
    congr 1
    omega

theorem retry_copy_b_source_rank {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles) :
    retrySourceRank family (family.copyBId tile).issue = retryUnit family*(1024*copyBSerial tile) := by
  cases tile with
  | zero => exact retry_initial_source_rank family 0 7
  | succ tile =>
    have he := retry_prefetch_source_rank family tile ht 2
    change retrySourceRank family (family.copyBId (tile+1)).issue = _ at he
    rw [he]
    dsimp [retryClock,copyBSerial]
    congr 1
    omega

theorem retry_init_source_rank {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot : Stage) :
    retrySourceRank family (family.initId slot) = retryUnit family*(1024*slot.val) := by
  exact retry_initial_source_rank family 0 ⟨slot.val,by have := slot.isLt; change slot.val < 8; omega⟩

theorem retry_inval_source_rank {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot : Stage) :
    retrySourceRank family (family.invalId slot) = retryUnit family*(1024*(10*tiles+14+slot.val)) := by
  have he := retry_output_source_rank family 0 ⟨6+slot.val,by have := slot.isLt; change 6+slot.val < 8; omega⟩
  have hs : retrySourceRank family (family.invalId slot) = retryClock family (8+10*tiles+(6+slot.val)) 0 := by
    simpa only [ReplySourceFamily.invalId,Nat.add_assoc] using he
  rw [hs]
  dsimp [retryClock]
  congr 1
  omega

theorem retry_copy_roles_disjoint {tiles candidate} (family : ReplySourceFamily tiles candidate) (left right : Nat) (hl : left < tiles) (hr : right < tiles) :
    family.copyAId left ≠ family.copyBId right := by
  intro he
  have hh := congrArg (fun id : Tma.CopyId => retrySourceRank family id.issue) he
  rw [retry_copy_a_source_rank family left hl,retry_copy_b_source_rank family right hr] at hh
  have hs := Nat.eq_of_mul_eq_mul_left (retry_unit_pos family) hh
  by_cases hleft : left = 0 <;> by_cases hright : right = 0 <;>
    simp only [copyASerial,copyBSerial,hleft,hright,ite_true,ite_false] at hs <;> omega

end
end Ptx.Kernels.HopperDoubleBuffer
