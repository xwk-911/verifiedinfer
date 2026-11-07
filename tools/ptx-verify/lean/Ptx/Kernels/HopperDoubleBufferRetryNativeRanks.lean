import Ptx.Kernels.HopperDoubleBufferRetryClockGaps
import Ptx.Kernels.HopperDoubleBufferRetryCtaControl

/-! Retry-aware ranks for actual native arrival, warp rendezvous, operand
issue and completion edges. Rank values are proof devices only: source events,
participation requirements and memory/visibility semantics are unchanged. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def retryNativeTick {tiles candidate} (family : ReplySourceFamily tiles candidate) (id : Ptx.Event.EventId) : Nat :=
  retrySourceRank family id / retryUnit family / 1024
def retryUnifiedRank {tiles candidate} (family : ReplySourceFamily tiles candidate) : Unified.ControlNode → Nat
  | .base node => 2*retryTmaRank family node
  | .arrival id => 2*(retryUnit family*(1024*retryNativeTick family id))-1
  | .operand id _ => 2*(retryUnit family*(1024*retryNativeTick family id+128))

theorem retry_actual_native_tick {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane) (index : Fin 4) :
    retryNativeTick family (family.nativeId tile lane index) = 12+10*tile+index.val := by
  unfold retryNativeTick
  rw [retry_native_source_rank family tile ht lane index]
  simp only [retryClock,Nat.mul_div_cancel_left _ (retry_unit_pos family)]
  have hl := lane.isLt
  omega

theorem retry_native_arrival_order {tiles initial candidate left right} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (he : Unified.NativeArrival candidate left right) : retryUnifiedRank family left < retryUnifiedRank family right := by
  cases left with
  | base node =>
    cases node <;> cases right <;> try exact False.elim he
    rename_i before event
    obtain ⟨hp,hs⟩ := he
    obtain ⟨signature,hs⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨tile,lane,index,ht,rfl,_⟩ := retry_native_signature_shape family hw hs
    have hg := retry_before_native_clock_gap family hw tile ht lane index hp
    simp only [retryUnifiedRank,retryTmaRank,retry_actual_native_tick family tile ht lane index]
    omega
  | arrival _ | operand _ _ => exact False.elim he

theorem retry_native_rendezvous_order {tiles initial candidate left right} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (he : Unified.NativeRendezvous HopperStage.block candidate left right) :
    retryUnifiedRank family left < retryUnifiedRank family right := by
  cases left <;> cases right <;> try exact False.elim he
  rename_i left node
  cases node <;> try exact False.elim he
  rename_i right
  obtain ⟨tile,ll,rl,index,ht,rfl,rfl⟩ := retry_native_sync_identity family hw he
  have hp : 0 < retryUnit family*(1024*(12+10*tile+index.val)) :=
    Nat.mul_pos (retry_unit_pos family) (by omega)
  have hm : retryUnit family*(1024*(12+10*tile+index.val)) ≤ retryClock family (12+10*tile+index.val) rl :=
    Nat.mul_le_mul_left _ (by omega)
  simp only [retryUnifiedRank,retryTmaRank,retry_actual_native_tick family tile ht ll index,
    retry_native_source_rank family tile ht rl index]
  omega

theorem retry_native_issue_order {tiles initial candidate left right} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (he : Unified.NativeIssue candidate left right) : retryUnifiedRank family left < retryUnifiedRank family right := by
  cases left with
  | base node =>
    cases node <;> cases right <;> try exact False.elim he
    rename_i event issue operand
    obtain ⟨rfl,hs⟩ := he
    obtain ⟨⟨mark,call⟩,hs⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨tile,lane,ht,rfl,_,_⟩ := retry_native_mma_case family hw (Unified.representative_at hs).1
    simp only [retryUnifiedRank,retryTmaRank,retry_actual_native_tick family tile ht lane 1,
      retry_native_source_rank family tile ht lane 1]
    apply Nat.mul_lt_mul_of_pos_left _ (by decide)
    apply Nat.mul_lt_mul_of_pos_left _ (retry_unit_pos family)
    have hl := lane.isLt
    omega
  | arrival _ | operand _ _ => exact False.elim he

theorem retry_native_completion_tiles {tiles initial candidate issue wait} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hb : tiles ≤ 2^28)
    (he : Unified.WgmmaCompletedAt candidate issue wait) :
    ∃ it il wt wl, it < tiles ∧ wt < tiles ∧ issue = family.nativeId it il 1 ∧
      wait = family.nativeId wt wl 3 ∧ it ≤ wt := by
  obtain ⟨collective,lane,mark,groups,keep,before,after,query,he,_,_,_,_,hg,_⟩ := he
  have hm : candidate.eventAt issue = some (.mma (collective.marks 0) (collective.calls 0)) := by
    simpa only [collective.representative] using collective.matched 0
  obtain ⟨it,il,hit,hissue,_,hcall⟩ := retry_native_mma_case family hw hm
  have hgroup : (collective.calls lane).group = it := by
    rw [collective.cohort.group,hcall]
    exact reply_call_group _ _ _ _ _
  obtain ⟨wt,wl,hwt,hwait,hafter⟩ := retry_native_wait_case family hw hb he
  rw [hgroup,hafter] at hg
  exact ⟨it,il,wt,wl,hit,hwt,hissue,hwait,by omega⟩

theorem retry_native_finish_order {tiles initial candidate left right} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hb : tiles ≤ 2^28)
    (he : Unified.NativeFinish candidate left right) : retryUnifiedRank family left < retryUnifiedRank family right := by
  cases left <;> cases right <;> try exact False.elim he
  rename_i issue operand node
  cases node <;> try exact False.elim he
  rename_i wait
  obtain ⟨it,il,wt,wl,hit,hwt,rfl,rfl,htw⟩ := retry_native_completion_tiles family hw hb he
  simp only [retryUnifiedRank,retryTmaRank,retry_actual_native_tick family it hit il 1,
    retry_native_source_rank family wt hwt wl 3,retryClock]
  apply Nat.mul_lt_mul_of_pos_left _ (by decide)
  apply Nat.mul_lt_mul_of_pos_left _ (retry_unit_pos family)
  omega

end
end Ptx.Kernels.HopperDoubleBuffer
