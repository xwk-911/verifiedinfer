import Ptx.Kernels.HopperDoubleBufferRetryClockOrder

/-! Retry-aware clocks attached to actual source identities. Every present
source event has a clock entry and every actual program-order edge increases
the rank. Actual native source clocks are aligned across lanes. Resource,
implicit TMA and combined-control edge checks remain separate obligations. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def retryRankLane (id : Ptx.Event.EventId) : Wgmma.Lane := ⟨resourceLane id.thread%128,Nat.mod_lt _ (by decide)⟩
def retrySourceRank {tiles candidate} (family : ReplySourceFamily tiles candidate) (id : Ptx.Event.EventId) : Nat :=
  ((retrySourceClocks family (retryRankLane id))[id.serial]?).getD 0

theorem retry_rank_lane_of_thread {tiles id lane} (h : id.thread = (ctx tiles lane).id) : retryRankLane id = lane := by
  apply Fin.ext
  dsimp [retryRankLane]
  rw [h,resource_lane_value,Nat.mod_eq_of_lt lane.isLt]

theorem retry_source_event_clock_bound {tiles initial candidate id event} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (he : candidate.eventAt id = some event) :
    id.serial < (retrySourceClocks family (retryRankLane id)).length := by
  obtain ⟨trace,ht,hid,hget⟩ := Unified.eventAt_trace he
  obtain ⟨lane,rfl⟩ := retry_trace_family family hw ht
  have hthread : id.thread = (ctx tiles lane).id := hid.symm.trans (family.ids lane)
  rw [retry_rank_lane_of_thread hthread,retry_source_clocks_length]
  rw [family.events] at hget
  exact (List.getElem?_eq_some_iff.mp hget).1

theorem retry_present_source_clock_bound {tiles initial candidate id} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hp : candidate.view.Present id) :
    id.serial < (retrySourceClocks family (retryRankLane id)).length := by
  obtain ⟨event,he⟩ := Option.isSome_iff_exists.mp hp
  rw [Unified.view_eventAt] at he
  obtain ⟨rich,hr,_⟩ := Option.map_eq_some_iff.mp he
  exact retry_source_event_clock_bound family hw hr

theorem retry_source_program_order {tiles initial candidate left right} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hp : Hopper.ProgramOrder candidate.view left right) :
    retrySourceRank family left < retrySourceRank family right := by
  have hl := retry_present_source_clock_bound family hw hp.1
  have hr := retry_present_source_clock_bound family hw hp.2.1
  have he : retryRankLane left = retryRankLane right := by apply Fin.ext; dsimp [retryRankLane]; rw [hp.2.2.1]
  rw [← he] at hr
  have hs := (retry_source_clocks_strict family (retryRankLane left)).rel_getElem_of_lt hl hr hp.2.2.2
  simp only [retrySourceRank,← he,List.getElem?_eq_getElem hl,List.getElem?_eq_getElem hr,Option.getD_some]
  exact hs

theorem retry_loop_clock_index_retained {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane)
    (m n index value : Nat) (hle : m ≤ n) (he : (retryLoopClocks family lane m)[index]? = some value) :
    (retryLoopClocks family lane n)[index]? = some value := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    simpa only [hm] using he
  | succ n ih =>
    by_cases hm : m = n+1
    · simpa only [hm] using he
    · have hold := ih (by omega)
      have hi := (List.getElem?_eq_some_iff.mp hold).1
      rw [retryLoopClocks,List.getElem?_append_left hi]
      exact hold

theorem retry_source_iteration_clock {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane)
    (tile index value : Nat) (ht : tile < tiles) (he : (retryIterationClocks family tile lane)[index]? = some value) :
    (retrySourceClocks family lane)[replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+index]? = some value := by
  have hs : (retryLoopClocks family lane (tile+1))[(retryLoopClocks family lane tile).length+index]? = some value := by
    rw [retryLoopClocks,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    exact he
  have hf := retry_loop_clock_index_retained family lane (tile+1) tiles _ value (by omega) hs
  have hprefix : replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile =
      (retryInitialClocks family lane).length+(retryLoopClocks family lane tile).length := by
    rw [retry_initial_clocks_length,retry_loop_clocks_length]
    rfl
  rw [hprefix,retrySourceClocks]
  have hi := (List.getElem?_eq_some_iff.mp hf).1
  rw [List.getElem?_append_left (by simp only [List.length_append]; omega),List.getElem?_append_right (by omega)]
  simpa only [Nat.add_assoc,Nat.add_sub_cancel_left] using hf

theorem retry_iteration_native_clock {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (tile : Nat) (lane : Wgmma.Lane) (index : Fin 4) :
    (retryIterationClocks family tile lane)[family.schedules lane tile+preludeEventCount tile tiles (HopperStage.leader lane)+1+index.val]? =
      some (retryClock family (12+10*tile+index.val) lane) := by
  simp only [retryIterationClocks,List.append_assoc]
  rw [List.getElem?_append_right (by simp only [retryFailedClocks,List.length_ofFn]; omega)]
  simp only [retryFailedClocks,List.length_ofFn]
  rw [List.getElem?_append_right (by simp only [List.length_cons,List.length_nil]; omega)]
  simp only [List.length_cons,List.length_nil]
  rw [List.getElem?_append_right (by simp only [retryPreludeClocks,List.length_ofFn]; omega)]
  simp only [retryPreludeClocks,List.length_ofFn]
  rw [show family.schedules lane tile+preludeEventCount tile tiles (HopperStage.leader lane)+1+index.val-family.schedules lane tile-1-
    preludeEventCount tile tiles (HopperStage.leader lane) = index.val by omega]
  rw [List.getElem?_eq_getElem (by simp only [retryComputeClocks,List.length_ofFn]; have := index.isLt; omega)]
  simp only [retryComputeClocks,List.getElem_ofFn]

theorem retry_native_source_rank {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane) (index : Fin 4) :
    retrySourceRank family (family.nativeId tile lane index) = retryClock family (12+10*tile+index.val) lane := by
  have he := retry_source_iteration_clock family lane tile _ _ ht (retry_iteration_native_clock family tile lane index)
  have hl : retryRankLane (family.nativeId tile lane index) = lane := retry_rank_lane_of_thread (tiles := tiles) rfl
  unfold retrySourceRank
  rw [hl]
  change ((retrySourceClocks family lane)[replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+
    (family.schedules lane tile+preludeEventCount tile tiles (HopperStage.leader lane)+1+index.val)]?).getD 0 = _
  rw [he]
  rfl

theorem retry_failed_wait_source_rank {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane) (attempt : Nat) (ha : attempt < family.schedules lane tile) :
    retrySourceRank family (family.failedWaitId tile lane attempt) = retryFailedClock family tile lane attempt := by
  have he : (retryIterationClocks family tile lane)[attempt]? = some (retryFailedClock family tile lane attempt) := by
    simp only [retryIterationClocks,List.append_assoc]
    rw [List.getElem?_append_left (by simpa only [retryFailedClocks,List.length_ofFn] using ha)]
    rw [List.getElem?_eq_getElem (by simpa only [retryFailedClocks,List.length_ofFn] using ha)]
    simp only [retryFailedClocks,List.getElem_ofFn]
  have hr := retry_source_iteration_clock family lane tile attempt _ ht he
  have hl : retryRankLane (family.failedWaitId tile lane attempt) = lane := retry_rank_lane_of_thread (tiles := tiles) rfl
  unfold retrySourceRank
  rw [hl]
  change ((retrySourceClocks family lane)[replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+attempt]?).getD 0 = _
  rw [hr]
  rfl

theorem retry_successful_wait_source_rank {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane) :
    retrySourceRank family (family.waitId tile lane) = retryClock family (8+10*tile) lane := by
  have he : (retryIterationClocks family tile lane)[family.schedules lane tile]? = some (retryClock family (8+10*tile) lane) := by
    simp only [retryIterationClocks,List.append_assoc]
    rw [List.getElem?_append_right (by simp only [retryFailedClocks,List.length_ofFn]; exact Nat.le_refl _)]
    simp only [retryFailedClocks,List.length_ofFn,Nat.sub_self]
    rfl
  have hr := retry_source_iteration_clock family lane tile _ _ ht he
  have hl : retryRankLane (family.waitId tile lane) = lane := retry_rank_lane_of_thread (tiles := tiles) rfl
  unfold retrySourceRank
  rw [hl]
  change ((retrySourceClocks family lane)[replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+family.schedules lane tile]?).getD 0 = _
  rw [hr]
  rfl

end
end Ptx.Kernels.HopperDoubleBuffer
