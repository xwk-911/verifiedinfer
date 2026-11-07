import Ptx.Kernels.HopperDoubleBufferRetryNativeCases

/-! Finite retry-aware control clock, independent of arithmetic/byte replies.
Every actual source event gets a clock entry. Failed waits share a bounded
subinterval before the future notification ranks; this is a proof device,
not an inserted execution step or a memory-visibility rule. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def retryBudget {tiles candidate} (family : ReplySourceFamily tiles candidate) : Nat :=
  1+∑ tile ∈ Finset.range tiles, ∑ lane : Wgmma.Lane, family.schedules lane tile
def retryUnit {tiles candidate} (family : ReplySourceFamily tiles candidate) : Nat := 128*retryBudget family+1
def retryClock {tiles candidate} (family : ReplySourceFamily tiles candidate) (tick : Nat) (lane : Wgmma.Lane) : Nat :=
  retryUnit family*(1024*tick+lane.val)
def retryFailedClock {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane) (attempt : Nat) : Nat :=
  retryUnit family*(1024*(7+10*tile)+128)+retryBudget family*lane.val+attempt
def retryInitialClocks {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) : List Nat :=
  List.ofFn (fun i : Fin (if HopperStage.leader lane then 8 else 2) =>
    retryClock family (i.val+(if HopperStage.leader lane then 0 else 3)) lane)
def retryFailedClocks {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane) : List Nat :=
  List.ofFn (fun i : Fin (family.schedules lane tile) => retryFailedClock family tile lane i.val)
def retryPreludeClocks {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane) : List Nat :=
  List.ofFn (fun i : Fin (preludeEventCount tile tiles (HopperStage.leader lane)) => retryClock family (9+10*tile+i.val) lane)
def retryComputeClocks {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane) : List Nat :=
  List.ofFn (fun i : Fin 6 => retryClock family (12+10*tile+i.val) lane)
def retryIterationClocks {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane) : List Nat :=
  retryFailedClocks family tile lane++[retryClock family (8+10*tile) lane]++
    retryPreludeClocks family tile lane++retryComputeClocks family tile lane
def retryLoopClocks {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) : Nat → List Nat
  | 0 => []
  | n+1 => retryLoopClocks family lane n++retryIterationClocks family n lane
def retryOutputClocks {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) : List Nat :=
  List.ofFn (fun i : Fin (if HopperStage.leader lane then 8 else 6) => retryClock family (8+10*tiles+i.val) lane)
def retrySourceClocks {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) : List Nat :=
  (retryInitialClocks family lane++retryLoopClocks family lane tiles)++retryOutputClocks family lane

theorem retry_budget_pos {tiles candidate} (family : ReplySourceFamily tiles candidate) : 0 < retryBudget family := by
  unfold retryBudget
  omega
theorem retry_schedule_lt_budget {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane) :
    family.schedules lane tile < retryBudget family := by
  have hl : family.schedules lane tile ≤ ∑ who : Wgmma.Lane, family.schedules who tile :=
    Finset.single_le_sum (s := Finset.univ) (f := fun who : Wgmma.Lane => family.schedules who tile)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ lane)
  have ht' : (∑ who : Wgmma.Lane, family.schedules who tile) ≤ ∑ t ∈ Finset.range tiles, ∑ who : Wgmma.Lane, family.schedules who t :=
    Finset.single_le_sum (s := Finset.range tiles) (f := fun t => ∑ who : Wgmma.Lane, family.schedules who t)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr ht)
  unfold retryBudget
  omega
theorem retry_unit_pos {tiles candidate} (family : ReplySourceFamily tiles candidate) : 0 < retryUnit family := by
  unfold retryUnit
  omega
theorem retry_clock_strict {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) :
    StrictMono (fun tick => retryClock family tick lane) := by
  intro left right hlr
  apply Nat.mul_lt_mul_of_pos_left (by omega) (retry_unit_pos family)
theorem retry_clock_mono {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) {left right : Nat} (h : left ≤ right) :
    retryClock family left lane ≤ retryClock family right lane := (retry_clock_strict family lane).monotone h
theorem retry_failed_clock_bounds {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles)
    (lane : Wgmma.Lane) (attempt : Nat) (ha : attempt < family.schedules lane tile) :
    retryUnit family*(1024*(7+10*tile)+128) ≤ retryFailedClock family tile lane attempt ∧
      retryFailedClock family tile lane attempt < retryUnit family*(1024*(7+10*tile)+129) := by
  have hr := retry_schedule_lt_budget family tile ht lane
  have hl := lane.isLt
  have hm : retryBudget family*lane.val+retryBudget family ≤ retryBudget family*128 := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ (by omega)
  have hoff : retryBudget family*lane.val+attempt < retryUnit family := by unfold retryUnit; omega
  have he : retryUnit family*(1024*(7+10*tile)+129) = retryUnit family*(1024*(7+10*tile)+128)+retryUnit family := by
    rw [show 1024*(7+10*tile)+129 = (1024*(7+10*tile)+128)+1 by omega,Nat.mul_add,Nat.mul_one]
  dsimp [retryFailedClock]
  omega
theorem retry_failed_before_success {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles)
    (lane : Wgmma.Lane) (attempt : Nat) (ha : attempt < family.schedules lane tile) :
    retryFailedClock family tile lane attempt < retryClock family (8+10*tile) lane := by
  apply (retry_failed_clock_bounds family tile ht lane attempt ha).2.trans_le
  apply Nat.mul_le_mul_left
  omega

theorem retry_failed_clock_lane_order {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles)
    (left right : Wgmma.Lane) (i j : Nat) (hlr : left.val < right.val) (hi : i < family.schedules left tile) :
    retryFailedClock family tile left i < retryFailedClock family tile right j := by
  have hb := retry_schedule_lt_budget family tile ht left
  have hm : retryBudget family*left.val+retryBudget family ≤ retryBudget family*right.val := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ (by omega)
  dsimp [retryFailedClock]
  omega

theorem retry_initial_clocks_length {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) :
    (retryInitialClocks family lane).length = (replyInitialEvents lane (family.replies lane)).length := by
  cases hl : HopperStage.leader lane <;> simp [retryInitialClocks,replyInitialEvents,initializationEvents,replyInitialCopies,hl]
theorem retry_iteration_clocks_length {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane) :
    (retryIterationClocks family tile lane).length =
      (replyIterationEvents tiles lane (family.replies lane) (family.schedules lane) tile).length := by
  rw [replyIterationEvents,iteration_events_length]
  simp only [retryIterationClocks,retryFailedClocks,retryPreludeClocks,retryComputeClocks,List.length_append,
    List.length_ofFn,List.length_cons,List.length_nil]
  omega
theorem retry_loop_clocks_length {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) (n : Nat) :
    (retryLoopClocks family lane n).length = (replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) n).length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) (n+1) =
        replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) n++
          replyIterationEvents tiles lane (family.replies lane) (family.schedules lane) n := by
      simp only [replyLoopEvents,loopEvents,replyIterationEvents,replyTileCheckpoint,Nat.zero_add]
    rw [retryLoopClocks,he,List.length_append,List.length_append,ih,retry_iteration_clocks_length]
theorem retry_output_clocks_length {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) :
    (retryOutputClocks family lane).length = (outputEvents (ctx tiles lane)
      (replyCheckpoint tiles lane (family.replies lane) (family.schedules lane)).1 lane (HopperStage.leader lane)
        (replyCheckpoint tiles lane (family.replies lane) (family.schedules lane)).2).length := by
  cases hl : HopperStage.leader lane <;> simp [retryOutputClocks,outputEvents,outputWriteEvents,returnEvents,hl]
theorem retry_source_clocks_length {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) :
    (retrySourceClocks family lane).length = (replyPositiveEvents tiles lane (family.replies lane) (family.schedules lane)).length := by
  simp only [retrySourceClocks,List.length_append,retry_initial_clocks_length,retry_loop_clocks_length,retry_output_clocks_length]
  simp only [replyPositiveEvents,List.length_append,replyInitialEvents,replyLoopEvents]
  omega

end
end Ptx.Kernels.HopperDoubleBuffer
