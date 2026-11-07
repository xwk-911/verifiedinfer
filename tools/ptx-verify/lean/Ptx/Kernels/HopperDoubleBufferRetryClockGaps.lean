import Ptx.Kernels.HopperDoubleBufferRetrySourceRank

/-! Actual source clocks leave a lane-independent gap before native arrival.
The gap follows from the finite retry clock shape, not an extra source-order
or readiness premise. Failed waits keep their actual bounded ordinals. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def RetryClockShape {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (lane : Wgmma.Lane) (value : Nat) : Prop :=
  (∃ tick, value = retryClock family tick lane) ∨
    ∃ tile attempt, tile < tiles ∧ attempt < family.schedules lane tile ∧
      value = retryFailedClock family tile lane attempt

theorem retry_iteration_clock_shape {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane) (value : Nat)
    (hv : value ∈ retryIterationClocks family tile lane) : RetryClockShape family lane value := by
  simp only [retryIterationClocks,List.mem_append,List.mem_singleton] at hv
  rcases hv with ((hf | rfl) | hp) | hc
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
    exact .inr ⟨tile,i.val,ht,i.isLt,rfl⟩
  · exact .inl ⟨_,rfl⟩
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact .inl ⟨_,rfl⟩
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    exact .inl ⟨_,rfl⟩

theorem retry_source_clock_shape {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (lane : Wgmma.Lane) (value : Nat) (hv : value ∈ retrySourceClocks family lane) :
    RetryClockShape family lane value := by
  simp only [retrySourceClocks,List.mem_append] at hv
  rcases hv with (hi | hl) | ho
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hi
    exact .inl ⟨_,rfl⟩
  · obtain ⟨tile,ht,hv⟩ := retry_loop_clock_case family lane tiles value hl
    exact retry_iteration_clock_shape family tile ht lane value hv
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ho
    exact .inl ⟨_,rfl⟩

theorem retry_clock_gap {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (lane : Wgmma.Lane) (value target : Nat) (hs : RetryClockShape family lane value)
    (hlt : value < retryClock family target lane) : value < retryUnit family*(1024*target) := by
  have hl := lane.isLt
  rcases hs with ⟨tick,rfl⟩ | ⟨tile,attempt,ht,ha,rfl⟩
  · have hi : 1024*tick+lane.val < 1024*target+lane.val := Nat.lt_of_mul_lt_mul_left hlt
    apply Nat.mul_lt_mul_of_pos_left _ (retry_unit_pos family)
    omega
  · have hb := retry_failed_clock_bounds family tile ht lane attempt ha
    have htarget : 7+10*tile < target := by
      by_contra hn
      have hm : retryClock family target lane ≤ retryUnit family*(1024*(7+10*tile)+128) :=
        Nat.mul_le_mul_left _ (by omega)
      exact (hm.trans hb.1).not_gt hlt
    exact hb.2.trans_le (Nat.mul_le_mul_left _ (by omega))

theorem retry_present_source_rank_member {tiles initial candidate id} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hp : candidate.view.Present id) :
    retrySourceRank family id ∈ retrySourceClocks family (retryRankLane id) := by
  have hi := retry_present_source_clock_bound family hw hp
  simp only [retrySourceRank,List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi

theorem retry_before_native_clock_gap {tiles initial candidate before} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane) (index : Fin 4)
    (hp : Hopper.ProgramOrder candidate.view before (family.nativeId tile lane index)) :
    retrySourceRank family before < retryUnit family*(1024*(12+10*tile+index.val)) := by
  have ho := retry_source_program_order family hw hp
  rw [retry_native_source_rank family tile ht lane index] at ho
  have hl : retryRankLane before = lane := retry_rank_lane_of_thread (tiles := tiles) hp.2.2.1
  have hm := retry_present_source_rank_member family hw hp.1
  rw [hl] at hm
  exact retry_clock_gap family lane _ _ (retry_source_clock_shape family lane _ hm) ho

end
end Ptx.Kernels.HopperDoubleBuffer
