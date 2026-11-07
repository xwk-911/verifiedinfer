import Ptx.Kernels.HopperDoubleBufferRetryControlClock

/-! Strict source-clock order across arbitrary finite retry blocks. The global
retry budget bounds every failed-wait ordinal; fixed stage gaps accommodate
all lanes and leave notification slots without changing the source program. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_clock_interval {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane)
    (tick lo hi : Nat) (hlo : lo ≤ tick) (hhi : tick ≤ hi) :
    retryUnit family*(1024*lo) ≤ retryClock family tick lane ∧ retryClock family tick lane ≤ retryUnit family*(1024*hi+127) := by
  have hl := lane.isLt
  constructor <;> apply Nat.mul_le_mul_left <;> omega

theorem retry_initial_clocks_strict {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) :
    (retryInitialClocks family lane).Pairwise (· < ·) := by
  apply List.pairwise_ofFn.mpr
  intro left right hlr
  apply retry_clock_strict family lane
  omega
theorem retry_failed_clocks_strict {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane) :
    (retryFailedClocks family tile lane).Pairwise (· < ·) := by
  apply List.pairwise_ofFn.mpr
  intro left right hlr
  dsimp [retryFailedClock]
  omega
theorem retry_prelude_clocks_strict {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane) :
    (retryPreludeClocks family tile lane).Pairwise (· < ·) := by
  apply List.pairwise_ofFn.mpr
  intro left right hlr
  apply retry_clock_strict family lane
  omega
theorem retry_compute_clocks_strict {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane) :
    (retryComputeClocks family tile lane).Pairwise (· < ·) := by
  apply List.pairwise_ofFn.mpr
  intro left right hlr
  apply retry_clock_strict family lane
  omega
theorem retry_prelude_count_le (tile tiles leader) : preludeEventCount tile tiles leader ≤ 3 := by
  unfold preludeEventCount
  split_ifs <;> omega

theorem retry_iteration_clocks_strict {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane) :
    (retryIterationClocks family tile lane).Pairwise (· < ·) := by
  have hprefix : (retryFailedClocks family tile lane++[retryClock family (8+10*tile) lane]).Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨retry_failed_clocks_strict family tile lane,by simp,?_⟩
    intro left hl right hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
    have he : right = retryClock family (8+10*tile) lane := List.mem_singleton.mp hr
    rw [he]
    exact retry_failed_before_success family tile ht lane i.val i.isLt
  have hsuffix : (retryPreludeClocks family tile lane++retryComputeClocks family tile lane).Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨retry_prelude_clocks_strict family tile lane,retry_compute_clocks_strict family tile lane,?_⟩
    intro left hl right hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    have hi := i.isLt
    have hb := retry_prelude_count_le tile tiles (HopperStage.leader lane)
    apply retry_clock_strict family lane
    omega
  have heq : retryIterationClocks family tile lane =
      (retryFailedClocks family tile lane++[retryClock family (8+10*tile) lane])++
        (retryPreludeClocks family tile lane++retryComputeClocks family tile lane) := by simp only [retryIterationClocks,List.append_assoc]
  rw [heq]
  apply List.pairwise_append.mpr
  refine ⟨hprefix,hsuffix,?_⟩
  intro left hl right hr
  have hleft : left ≤ retryClock family (8+10*tile) lane := by
    rcases List.mem_append.mp hl with hf | hs
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
      exact (retry_failed_before_success family tile ht lane i.val i.isLt).le
    · exact (List.mem_singleton.mp hs).le
  have hright : retryClock family (9+10*tile) lane ≤ right := by
    rcases List.mem_append.mp hr with hp | hc
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
      exact retry_clock_mono family lane (by omega)
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
      exact retry_clock_mono family lane (by omega)
  exact hleft.trans_lt ((retry_clock_strict family lane (by omega : 8+10*tile < 9+10*tile)).trans_le hright)

theorem retry_initial_clock_bounds {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) (value : Nat)
    (hv : value ∈ retryInitialClocks family lane) : value ≤ retryUnit family*(1024*7+127) := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
  have hi := i.isLt
  have ht : i.val+(if HopperStage.leader lane then 0 else 3) ≤ 7 := by
    have aux (leader : Bool) (j : Nat) (hj : j < if leader then 8 else 2) : j+(if leader then 0 else 3) ≤ 7 := by
      cases leader <;> simp_all <;> omega
    exact aux (HopperStage.leader lane) i.val hi
  exact (retry_clock_interval family lane _ 0 7 (Nat.zero_le _) ht).2

theorem retry_iteration_clock_bounds {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles)
    (lane : Wgmma.Lane) (value : Nat) (hv : value ∈ retryIterationClocks family tile lane) :
    retryUnit family*(1024*(7+10*tile)+128) ≤ value ∧ value ≤ retryUnit family*(1024*(17+10*tile)+127) := by
  simp only [retryIterationClocks,List.mem_append,List.mem_singleton] at hv
  rcases hv with ((hf | rfl) | hp) | hc
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
    have hb := retry_failed_clock_bounds family tile ht lane i.val i.isLt
    refine ⟨hb.1,hb.2.le.trans ?_⟩
    apply Nat.mul_le_mul_left
    omega
  · constructor <;> apply Nat.mul_le_mul_left <;> have hl := lane.isLt <;> omega
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    have hi := i.isLt
    have hb := retry_prelude_count_le tile tiles (HopperStage.leader lane)
    constructor <;> apply Nat.mul_le_mul_left <;> have hl := lane.isLt <;> omega
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    have hi := i.isLt
    constructor <;> apply Nat.mul_le_mul_left <;> have hl := lane.isLt <;> omega

theorem retry_loop_clock_case {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) (n value : Nat)
    (hv : value ∈ retryLoopClocks family lane n) : ∃ tile < n, value ∈ retryIterationClocks family tile lane := by
  induction n with
  | zero => cases hv
  | succ n ih =>
    rcases List.mem_append.mp hv with hold | hlast
    · obtain ⟨tile,ht,hv⟩ := ih hold
      exact ⟨tile,by omega,hv⟩
    · exact ⟨n,by omega,hlast⟩

theorem retry_loop_clocks_strict {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) (n : Nat) (hn : n ≤ tiles) :
    (retryLoopClocks family lane n).Pairwise (· < ·) := by
  induction n with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    apply List.pairwise_append.mpr
    refine ⟨ih (by omega),retry_iteration_clocks_strict family n (by omega) lane,?_⟩
    intro left hl right hr
    obtain ⟨tile,ht,hv⟩ := retry_loop_clock_case family lane n left hl
    have hb := retry_iteration_clock_bounds family tile (by omega) lane left hv
    have hc := retry_iteration_clock_bounds family n (by omega) lane right hr
    have hg : retryUnit family*(1024*(17+10*tile)+127) < retryUnit family*(1024*(7+10*n)+128) :=
      Nat.mul_lt_mul_of_pos_left (by omega) (retry_unit_pos family)
    exact hb.2.trans_lt (hg.trans_le hc.1)

theorem retry_output_clocks_strict {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) :
    (retryOutputClocks family lane).Pairwise (· < ·) := by
  apply List.pairwise_ofFn.mpr
  intro left right hlr
  apply retry_clock_strict family lane
  omega
theorem retry_output_clock_lower {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) (value : Nat)
    (hv : value ∈ retryOutputClocks family lane) : retryUnit family*(1024*(8+10*tiles)) ≤ value := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
  exact (retry_clock_interval family lane _ (8+10*tiles) _ (by omega) (Nat.le_refl _)).1

theorem retry_source_clocks_strict {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) :
    (retrySourceClocks family lane).Pairwise (· < ·) := by
  have hprefix : (retryInitialClocks family lane++retryLoopClocks family lane tiles).Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨retry_initial_clocks_strict family lane,retry_loop_clocks_strict family lane tiles (Nat.le_refl _),?_⟩
    intro left hl right hr
    obtain ⟨tile,ht,hv⟩ := retry_loop_clock_case family lane tiles right hr
    have hb := retry_initial_clock_bounds family lane left hl
    have hc := retry_iteration_clock_bounds family tile ht lane right hv
    have hg : retryUnit family*(1024*7+127) < retryUnit family*(1024*(7+10*tile)+128) :=
      Nat.mul_lt_mul_of_pos_left (by omega) (retry_unit_pos family)
    exact hb.trans_lt (hg.trans_le hc.1)
  apply List.pairwise_append.mpr
  refine ⟨hprefix,retry_output_clocks_strict family lane,?_⟩
  intro left hl right hr
  have hright := retry_output_clock_lower family lane right hr
  rcases List.mem_append.mp hl with hi | hlo
  · have hb := retry_initial_clock_bounds family lane left hi
    have hg : retryUnit family*(1024*7+127) < retryUnit family*(1024*(8+10*tiles)) :=
      Nat.mul_lt_mul_of_pos_left (by omega) (retry_unit_pos family)
    exact hb.trans_lt (hg.trans_le hright)
  · obtain ⟨tile,ht,hv⟩ := retry_loop_clock_case family lane tiles left hlo
    have hb := retry_iteration_clock_bounds family tile ht lane left hv
    have hg : retryUnit family*(1024*(17+10*tile)+127) < retryUnit family*(1024*(8+10*tiles)) :=
      Nat.mul_lt_mul_of_pos_left (by omega) (retry_unit_pos family)
    exact hb.2.trans_lt (hg.trans_le hright)

end
end Ptx.Kernels.HopperDoubleBuffer
