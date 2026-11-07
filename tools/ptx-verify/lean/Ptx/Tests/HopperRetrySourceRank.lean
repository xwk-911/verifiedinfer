import Ptx.Kernels.HopperDoubleBufferRetrySourceRank
import Ptx.Kernels.HopperDoubleBufferNativeRanks
import Ptx.Kernels.HopperDoubleBufferRetryNativeReuse
import Ptx.Tests.HopperRetryAdmission

/-! Retry-aware source ranks on the actual three-tile heterogeneous-retry
fixture. These tests establish actual source order and clock placement, not
resource/CTA/native combined-control acyclicity or a full memory witness. -/
namespace Ptx.HopperRetrySourceRankTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev family := HopperRetryAdmissionTests.family
abbrev candidate := HopperRetryAdmissionTests.candidate
abbrev source := HopperRetryAdmissionTests.source_well_formed

theorem finite_clock_budget (value : ℝ) : retryBudget (family value) = 1150 ∧ retryUnit (family value) = 147201 := by
  have hb : retryBudget (family value) = 1150 := by
    change 1+(∑ tile ∈ Finset.range 3, ∑ lane : Wgmma.Lane, (lane.val%3+tile+1)) = 1150
    decide
  exact ⟨hb,by rw [retryUnit,hb]⟩

theorem actual_clock_lengths (value : ℝ) :
    (retrySourceClocks (family value) 0).length = 49 ∧ (retrySourceClocks (family value) 2).length = 41 := ⟨rfl,rfl⟩

theorem actual_native_clock_positions (value : ℝ) (tile : Fin 3) (lane : Wgmma.Lane) (index : Fin 4) :
    retrySourceRank (family value) ((family value).nativeId tile lane index) = retryClock (family value) (12+10*tile.val+index.val) lane :=
  retry_native_source_rank (family value) tile tile.isLt lane index

theorem heterogeneous_native_alignment (value : ℝ) :
    retrySourceRank (family value) ((family value).nativeId 0 0 0)+2*retryUnit (family value) =
      retrySourceRank (family value) ((family value).nativeId 0 2 0) := by
  rw [retry_native_source_rank (family value) 0 (by decide) 0 0,retry_native_source_rank (family value) 0 (by decide) 2 0]
  change retryUnit (family value)*12288+2*retryUnit (family value) = retryUnit (family value)*12290
  omega

theorem old_serial_clock_is_not_aligned (value : ℝ) :
    nativeTick 3 ((family value).nativeId 0 0 0) ≠ nativeTick 3 ((family value).nativeId 0 2 0) := by
  change producerTick 3 13 ≠ peerTick 3 6
  decide

theorem actual_failed_before_success (value : ℝ) (tile : Fin 3) (lane : Wgmma.Lane) (attempt : Fin ((family value).schedules lane tile)) :
    retrySourceRank (family value) ((family value).failedWaitId tile lane attempt) <
      retrySourceRank (family value) ((family value).waitId tile lane) := by
  rw [retry_failed_wait_source_rank (family value) tile tile.isLt lane attempt attempt.isLt,
    retry_successful_wait_source_rank (family value) tile tile.isLt lane]
  exact retry_failed_before_success (family value) tile tile.isLt lane attempt attempt.isLt

theorem actual_cross_lane_failed_order (value : ℝ) (tile : Fin 3) (left right : Wgmma.Lane) (hlr : left.val < right.val)
    (i : Fin ((family value).schedules left tile)) (j : Fin ((family value).schedules right tile)) :
    retrySourceRank (family value) ((family value).failedWaitId tile left i) <
      retrySourceRank (family value) ((family value).failedWaitId tile right j) := by
  rw [retry_failed_wait_source_rank (family value) tile tile.isLt left i i.isLt,
    retry_failed_wait_source_rank (family value) tile tile.isLt right j j.isLt]
  exact retry_failed_clock_lane_order (family value) tile tile.isLt left right i j hlr i.isLt

theorem actual_reuse_source_order (value : ℝ) :
    retrySourceRank (family value) ((family value).nativeWaitId 0 0) <
      retrySourceRank (family value) ((family value).copyAId 2).issue := by
  apply retry_source_program_order (family value) (source value (fun _ => .bits (byte 0)))
  refine ⟨?_,?_,rfl,(retry_native_wait_before_later_copy_serial (family value) 0 2 (by decide)).1⟩
  · simp only [Hopper.Candidate.Present,Unified.view_eventAt,
      family_native_wait_at (family value) (source value (fun _ => .bits (byte 0))) (by decide) 0 (by decide) 0,Option.map_some,Option.isSome_some]
  · have he := Tma.copyAt_iff.mp (family_copy_a_at (family value) (source value (fun _ => .bits (byte 0))) 2 (by decide))
    simp only [Hopper.Candidate.Present,he,Option.isSome_some]

theorem source_only_cycles_rejected (value : ℝ) (id : Ptx.Event.EventId) :
    ¬Ptx.Event.Path (Hopper.ProgramOrder (candidate value).view) id id := by
  intro hcycle
  have hh := hcycle.rank_lt (retrySourceRank (family value))
    (fun _ _ => retry_source_program_order (family value) (source value (fun _ => .bits (byte 0))))
  omega

end
end Ptx.HopperRetrySourceRankTests
