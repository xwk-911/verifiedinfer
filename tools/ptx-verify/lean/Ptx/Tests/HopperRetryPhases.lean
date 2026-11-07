import Ptx.Kernels.HopperDoubleBufferRetryObservations
import Ptx.Tests.HopperRetryPrefetch

/-! Multi-tile nonzero-retry histories: actual-origin soundness, unbounded
phase rules instantiated on both arenas and reuse, and old-phase rejection.
No HistoryValid, memory/tensor admission or hardware verdict is asserted. -/
namespace Ptx.HopperRetryPhasesTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev family := HopperRetryPrefetchTests.family
abbrev candidate := HopperRetryPrefetchTests.candidate

theorem three_tile_failed_counts (value : ℝ) :
    (retryFailedEntries (family value) 0).length = 255 ∧ (retryFailedEntries (family value) 1).length = 383 ∧
      (retryFailedEntries (family value) 2).length = 511 := by
  simp only [retry_failed_entries_length]
  change (List.ofFn (fun lane : Wgmma.Lane => HopperRetryPrefetchTests.schedule lane 0)).sum = 255 ∧
    (List.ofFn (fun lane : Wgmma.Lane => HopperRetryPrefetchTests.schedule lane 1)).sum = 383 ∧
    (List.ofFn (fun lane : Wgmma.Lane => HopperRetryPrefetchTests.schedule lane 2)).sum = 511
  decide

theorem three_tile_history_lengths (value : ℝ) :
    (retryResourceHistory (family value) 0).length = 1030 ∧ (retryResourceHistory (family value) 1).length = 516 := by
  have hf := three_tile_failed_counts value
  simp only [retryResourceHistory,List.length_append,List.length_cons,List.length_nil,
    show uses 3 0 = 2 from by decide,show uses 3 1 = 1 from by decide,retry_phases_length_succ]
  change 1+(0+131+(retryFailedEntries (family value) 0).length+131+(retryFailedEntries (family value) 2).length)+1 = 1030 ∧
    1+(0+131+(retryFailedEntries (family value) 1).length)+1 = 516
  omega

theorem three_tile_phase_positions (value : ℝ) :
    retryNoticeAIndex (family value) 0 0 = 257 ∧ retryNoticeBIndex (family value) 0 0 = 258 ∧
    retryNoticeAIndex (family value) 0 1 = 899 ∧ retryNoticeBIndex (family value) 0 1 = 900 ∧
    retryNoticeAIndex (family value) 1 0 = 385 := by
  have hf := three_tile_failed_counts value
  simp only [retryNoticeAIndex,retryNoticeBIndex,retryPhaseStart,retry_phases_length_succ]
  change 1+0+1+(retryFailedEntries (family value) 0).length = 257 ∧
    1+0+1+(retryFailedEntries (family value) 0).length+1 = 258 ∧
    1+(0+131+(retryFailedEntries (family value) 0).length)+1+(retryFailedEntries (family value) 2).length = 899 ∧
    1+(0+131+(retryFailedEntries (family value) 0).length)+1+(retryFailedEntries (family value) 2).length+1 = 900 ∧
    1+0+1+(retryFailedEntries (family value) 1).length = 385
  omega

theorem both_histories_protocol (value : ℝ) (slot : Stage) :
    Mbarrier.run none ((retryResourceHistory (family value) slot).map Tma.Entry.operation) = some none :=
  retry_history_protocol (family value) slot

theorem actual_a_notifications (value : ℝ) (tile : Fin 3) :
    Tma.resourceAt Tma.localShared (candidate value).view (.notification ((family value).copyAId tile)) =
      some ⟨dataGate (stage tile),.completeTx 2048⟩ := by
  rw [Tma.resourceAt,Tma.notification,HopperRetryPrefetchTests.actual_a_copies value tile]
  fin_cases tile <;> rfl

theorem actual_b_notifications (value : ℝ) (tile : Fin 3) :
    Tma.resourceAt Tma.localShared (candidate value).view (.notification ((family value).copyBId tile)) =
      some ⟨dataGate (stage tile),.completeTx 256⟩ := by
  rw [Tma.resourceAt,Tma.notification,HopperRetryPrefetchTests.actual_b_copies value tile]
  fin_cases tile <;> rfl

theorem actual_phase_resources (value : ℝ) (slot : Stage) (phase : Nat) (hp : phase < uses 3 slot)
    (entry : Tma.Entry) (he : entry ∈ retryPhaseEntries (family value) slot phase) :
    Tma.resourceAt Tma.localShared (candidate value).view entry.origin = some ⟨dataGate slot,entry.operation⟩ := by
  have hw := HopperRetryPrefetchTests.source_well_formed value (fun _ => .bits (byte 0))
  have ht := (stage_tile_in_range 3 slot phase).mpr hp
  simp only [retryPhaseEntries,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with ((rfl | he) | (rfl | rfl)) | he
  · simpa only [Tma.resourceAt,stage_tile_slot,dataGate] using family_expect_at (family value) hw _ ht
  · obtain ⟨lane,attempt,rfl⟩ := (retry_failed_entry (family value) _ _).mp he
    apply Hopper.barrierAt_iff.mpr
    apply Unified.view_barrier_iff.mpr
    simpa only [stage_tile_slot,stage_tile_phase,dataGate,waitEvent,ctx,HopperStage.ctx] using
      family_failed_wait_at (family value) hw _ ht lane attempt attempt.isLt
  · simpa only [stage_tile_slot] using actual_a_notifications value ⟨_,ht⟩
  · simpa only [stage_tile_slot] using actual_b_notifications value ⟨_,ht⟩
  · obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp he
    apply Hopper.barrierAt_iff.mpr
    apply Unified.view_barrier_iff.mpr
    simpa only [stage_tile_slot,dataGate,waitEvent,ctx,HopperStage.ctx] using family_wait_at (family value) hw _ ht lane

theorem actual_history_resources (value : ℝ) (slot : Stage) (entry : Tma.Entry)
    (he : entry ∈ retryResourceHistory (family value) slot) :
    Tma.resourceAt Tma.localShared (candidate value).view entry.origin = some ⟨dataGate slot,entry.operation⟩ := by
  have hw := HopperRetryPrefetchTests.source_well_formed value (fun _ => .bits (byte 0))
  simp only [retryResourceHistory,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with (rfl | he) | rfl
  · exact family_init_at (family value) hw slot
  · obtain ⟨phase,hp,he⟩ := (retry_phases_entry (family value) slot _ entry).mp he
    exact actual_phase_resources value slot phase hp entry he
  · exact family_inval_at (family value) hw slot

theorem entries_belong_to_actual_inventory (value : ℝ) (slot : Stage) (entry : Tma.Entry)
    (he : entry ∈ retryResourceHistory (family value) slot) :
    entry ∈ Tma.inventory Tma.localShared (candidate value).view (dataGate slot) :=
  Tma.inventory_iff.mpr (actual_history_resources value slot entry he)

theorem initial_a_observed (value : ℝ) (lane : Wgmma.Lane) :
    Tma.observation (retryResourceHistory (family value) 0) (retryNoticeAIndex (family value) 0 0)
      (retryPhaseWaitIndex (family value) 0 0 lane) = some ((family value).copyAId 0,(family value).waitId 0 lane) :=
  retry_observe_a (family value) 0 0 (by decide) lane

theorem other_arena_b_observed (value : ℝ) (lane : Wgmma.Lane) :
    Tma.observation (retryResourceHistory (family value) 1) (retryNoticeBIndex (family value) 1 0)
      (retryPhaseWaitIndex (family value) 1 0 lane) = some ((family value).copyBId 1,(family value).waitId 1 lane) :=
  retry_observe_b (family value) 1 0 (by decide) lane

theorem reused_arena_a_observed (value : ℝ) (lane : Wgmma.Lane) :
    Tma.observation (retryResourceHistory (family value) 0) (retryNoticeAIndex (family value) 0 1)
      (retryPhaseWaitIndex (family value) 0 1 lane) = some ((family value).copyAId 2,(family value).waitId 2 lane) :=
  retry_observe_a (family value) 0 1 (by decide) lane

theorem reused_arena_b_observed (value : ℝ) (lane : Wgmma.Lane) :
    Tma.observation (retryResourceHistory (family value) 0) (retryNoticeBIndex (family value) 0 1)
      (retryPhaseWaitIndex (family value) 0 1 lane) = some ((family value).copyBId 2,(family value).waitId 2 lane) :=
  retry_observe_b (family value) 0 1 (by decide) lane

theorem initial_a_cannot_satisfy_reuse (value : ℝ) (lane : Wgmma.Lane) :
    Tma.observation (retryResourceHistory (family value) 0) (retryNoticeAIndex (family value) 0 0)
      (retryPhaseWaitIndex (family value) 0 1 lane) = none :=
  retry_other_a_phase_not_observed (family value) 0 0 1 (by decide) (by decide) (by decide) lane

theorem initial_b_cannot_satisfy_reuse (value : ℝ) (lane : Wgmma.Lane) :
    Tma.observation (retryResourceHistory (family value) 0) (retryNoticeBIndex (family value) 0 0)
      (retryPhaseWaitIndex (family value) 0 1 lane) = none :=
  retry_other_b_phase_not_observed (family value) 0 0 1 (by decide) (by decide) (by decide) lane

theorem parity_wrap_does_not_restore_old_observation {candidate} (family : ReplySourceFamily 5 candidate) (lane : Wgmma.Lane) :
    expectedParity (stageTile 0 0) = expectedParity (stageTile 0 2) ∧
    Tma.observation (retryResourceHistory family 0) (retryNoticeAIndex family 0 0)
      (retryPhaseWaitIndex family 0 2 lane) = none :=
  ⟨by decide,retry_other_a_phase_not_observed family 0 0 2 (by decide) (by decide) (by decide) lane⟩

end
end Ptx.HopperRetryPhasesTests
