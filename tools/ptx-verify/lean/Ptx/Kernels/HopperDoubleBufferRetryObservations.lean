import Ptx.Kernels.HopperDoubleBufferRetryPhasePrefixes

/-! Completion observations in constructed actual-origin retry histories.
Full phase/lifetime stamps, rather than parity alone, reject reused-slot old
notifications. HistoryValid and control/memory admission are still separate. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_phase_take_no_initialization {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase index) :
    ((retryPhaseEntries family slot phase).take index).filter isInitialization = [] := by
  have hh := List.filter_eq_nil_iff.mp (retry_phase_no_initialization family slot phase)
  exact List.filter_eq_nil_iff.mpr (fun entry he => hh entry (List.mem_of_mem_take he))

theorem retry_phase_lifetime {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (hp : phase < uses tiles slot)
    (index : Nat) (hi : index ≤ (retryPhaseEntries family slot phase).length) :
    Tma.lifetimeBefore (retryResourceHistory family slot) (retryPhaseStart family slot phase+index) = 1 := by
  change (((retryResourceHistory family slot).take (retryPhaseStart family slot phase+index)).filter isInitialization).length = 1
  rw [retry_history_take family slot phase hp index hi,List.filter_append,List.filter_append,
    retry_phases_no_initialization,retry_phase_take_no_initialization]
  rfl

theorem retry_notice_a_prefix {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (hp : phase < uses tiles slot) :
    Mbarrier.run none (((retryResourceHistory family slot).map Tma.Entry.operation).take (retryNoticeAIndex family slot phase)) =
      some (some (awaitingTransfer phase 2304)) := by
  have he : retryNoticeAIndex family slot phase = retryPhaseStart family slot phase+
      (1+(retryFailedEntries family (stageTile slot phase)).length+0) := by unfold retryNoticeAIndex; omega
  rw [← List.map_take,he,retry_history_take family slot phase hp _ (by rw [retry_phase_length]; omega),
    retry_phase_take_notifications family slot phase 0 (by decide)]
  simp only [List.take_zero,List.append_nil]
  rw [List.map_append,Mbarrier.run_append,retry_history_prefix_run,Option.bind_some]
  simp only [List.map_append,List.map_cons,List.map_nil,Mbarrier.run_append,
    retry_arrival_run,Option.bind_some,retry_failed_run]

theorem retry_notice_b_prefix {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (hp : phase < uses tiles slot) :
    Mbarrier.run none (((retryResourceHistory family slot).map Tma.Entry.operation).take (retryNoticeBIndex family slot phase)) =
      some (some (awaitingTransfer phase 256)) := by
  have he : retryNoticeBIndex family slot phase = retryPhaseStart family slot phase+
      (1+(retryFailedEntries family (stageTile slot phase)).length+1) := by unfold retryNoticeBIndex retryNoticeAIndex; omega
  rw [← List.map_take,he,retry_history_take family slot phase hp _ (by rw [retry_phase_length]; omega),
    retry_phase_take_notifications family slot phase 1 (by decide)]
  simp only [List.take_succ_cons,List.take_zero]
  rw [List.map_append,Mbarrier.run_append,retry_history_prefix_run,Option.bind_some]
  simp only [List.map_append,List.map_cons,List.map_nil,Mbarrier.run_append,
    retry_arrival_run,Option.bind_some,retry_failed_run]
  simp [Mbarrier.run,Mbarrier.step,Mbarrier.accept,Mbarrier.WellFormed,Mbarrier.finish,Mbarrier.limit,awaitingTransfer]

theorem retry_notice_a_stamp {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (hp : phase < uses tiles slot) :
    Tma.stampBefore (retryResourceHistory family slot) (retryNoticeAIndex family slot phase) = some ⟨1,phase⟩ := by
  rw [Tma.stampBefore,retry_notice_a_prefix family slot phase hp]
  have hl : Tma.lifetimeBefore (retryResourceHistory family slot) (retryNoticeAIndex family slot phase) = 1 := by
    rw [retryNoticeAIndex,Nat.add_assoc]
    exact retry_phase_lifetime family slot phase hp _ (by rw [retry_phase_length]; omega)
  rw [hl]
  rfl

theorem retry_notice_b_stamp {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (hp : phase < uses tiles slot) :
    Tma.stampBefore (retryResourceHistory family slot) (retryNoticeBIndex family slot phase) = some ⟨1,phase⟩ := by
  rw [Tma.stampBefore,retry_notice_b_prefix family slot phase hp]
  have hl : Tma.lifetimeBefore (retryResourceHistory family slot) (retryNoticeBIndex family slot phase) = 1 := by
    have he : retryNoticeBIndex family slot phase = retryPhaseStart family slot phase+
        (2+(retryFailedEntries family (stageTile slot phase)).length) := by unfold retryNoticeBIndex retryNoticeAIndex; omega
    rw [he]
    exact retry_phase_lifetime family slot phase hp _ (by rw [retry_phase_length]; omega)
  rw [hl]
  rfl

theorem retry_wait_stamp {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (hp : phase < uses tiles slot) (lane : Wgmma.Lane) :
    Tma.stampBefore (retryResourceHistory family slot) (retryPhaseWaitIndex family slot phase lane) = some ⟨1,phase+1⟩ := by
  rw [Tma.stampBefore,retry_history_wait_prefix family slot phase hp lane]
  have hl : Tma.lifetimeBefore (retryResourceHistory family slot) (retryPhaseWaitIndex family slot phase lane) = 1 := by
    have he : retryPhaseWaitIndex family slot phase lane = retryPhaseStart family slot phase+
        (3+(retryFailedEntries family (stageTile slot phase)).length+lane.val) := by unfold retryPhaseWaitIndex retryNoticeAIndex; omega
    rw [he]
    exact retry_phase_lifetime family slot phase hp _ (by rw [retry_phase_length]; have := lane.isLt; omega)
  rw [hl]
  by_cases hz : lane.val = 0 <;> simp [hz,transferredState,readyState]

theorem retry_observe_a {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (hp : phase < uses tiles slot) (lane : Wgmma.Lane) :
    Tma.observation (retryResourceHistory family slot) (retryNoticeAIndex family slot phase) (retryPhaseWaitIndex family slot phase lane) =
      some (family.copyAId (stageTile slot phase),family.waitId (stageTile slot phase) lane) := by
  rw [Tma.observation,retry_history_notice_a_at family slot phase hp,retry_history_wait_at family slot phase hp lane]
  simp only [bind,Option.bind,Tma.noticeCopy,Tma.waitEvent]
  rw [retry_notice_a_stamp family slot phase hp,retry_wait_stamp family slot phase hp lane]
  dsimp only
  rw [ite_eq_left (by simp [retryPhaseWaitIndex]; omega)]

theorem retry_observe_b {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (hp : phase < uses tiles slot) (lane : Wgmma.Lane) :
    Tma.observation (retryResourceHistory family slot) (retryNoticeBIndex family slot phase) (retryPhaseWaitIndex family slot phase lane) =
      some (family.copyBId (stageTile slot phase),family.waitId (stageTile slot phase) lane) := by
  rw [Tma.observation,retry_history_notice_b_at family slot phase hp,retry_history_wait_at family slot phase hp lane]
  simp only [bind,Option.bind,Tma.noticeCopy,Tma.waitEvent]
  rw [retry_notice_b_stamp family slot phase hp,retry_wait_stamp family slot phase hp lane]
  dsimp only
  rw [ite_eq_left (by simp [retryNoticeBIndex,retryPhaseWaitIndex]; omega)]

theorem retry_other_a_phase_not_observed {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot old current)
    (ho : old < uses tiles slot) (hc : current < uses tiles slot) (hne : old ≠ current) (lane : Wgmma.Lane) :
    Tma.observation (retryResourceHistory family slot) (retryNoticeAIndex family slot old) (retryPhaseWaitIndex family slot current lane) = none := by
  rw [Tma.observation,retry_history_notice_a_at family slot old ho,retry_history_wait_at family slot current hc lane]
  simp only [bind,Option.bind,Tma.noticeCopy,Tma.waitEvent]
  rw [retry_notice_a_stamp family slot old ho,retry_wait_stamp family slot current hc lane]
  dsimp only
  rw [ite_eq_right (by simp; omega)]

theorem retry_other_b_phase_not_observed {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot old current)
    (ho : old < uses tiles slot) (hc : current < uses tiles slot) (hne : old ≠ current) (lane : Wgmma.Lane) :
    Tma.observation (retryResourceHistory family slot) (retryNoticeBIndex family slot old) (retryPhaseWaitIndex family slot current lane) = none := by
  rw [Tma.observation,retry_history_notice_b_at family slot old ho,retry_history_wait_at family slot current hc lane]
  simp only [bind,Option.bind,Tma.noticeCopy,Tma.waitEvent]
  rw [retry_notice_b_stamp family slot old ho,retry_wait_stamp family slot current hc lane]
  dsimp only
  rw [ite_eq_right (by simp; omega)]

/-- Constructed histories for arbitrary completed source candidates. This
does not assert unique/exhaustive/ordered HistoryValid or full admission. -/
theorem completed_candidate_retry_histories {tiles initial candidate} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) :
    ∃ family : ReplySourceFamily tiles candidate,
      (∀ slot, Mbarrier.run none ((retryResourceHistory family slot).map Tma.Entry.operation) = some none) ∧
      (∀ slot entry, entry ∈ retryResourceHistory family slot →
        Tma.resourceAt Tma.localShared candidate.view entry.origin = some ⟨dataGate slot,entry.operation⟩) ∧
      (∀ slot phase, phase < uses tiles slot → ∀ lane,
        Tma.observation (retryResourceHistory family slot) (retryNoticeAIndex family slot phase) (retryPhaseWaitIndex family slot phase lane) =
          some (family.copyAId (stageTile slot phase),family.waitId (stageTile slot phase) lane) ∧
        Tma.observation (retryResourceHistory family slot) (retryNoticeBIndex family slot phase) (retryPhaseWaitIndex family slot phase lane) =
          some (family.copyBId (stageTile slot phase),family.waitId (stageTile slot phase) lane)) := by
  obtain ⟨family⟩ := completed_candidate_reply_family ht hb hw hc
  exact ⟨family,retry_history_protocol family,retry_history_entry_sound family hw hd,
    fun slot phase hp lane => ⟨retry_observe_a family slot phase hp lane,retry_observe_b family slot phase hp lane⟩⟩

end
end Ptx.Kernels.HopperDoubleBuffer
