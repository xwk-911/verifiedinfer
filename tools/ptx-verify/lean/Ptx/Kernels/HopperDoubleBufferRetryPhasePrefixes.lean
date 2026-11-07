import Ptx.Kernels.HopperDoubleBufferRetryPhases

/-! Variable-length prefixes for actual retry histories. Positions are local
resource-history indices, distinct from source event serial numbers. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def retryPhaseStart {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot : Stage) (phase : Nat) : Nat :=
  1+(retryPhases family slot phase).length
def retryNoticeAIndex {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot : Stage) (phase : Nat) : Nat :=
  retryPhaseStart family slot phase+1+(retryFailedEntries family (stageTile slot phase)).length
def retryNoticeBIndex {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot : Stage) (phase : Nat) : Nat :=
  retryNoticeAIndex family slot phase+1
def retryPhaseWaitIndex {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot : Stage) (phase : Nat) (lane : Wgmma.Lane) : Nat :=
  retryNoticeAIndex family slot phase+2+lane.val

theorem retry_phases_split {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot) (m n : Nat) (hm : m ≤ n) :
    ∃ rest, retryPhases family slot n = retryPhases family slot m++rest := by
  induction n with
  | zero =>
    have he : m = 0 := by omega
    subst m
    exact ⟨[],rfl⟩
  | succ n ih =>
    by_cases he : m = n+1
    · exact ⟨[],by simp only [he,List.append_nil]⟩
    · obtain ⟨rest,hr⟩ := ih (by omega)
      exact ⟨rest++retryPhaseEntries family slot n,by rw [retryPhases,hr,List.append_assoc]⟩

theorem retry_history_split_phase {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (hp : phase < uses tiles slot) :
    ∃ rest, retryResourceHistory family slot =
      (([⟨.source (family.initId slot),.init 1⟩] : List Tma.Entry)++retryPhases family slot phase)++
        retryPhaseEntries family slot phase++rest := by
  obtain ⟨rest,hr⟩ := retry_phases_split family slot (phase+1) (uses tiles slot) (by omega)
  refine ⟨rest++[⟨.source (family.invalId slot),.inval⟩],?_⟩
  simp only [retryResourceHistory,hr,retryPhases,List.append_assoc]

theorem retry_history_take {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (hp : phase < uses tiles slot)
    (index : Nat) (hi : index ≤ (retryPhaseEntries family slot phase).length) :
    (retryResourceHistory family slot).take (retryPhaseStart family slot phase+index) =
      (([⟨.source (family.initId slot),.init 1⟩] : List Tma.Entry)++retryPhases family slot phase)++
        (retryPhaseEntries family slot phase).take index := by
  obtain ⟨rest,hr⟩ := retry_history_split_phase family slot phase hp
  have hl : (([⟨.source (family.initId slot),.init 1⟩] : List Tma.Entry)++retryPhases family slot phase).length =
      retryPhaseStart family slot phase := by simp [retryPhaseStart,Nat.add_comm]
  rw [hr,← hl]
  exact take_within_middle _ _ _ index hi

theorem retry_history_phase_at {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (hp : phase < uses tiles slot)
    (index : Nat) (hi : index < (retryPhaseEntries family slot phase).length) :
    (retryResourceHistory family slot)[retryPhaseStart family slot phase+index]? =
      (retryPhaseEntries family slot phase)[index]? := by
  obtain ⟨rest,hr⟩ := retry_history_split_phase family slot phase hp
  have hl : (([⟨.source (family.initId slot),.init 1⟩] : List Tma.Entry)++retryPhases family slot phase).length =
      retryPhaseStart family slot phase := by simp [retryPhaseStart,Nat.add_comm]
  rw [hr,List.append_assoc,List.getElem?_append_right (by rw [hl]; omega),hl,Nat.add_sub_cancel_left,
    List.getElem?_append_left hi]

theorem retry_history_notice_a_at {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (hp : phase < uses tiles slot) :
    (retryResourceHistory family slot)[retryNoticeAIndex family slot phase]? =
      some ⟨.notification (family.copyAId (stageTile slot phase)),.completeTx 2048⟩ := by
  rw [retryNoticeAIndex,Nat.add_assoc,retry_history_phase_at family slot phase hp _ (by rw [retry_phase_length]; omega)]
  simp only [retryPhaseEntries,List.append_assoc]
  rw [List.getElem?_append_right (by simp),List.getElem?_append_right (by simp)]
  simp

theorem retry_history_notice_b_at {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (hp : phase < uses tiles slot) :
    (retryResourceHistory family slot)[retryNoticeBIndex family slot phase]? =
      some ⟨.notification (family.copyBId (stageTile slot phase)),.completeTx 256⟩ := by
  have he : retryNoticeBIndex family slot phase = retryPhaseStart family slot phase+
      (2+(retryFailedEntries family (stageTile slot phase)).length) := by unfold retryNoticeBIndex retryNoticeAIndex; omega
  rw [he,retry_history_phase_at family slot phase hp _ (by rw [retry_phase_length]; omega)]
  simp only [retryPhaseEntries,List.append_assoc]
  rw [List.getElem?_append_right (by simp only [List.length_cons,List.length_nil]; omega),
    List.getElem?_append_right (by simp only [List.length_cons,List.length_nil]; omega)]
  simp only [List.length_cons,List.length_nil]
  rw [show 2+(retryFailedEntries family (stageTile slot phase)).length-1-
    (retryFailedEntries family (stageTile slot phase)).length = 1 by omega]
  rfl

theorem retry_history_wait_at {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (hp : phase < uses tiles slot) (lane : Wgmma.Lane) :
    (retryResourceHistory family slot)[retryPhaseWaitIndex family slot phase lane]? =
      some ⟨.source (family.waitId (stageTile slot phase) lane),.tryWaitParity (phase%2) true⟩ := by
  have he : retryPhaseWaitIndex family slot phase lane = retryPhaseStart family slot phase+
      (3+(retryFailedEntries family (stageTile slot phase)).length+lane.val) := by unfold retryPhaseWaitIndex retryNoticeAIndex; omega
  rw [he,retry_history_phase_at family slot phase hp _ (by rw [retry_phase_length]; have := lane.isLt; omega)]
  simp only [retryPhaseEntries,List.append_assoc]
  rw [List.getElem?_append_right (by simp only [List.length_cons,List.length_nil]; omega),
    List.getElem?_append_right (by simp only [List.length_cons,List.length_nil]; omega),
    List.getElem?_append_right (by simp only [List.length_cons,List.length_nil]; omega)]
  simp only [List.length_cons,List.length_nil]
  rw [show 3+(retryFailedEntries family (stageTile slot phase)).length+lane.val-1-
    (retryFailedEntries family (stageTile slot phase)).length-2 = lane.val by omega]
  simp only [retrySuccessfulEntries,List.getElem?_ofFn,dite_eq_left lane.isLt,stage_tile_phase]

theorem retry_phase_take_notifications {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase)
    (index : Nat) (hi : index ≤ 2) :
    (retryPhaseEntries family slot phase).take (1+(retryFailedEntries family (stageTile slot phase)).length+index) =
      ([⟨.source (family.expectId (stageTile slot phase)),.arriveExpectTx 2304⟩]++retryFailedEntries family (stageTile slot phase))++
        ([⟨.notification (family.copyAId (stageTile slot phase)),.completeTx 2048⟩,
          ⟨.notification (family.copyBId (stageTile slot phase)),.completeTx 256⟩] : List Tma.Entry).take index := by
  have hh := take_within_middle
    ([⟨.source (family.expectId (stageTile slot phase)),.arriveExpectTx 2304⟩]++retryFailedEntries family (stageTile slot phase))
    ([⟨.notification (family.copyAId (stageTile slot phase)),.completeTx 2048⟩,
      ⟨.notification (family.copyBId (stageTile slot phase)),.completeTx 256⟩] : List Tma.Entry)
    (retrySuccessfulEntries family (stageTile slot phase)) index (by simpa only [List.length_cons,List.length_nil] using hi)
  simpa only [retryPhaseEntries,List.length_append,List.length_cons,List.length_nil] using hh

theorem retry_phase_take_waits {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (lane : Wgmma.Lane) :
    (retryPhaseEntries family slot phase).take (3+(retryFailedEntries family (stageTile slot phase)).length+lane.val) =
      ([⟨.source (family.expectId (stageTile slot phase)),.arriveExpectTx 2304⟩]++retryFailedEntries family (stageTile slot phase)++
        [⟨.notification (family.copyAId (stageTile slot phase)),.completeTx 2048⟩,
          ⟨.notification (family.copyBId (stageTile slot phase)),.completeTx 256⟩])++
        (retrySuccessfulEntries family (stageTile slot phase)).take lane.val := by
  have hh := take_within_middle
    ([⟨.source (family.expectId (stageTile slot phase)),.arriveExpectTx 2304⟩]++retryFailedEntries family (stageTile slot phase)++
      [⟨.notification (family.copyAId (stageTile slot phase)),.completeTx 2048⟩,
        ⟨.notification (family.copyBId (stageTile slot phase)),.completeTx 256⟩])
    (retrySuccessfulEntries family (stageTile slot phase)) [] lane.val (by simpa only [retrySuccessfulEntries,List.length_ofFn] using Nat.le_of_lt lane.isLt)
  simpa only [retryPhaseEntries,List.append_nil,List.length_append,List.length_cons,List.length_nil,
    show 1+(retryFailedEntries family (stageTile slot phase)).length+2 = 3+(retryFailedEntries family (stageTile slot phase)).length by omega] using hh

theorem retry_history_prefix_run {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) :
    Mbarrier.run none ((([⟨.source (family.initId slot),.init 1⟩] : List Tma.Entry)++retryPhases family slot phase).map Tma.Entry.operation) =
      some (some (readyState phase)) := by
  simp only [List.map_append,List.map_cons,List.map_nil,Mbarrier.run_append]
  have hi : Mbarrier.run none [.init 1] = some (some (readyState 0)) := by decide
  rw [hi,Option.bind_some,retry_phases_protocol]

theorem retry_phase_partial_waits {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (lane : Wgmma.Lane) :
    Mbarrier.run (some (readyState phase))
      (((retryPhaseEntries family slot phase).take (3+(retryFailedEntries family (stageTile slot phase)).length+lane.val)).map Tma.Entry.operation) =
      some (some (if lane.val = 0 then transferredState phase else readyState (phase+1))) := by
  rw [retry_phase_take_waits,List.map_append,List.map_append,List.map_append,List.map_cons,List.map_nil,
    List.map_cons,List.map_cons,List.map_nil,List.map_take,retry_successful_operations,List.take_replicate,
    Nat.min_eq_left (Nat.le_of_lt lane.isLt),Mbarrier.run_append,Mbarrier.run_append,Mbarrier.run_append,
    retry_arrival_run,Option.bind_some,retry_failed_run,Option.bind_some,retry_completions_run,Option.bind_some]
  cases hn : lane.val with
  | zero => rfl
  | succ n =>
    rw [List.replicate_succ,Mbarrier.run,successful_phase_wait,Option.bind_some,repeated_ready_waits]
    simp

theorem retry_history_wait_prefix {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (hp : phase < uses tiles slot) (lane : Wgmma.Lane) :
    Mbarrier.run none (((retryResourceHistory family slot).map Tma.Entry.operation).take (retryPhaseWaitIndex family slot phase lane)) =
      some (some (if lane.val = 0 then transferredState phase else readyState (phase+1))) := by
  have he : retryPhaseWaitIndex family slot phase lane = retryPhaseStart family slot phase+
      (3+(retryFailedEntries family (stageTile slot phase)).length+lane.val) := by unfold retryPhaseWaitIndex retryNoticeAIndex; omega
  rw [← List.map_take,he,retry_history_take family slot phase hp _ (by rw [retry_phase_length]; have := lane.isLt; omega),
    List.map_append,Mbarrier.run_append,retry_history_prefix_run,Option.bind_some,retry_phase_partial_waits]

end
end Ptx.Kernels.HopperDoubleBuffer
