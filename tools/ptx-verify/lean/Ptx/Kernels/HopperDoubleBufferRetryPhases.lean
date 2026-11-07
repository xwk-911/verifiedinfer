import Ptx.Kernels.HopperDoubleBufferReplyResourceEndpoints
import Ptx.Kernels.HopperDoubleBufferResourceObservations
import Ptx.Hopper.MbarrierRetries

/-! Constructed multi-phase histories with every actual failed wait retained.
Protocol runs and entry soundness are proved here. Inventory exhaustiveness,
uniqueness, source order and control admission remain separate obligations. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def retryFailedEntries {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) : List Tma.Entry :=
  (List.ofFn (fun lane : Wgmma.Lane => List.ofFn (fun attempt : Fin (family.schedules lane tile) =>
    (⟨.source (family.failedWaitId tile lane attempt),.tryWaitParity (expectedParity tile) false⟩ : Tma.Entry)))).flatten
def retrySuccessfulEntries {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) : List Tma.Entry :=
  List.ofFn (fun lane : Wgmma.Lane =>
    (⟨.source (family.waitId tile lane),.tryWaitParity (expectedParity tile) true⟩ : Tma.Entry))
def retryPhaseEntries {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot : Stage) (phase : Nat) : List Tma.Entry :=
  let tile := stageTile slot phase
  [⟨.source (family.expectId tile),.arriveExpectTx 2304⟩]++retryFailedEntries family tile++
    [⟨.notification (family.copyAId tile),.completeTx 2048⟩,⟨.notification (family.copyBId tile),.completeTx 256⟩]++
    retrySuccessfulEntries family tile
def retryPhases {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot : Stage) : Nat → List Tma.Entry
  | 0 => []
  | n+1 => retryPhases family slot n++retryPhaseEntries family slot n
def retryResourceHistory {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot : Stage) : List Tma.Entry :=
  [⟨.source (family.initId slot),.init 1⟩]++retryPhases family slot (uses tiles slot)++
    [⟨.source (family.invalId slot),.inval⟩]

theorem retry_failed_entry {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (entry : Tma.Entry) :
    entry ∈ retryFailedEntries family tile ↔ ∃ lane : Wgmma.Lane, ∃ attempt : Fin (family.schedules lane tile),
      entry = ⟨.source (family.failedWaitId tile lane attempt),.tryWaitParity (expectedParity tile) false⟩ := by
  simp only [retryFailedEntries,List.mem_flatten]
  constructor
  · rintro ⟨entries,hl,he⟩
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp hl
    obtain ⟨attempt,rfl⟩ := List.mem_ofFn.mp he
    exact ⟨lane,attempt,rfl⟩
  · rintro ⟨lane,attempt,rfl⟩
    exact ⟨_,List.mem_ofFn.mpr ⟨lane,rfl⟩,List.mem_ofFn.mpr ⟨attempt,rfl⟩⟩

theorem retry_failed_operations {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) :
    (retryFailedEntries family (stageTile slot phase)).map Tma.Entry.operation =
      List.replicate (retryFailedEntries family (stageTile slot phase)).length (.tryWaitParity (phase%2) false) := by
  apply List.map_eq_replicate_iff.mpr
  intro entry he
  obtain ⟨lane,attempt,rfl⟩ := (retry_failed_entry family _ _).mp he
  simp only [stage_tile_phase]

theorem retry_failed_entries_length {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) :
    (retryFailedEntries family tile).length = (List.ofFn (fun lane : Wgmma.Lane => family.schedules lane tile)).sum := by
  simp only [retryFailedEntries,List.length_flatten,List.map_ofFn,Function.comp_def,List.length_ofFn]

theorem retry_phases_length_succ {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot n) :
    (retryPhases family slot (n+1)).length = (retryPhases family slot n).length+
      131+(retryFailedEntries family (stageTile slot n)).length := by
  rw [retryPhases,List.length_append]
  simp only [retryPhaseEntries,List.length_append,List.length_cons,List.length_nil,retrySuccessfulEntries,List.length_ofFn]
  omega

theorem retry_successful_operations {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) :
    (retrySuccessfulEntries family (stageTile slot phase)).map Tma.Entry.operation =
      List.replicate 128 (.tryWaitParity (phase%2) true) := by
  simp [retrySuccessfulEntries,stage_tile_phase]

theorem retry_phase_length {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) :
    (retryPhaseEntries family slot phase).length = 131+(retryFailedEntries family (stageTile slot phase)).length := by
  simp [retryPhaseEntries,retrySuccessfulEntries]
  omega

theorem retry_failed_run {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (state : Mbarrier.PhaseState) :
    Mbarrier.run (some state) ((retryFailedEntries family (stageTile slot phase)).map Tma.Entry.operation) = some (some state) := by
  rw [retry_failed_operations]
  have hh := Mbarrier.Retries.run_failed_waits state
    (List.replicate (retryFailedEntries family (stageTile slot phase)).length (phase%2))
  simpa only [List.map_replicate] using hh

theorem retry_arrival_run (phase : Nat) :
    Mbarrier.run (some (readyState phase)) [.arriveExpectTx 2304] = some (some (awaitingTransfer phase 2304)) := by
  simp [Mbarrier.run,Mbarrier.step,Mbarrier.accept,Mbarrier.WellFormed,Mbarrier.finish,Mbarrier.limit,readyState,awaitingTransfer]

theorem retry_completions_run (phase : Nat) :
    Mbarrier.run (some (awaitingTransfer phase 2304)) [.completeTx 2048,.completeTx 256] = some (some (transferredState phase)) := by
  simp [Mbarrier.run,Mbarrier.step,Mbarrier.accept,Mbarrier.WellFormed,Mbarrier.finish,Mbarrier.limit,awaitingTransfer,transferredState]

theorem retry_phase_operations {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) :
    (retryPhaseEntries family slot phase).map Tma.Entry.operation =
      [.arriveExpectTx 2304]++(retryFailedEntries family (stageTile slot phase)).map Tma.Entry.operation++
        [.completeTx 2048,.completeTx 256]++List.replicate 128 (.tryWaitParity (phase%2) true) := by
  simp only [retryPhaseEntries,List.map_append,List.map_cons,List.map_nil,retry_successful_operations]

theorem retry_phase_protocol {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) :
    Mbarrier.run (some (readyState phase)) ((retryPhaseEntries family slot phase).map Tma.Entry.operation) =
      some (some (readyState (phase+1))) := by
  rw [retry_phase_operations,Mbarrier.run_append,Mbarrier.run_append,Mbarrier.run_append,
    retry_arrival_run,Option.bind_some,retry_failed_run,Option.bind_some,retry_completions_run,Option.bind_some]
  rw [List.replicate_succ,Mbarrier.run,successful_phase_wait,Option.bind_some,repeated_ready_waits]

theorem retry_phases_protocol {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot n) :
    Mbarrier.run (some (readyState 0)) ((retryPhases family slot n).map Tma.Entry.operation) = some (some (readyState n)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [retryPhases,List.map_append,Mbarrier.run_append,ih,Option.bind_some,retry_phase_protocol]

theorem retry_history_protocol {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot) :
    Mbarrier.run none ((retryResourceHistory family slot).map Tma.Entry.operation) = some none := by
  simp only [retryResourceHistory,List.map_append,List.map_cons,List.map_nil,Mbarrier.run_append]
  have hi : Mbarrier.run none [.init 1] = some (some (readyState 0)) := by decide
  rw [hi,Option.bind_some,retry_phases_protocol,Option.bind_some]
  rfl

theorem retry_phase_no_initialization {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) :
    (retryPhaseEntries family slot phase).filter isInitialization = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro entry he
  simp only [retryPhaseEntries,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with ((rfl | he) | (rfl | rfl)) | he
  · simp [isInitialization]
  · obtain ⟨lane,attempt,rfl⟩ := (retry_failed_entry family _ _).mp he
    simp [isInitialization]
  · simp [isInitialization]
  · simp [isInitialization]
  · obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp he
    simp [isInitialization]

theorem retry_phases_no_initialization {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot n) :
    (retryPhases family slot n).filter isInitialization = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [retryPhases,List.filter_append,ih,retry_phase_no_initialization]; rfl

theorem retry_phase_entry_sound {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (slot phase) (hp : phase < uses tiles slot)
    (entry : Tma.Entry) (he : entry ∈ retryPhaseEntries family slot phase) :
    Tma.resourceAt Tma.localShared candidate.view entry.origin = some ⟨dataGate slot,entry.operation⟩ := by
  have ht := (stage_tile_in_range tiles slot phase).mpr hp
  simp only [retryPhaseEntries,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with ((rfl | he) | (rfl | rfl)) | he
  · simpa only [Tma.resourceAt,stage_tile_slot,dataGate] using family_expect_at family hw _ ht
  · obtain ⟨lane,attempt,rfl⟩ := (retry_failed_entry family _ _).mp he
    apply Hopper.barrierAt_iff.mpr
    apply Unified.view_barrier_iff.mpr
    simpa only [stage_tile_slot,stage_tile_phase,dataGate,waitEvent,ctx,HopperStage.ctx] using family_failed_wait_at family hw _ ht lane attempt attempt.isLt
  · simpa only [stage_tile_slot] using family_notification_a family hw hd _ ht
  · simpa only [stage_tile_slot] using family_notification_b family hw hd _ ht
  · obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp he
    apply Hopper.barrierAt_iff.mpr
    apply Unified.view_barrier_iff.mpr
    simpa only [stage_tile_slot,dataGate,waitEvent,ctx,HopperStage.ctx] using family_wait_at family hw _ ht lane

theorem retry_phases_entry {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot n) (entry : Tma.Entry) :
    entry ∈ retryPhases family slot n ↔ ∃ phase < n, entry ∈ retryPhaseEntries family slot phase := by
  induction n with
  | zero => simp [retryPhases]
  | succ n ih =>
    simp only [retryPhases,List.mem_append,ih]
    constructor
    · rintro (⟨phase,hp,he⟩ | he)
      · exact ⟨phase,by omega,he⟩
      · exact ⟨n,by omega,he⟩
    · rintro ⟨phase,hp,he⟩
      by_cases hn : phase = n
      · exact Or.inr (hn ▸ he)
      · exact Or.inl ⟨phase,by omega,he⟩

theorem retry_history_entry_sound {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (slot) (entry : Tma.Entry)
    (he : entry ∈ retryResourceHistory family slot) :
    Tma.resourceAt Tma.localShared candidate.view entry.origin = some ⟨dataGate slot,entry.operation⟩ := by
  simp only [retryResourceHistory,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with (rfl | he) | rfl
  · exact family_init_at family hw slot
  · obtain ⟨phase,hp,he⟩ := (retry_phases_entry family slot _ entry).mp he
    exact retry_phase_entry_sound family hw hd slot phase hp entry he
  · exact family_inval_at family hw slot

end
end Ptx.Kernels.HopperDoubleBuffer
