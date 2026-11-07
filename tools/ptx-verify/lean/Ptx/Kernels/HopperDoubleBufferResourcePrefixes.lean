import Ptx.Kernels.HopperDoubleBufferResourceHistory

/-! Checked prefixes of the constructed source-matched resource histories.
The positions are per-resource history positions, not source event serials. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def phaseStart (phase : Nat) : Nat := 1+131*phase
def noticeAIndex (phase : Nat) : Nat := phaseStart phase+1
def noticeBIndex (phase : Nat) : Nat := phaseStart phase+2
def phaseWaitIndex (phase : Nat) (lane : Wgmma.Lane) : Nat := phaseStart phase+3+lane.val

theorem data_phases_split (a b tiles slot) (m n : Nat) (hm : m ≤ n) :
    ∃ rest, dataPhases a b tiles slot n = dataPhases a b tiles slot m++rest := by
  induction n with
  | zero =>
    have he : m = 0 := by omega
    subst m
    exact ⟨[],rfl⟩
  | succ n ih =>
    by_cases he : m = n+1
    · exact ⟨[],by simp only [he,List.append_nil]⟩
    · obtain ⟨rest,hr⟩ := ih (by omega)
      exact ⟨rest++dataPhaseEntries a b tiles slot n,by rw [dataPhases,hr,List.append_assoc]⟩

theorem data_history_split_phase (a b tiles slot phase) (hp : phase < uses tiles slot) :
    ∃ rest, dataResourceHistory a b tiles slot =
      (([⟨.source (dataInitId tiles slot),.init 1⟩] : List Tma.Entry)++dataPhases a b tiles slot phase)++
        dataPhaseEntries a b tiles slot phase++rest := by
  obtain ⟨rest,hr⟩ := data_phases_split a b tiles slot (phase+1) (uses tiles slot) (by omega)
  refine ⟨rest++[⟨.source (dataInvalId a b tiles slot),.inval⟩],?_⟩
  simp only [dataResourceHistory,hr,dataPhases,List.append_assoc]

theorem take_within_middle {α : Type} (first middle last : List α) (index : Nat) (hi : index ≤ middle.length) :
    (first++middle++last).take (first.length+index) = first++middle.take index := by
  rw [List.append_assoc,List.take_append]
  simp only [Nat.add_sub_cancel_left,List.take_of_length_le (by omega : first.length ≤ first.length+index)]
  rw [List.take_append]
  simp only [Nat.sub_eq_zero_of_le hi,List.take_zero,List.append_nil]

theorem data_history_take (a b tiles slot phase) (hp : phase < uses tiles slot) (index : Nat) (hi : index ≤ 131) :
    (dataResourceHistory a b tiles slot).take (phaseStart phase+index) =
      (([⟨.source (dataInitId tiles slot),.init 1⟩] : List Tma.Entry)++dataPhases a b tiles slot phase)++
        (dataPhaseEntries a b tiles slot phase).take index := by
  obtain ⟨rest,hr⟩ := data_history_split_phase a b tiles slot phase hp
  have hl : (([⟨.source (dataInitId tiles slot),.init 1⟩] : List Tma.Entry)++dataPhases a b tiles slot phase).length = phaseStart phase := by
    simp [phaseStart,data_phases_length,Nat.add_comm]
  rw [hr,← hl]
  exact take_within_middle _ _ _ index (by simpa only [data_phase_entries_length] using hi)

theorem data_history_phase_at (a b tiles slot phase) (hp : phase < uses tiles slot) (index : Nat) (hi : index < 131) :
    (dataResourceHistory a b tiles slot)[phaseStart phase+index]? =
      (dataPhaseEntries a b tiles slot phase)[index]? := by
  obtain ⟨rest,hr⟩ := data_history_split_phase a b tiles slot phase hp
  rw [hr,List.append_assoc,List.getElem?_append_right (by simp only [List.length_append,List.length_cons,List.length_nil,data_phases_length,phaseStart]; omega)]
  have hl : (([⟨.source (dataInitId tiles slot),.init 1⟩] : List Tma.Entry)++dataPhases a b tiles slot phase).length = phaseStart phase := by
    simp [phaseStart,data_phases_length,Nat.add_comm]
  rw [hl,Nat.add_sub_cancel_left,List.getElem?_append_left (by simpa only [data_phase_entries_length] using hi)]

theorem data_history_notice_a_at (a b tiles slot phase) (hp : phase < uses tiles slot) :
    (dataResourceHistory a b tiles slot)[noticeAIndex phase]? =
      some ⟨.notification (dataCopyAId a b tiles (stageTile slot phase)),.completeTx 2048⟩ := by
  rw [noticeAIndex,data_history_phase_at a b tiles slot phase hp 1 (by decide)]
  rfl

theorem data_history_notice_b_at (a b tiles slot phase) (hp : phase < uses tiles slot) :
    (dataResourceHistory a b tiles slot)[noticeBIndex phase]? =
      some ⟨.notification (dataCopyBId a b tiles (stageTile slot phase)),.completeTx 256⟩ := by
  rw [noticeBIndex,data_history_phase_at a b tiles slot phase hp 2 (by decide)]
  rfl

theorem data_history_wait_at (a b tiles slot phase) (hp : phase < uses tiles slot) (lane : Wgmma.Lane) :
    (dataResourceHistory a b tiles slot)[phaseWaitIndex phase lane]? =
      some ⟨.source (dataWaitId a b tiles (stageTile slot phase) lane),.tryWaitParity (phase%2) true⟩ := by
  rw [phaseWaitIndex,Nat.add_assoc,data_history_phase_at a b tiles slot phase hp (3+lane.val) (by have := lane.isLt; omega)]
  simp only [dataPhaseEntries]
  rw [List.getElem?_append_right (by simp)]
  change (List.ofFn (fun lane : Wgmma.Lane => (⟨.source (dataWaitId a b tiles (stageTile slot phase) lane),.tryWaitParity (phase%2) true⟩ : Tma.Entry)))[3+lane.val-3]? = _
  rw [Nat.add_sub_cancel_left]
  simp only [List.getElem?_ofFn,dite_eq_left lane.isLt]

theorem data_phase_take_wait (a b tiles slot phase) (lane : Wgmma.Lane) :
    ((dataPhaseEntries a b tiles slot phase).take (3+lane.val)).map Tma.Entry.operation =
      [.arriveExpectTx 2304,.completeTx 2048,.completeTx 256]++
        List.replicate lane.val (.tryWaitParity (phase%2) true) := by
  rw [List.map_take,data_phase_operations,phaseOperations,List.take_append]
  simp only [List.length_cons,List.length_nil,Nat.add_sub_cancel_left]
  rw [List.take_of_length_le (by simp),List.take_replicate,Nat.min_eq_left (Nat.le_of_lt lane.isLt)]

theorem data_phase_partial_waits (phase count : Nat) :
    Mbarrier.run (some (readyState phase))
      ([.arriveExpectTx 2304,.completeTx 2048,.completeTx 256]++List.replicate count (.tryWaitParity (phase%2) true)) =
      some (some (if count = 0 then transferredState phase else readyState (phase+1))) := by
  rw [Mbarrier.run_append,transfers_finish_phase,Option.bind_some]
  cases count with
  | zero => rfl
  | succ count =>
    rw [List.replicate_succ,Mbarrier.run,successful_phase_wait,Option.bind_some,repeated_ready_waits]
    rfl

theorem data_history_prefix_run (a b tiles slot phase) :
    Mbarrier.run none ((([⟨.source (dataInitId tiles slot),.init 1⟩] : List Tma.Entry)++dataPhases a b tiles slot phase).map Tma.Entry.operation) =
      some (some (readyState phase)) := by
  simp only [List.map_append,List.map_cons,List.map_nil,data_phases_operations,Mbarrier.run_append]
  have hi : Mbarrier.run none [.init 1] = some (some (readyState 0)) := by decide
  rw [hi,Option.bind_some,all_phases_protocol]

theorem data_history_wait_prefix (a b tiles slot phase) (hp : phase < uses tiles slot) (lane : Wgmma.Lane) :
    Mbarrier.run none (((dataResourceHistory a b tiles slot).map Tma.Entry.operation).take (phaseWaitIndex phase lane)) =
      some (some (if lane.val = 0 then transferredState phase else readyState (phase+1))) := by
  rw [← List.map_take,phaseWaitIndex,Nat.add_assoc,data_history_take a b tiles slot phase hp (3+lane.val) (by have := lane.isLt; omega),
    List.map_append,Mbarrier.run_append,data_history_prefix_run,Option.bind_some,data_phase_take_wait,data_phase_partial_waits]

end
end Ptx.Kernels.HopperDoubleBuffer
