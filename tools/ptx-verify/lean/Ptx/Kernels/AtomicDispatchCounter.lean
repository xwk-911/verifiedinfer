import Ptx.Kernels.AtomicDispatchOutputMemory

/-! The second increment is coherence-latest on every counter byte. A source
choice at one byte and SC-per-location prohibit reversing that order elsewhere. -/
namespace Ptx.AtomicDispatchEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.AtomicDispatchTrace
noncomputable section

theorem first_counter_byte (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Params cfg.counter cfg.x cfg.y launch.params) (jobs : Assignment execution) {offset : Nat} (ho : offset < 4) :
    execution.writeByte (firstCounter jobs) ((counterLoc cfg).add offset) = some (u32Byte 1 offset) := by
  simpa only [firstCounter,jobs.firstTicket,show wrap 32 (0+1) = 1 from rfl] using counter_write_byte cfg hw hd hp jobs.firstMember ho

theorem second_counter_byte (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Params cfg.counter cfg.x cfg.y launch.params) (jobs : Assignment execution) {offset : Nat} (ho : offset < 4) :
    execution.writeByte (secondCounter jobs) ((counterLoc cfg).add offset) = some (u32Byte 2 offset) := by
  simpa only [secondCounter,jobs.secondTicket,show wrap 32 (1+1) = 2 from rfl] using counter_write_byte cfg hw hd hp jobs.secondMember ho

theorem second_counter_reads_first_base (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate} {rf co}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Pre cfg launch) (hm : GenericMemoryConditions execution launch.initial rf co) (jobs : Assignment execution) :
    rf (secondCounter jobs) (counterLoc cfg) = .write (firstCounter jobs) := by
  have hr := counter_read_byte cfg hw hd hp.2.1 jobs.secondMember (offset := 0) (by decide)
  have hwb := second_counter_byte cfg hw hd hp.2.1 jobs (offset := 0) (by decide)
  have hl := counter_offset cfg (offset := 0) (by decide)
  simp only [Location.add,Nat.add_zero,jobs.secondTicket] at hr hwb hl
  have he := counter_eligible cfg hw hd hp.1 hp.2.1 rf hl (Or.inl (by rw [hr]; rfl))
  cases hs : rf (secondCounter jobs) (counterLoc cfg) with
  | initial =>
    have hv := initial_read_value hm.agreement he hr hs
    have hi := hp.2.2 0 (by decide)
    simp only [Location.add,Nat.add_zero] at hi
    have hbits := Symbolic.Byte.bits.inj (hv.trans hi)
    exact ((show Cells.wordByte 1 0 ≠ Cells.wordByte 0 0 by decide) hbits).elim
  | write writer =>
    have hv := write_read_value hm.agreement he hr hs
    rcases counter_writer_pair cfg hw hd hp.1 hp.2.1 jobs hl hv with hi | hi
    · exact congrArg Source.write hi
    · subst writer
      exact (rmw_no_self_read hm (no_mixed cfg hw hd hp.1 hp.2.1 rf) hr hwb hs).elim

theorem counter_order (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate} {rf co}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Pre cfg launch) (hm : GenericMemoryConditions execution launch.initial rf co) (jobs : Assignment execution)
    {offset : Nat} (ho : offset < 4) :
    co ((counterLoc cfg).add offset) (.write (firstCounter jobs)) (.write (secondCounter jobs)) := by
  have hstrong := rmw_morally_strong (counter_event cfg hw hd hp.2.1 jobs.firstMember)
    (counter_event cfg hw hd hp.2.1 jobs.secondMember) (by simp [atomicAddBytes]) True.intro True.intro
  have hne : firstCounter jobs ≠ secondCounter jobs := by
    intro he
    exact assigned_ids_ne hw jobs (congrArg EventId.thread he)
  have hwa := first_counter_byte cfg hw hd hp.2.1 jobs ho
  have hwb := second_counter_byte cfg hw hd hp.2.1 jobs ho
  have hn := no_mixed cfg hw hd hp.1 hp.2.1 rf
  rcases (hm.coherence hn).comparable _ _ _ _ _ hne hwa hwb (Or.inl hstrong) with hc | hc
  · exact hc
  · have hr := counter_read_byte cfg hw hd hp.2.1 jobs.secondMember (offset := 0) (by decide)
    have hwbase := first_counter_byte cfg hw hd hp.2.1 jobs (offset := 0) (by decide)
    simp only [Location.add,Nat.add_zero] at hr hwbase
    exact (coherence_before_cannot_read_after hm hn (morally_strong_symmetric hstrong) hwb hwa hc hr hwbase
      (second_counter_reads_first_base cfg hw hd hp hm jobs)).elim

end
end Ptx.AtomicDispatchEvent
