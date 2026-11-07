import Ptx.Event.Consistency
import Ptx.Tests.EventRaces

/-! A circular-exemption regression from one actual shared program. Each thread
can generate a finite local trace under the oracle semantics, but the two barrier
returns cannot be globally admitted by declaring each peer already exited. -/
namespace Ptx.EventBarrierTests
open Ptx Ptx.ISA Ptx.Event

def code : List Instr := [
  .mov 32 "%i" .tid,
  .setp .eq "%p" (.reg "%i") (.imm 0),
  .branch "%p" true 5,
  .barrier 1,
  .ret,
  .barrier 0,
  .ret]

def first : ThreadTrace := {
  id := EventRaceTests.writer
  oracle := fun _ => 0
  count := 5
  final := { thread := { pc := 6, regs := [("%p", 1), ("%i", 0)], status := .done }, generations := [(0,1)] }
  events := [.barrierArrival 0 0, .barrierReturn 0 0]
}
def second : ThreadTrace := {
  id := EventRaceTests.reader
  oracle := fun _ => 0
  count := 5
  final := { thread := { pc := 4, regs := [("%p", 0), ("%i", 1)], status := .done }, generations := [(1,1)] }
  events := [.barrierArrival 1 0, .barrierReturn 1 0]
}
def graph : Candidate := ⟨[first, second]⟩
def leaveFirst : EventId := ⟨EventRaceTests.writer, 1⟩
def leaveSecond : EventId := ⟨EventRaceTests.reader, 1⟩

theorem first_produced : first.Produced code [] := by rfl
theorem second_produced : second.Produced code [] := by rfl

/-- Final status alone is not sufficient to admit these returns. -/
theorem local_traces_complete : graph.Complete := by
  intro t ht
  simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht <;> subst t <;> rfl

theorem first_exit_before_second : ExitBeforeReturn graph leaveFirst leaveSecond := by
  refine ⟨by rfl, first, by simp [graph], rfl, rfl, 1, 0, by rfl, ?_⟩
  exact ⟨rfl, by intro g hg; simp [first] at hg⟩

theorem second_exit_before_first : ExitBeforeReturn graph leaveSecond leaveFirst := by
  refine ⟨by rfl, second, by simp [graph], rfl, rfl, 0, 0, by rfl, ?_⟩
  exact ⟨rfl, by intro g hg; simp [second] at hg⟩

theorem circular_exit_rejected (initial : ByteMap) (rf : ReadsFrom) (co : Coherence) :
    ¬ GenericMemoryConditions graph initial rf co := by
  intro hc
  apply hc.barrierControl leaveFirst
  exact .trans (.single (.inr (.inr first_exit_before_second)))
    (.single (.inr (.inr second_exit_before_first)))

theorem different_resources_do_not_synchronize :
    ¬ BarrierSync graph ⟨EventRaceTests.writer, 0⟩ leaveSecond := by
  rintro ⟨_, id, generation, ha, hb⟩
  have hea : graph.eventAt ⟨EventRaceTests.writer, 0⟩ = some (.barrierArrival 0 0) := rfl
  have heb : graph.eventAt leaveSecond = some (.barrierReturn 1 0) := rfl
  have hi₁ := congrArg (fun k => match k with | .barrierArrival id _ => id | _ => 42)
    (Option.some.inj (hea.symm.trans ha))
  have hi₂ := congrArg (fun k => match k with | .barrierReturn id _ => id | _ => 42)
    (Option.some.inj (heb.symm.trans hb))
  simp only at hi₁ hi₂
  omega

end Ptx.EventBarrierTests
