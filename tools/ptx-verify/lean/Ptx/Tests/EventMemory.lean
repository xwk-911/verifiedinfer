import Ptx.Event.Consistency
import Ptx.Tests.Event

/-! Bytewise source checks and a parameterized, provenance-checked read-only
execution witness. The witness establishes the new generic-memory predicates,
not ISA UB freedom, allocation safety or complete PTX-model correspondence. -/
namespace Ptx.EventMemoryTests
open Ptx Ptx.ISA Ptx.Event

example : payloadByte ⟨.global, 4⟩ [byte 7] ⟨.global, 3⟩ = none := by decide
example : payloadByte ⟨.global, 4⟩ [byte 7] ⟨.global, 5⟩ = none := by decide
example : payloadByte ⟨.shared .zero, 0⟩ [byte 7] ⟨.shared ⟨1,0,0⟩, 0⟩ = none := by decide

def code : List Instr := [.load .global "%r" ⟨.imm 0, 0⟩, .ret]
def loc : Location := ⟨.global, 0⟩
def payload (value : Nat) : List Byte := encodeU32 (wrap 32 value)
def trace (value : Nat) : ThreadTrace := {
  id := EventTests.id0
  oracle := fun _ => value
  count := 2
  final := { thread := { pc := 1, regs := [("%r", wrap 32 value)], status := .done }, queries := 1 }
  events := [.read loc (payload value)]
}
def graph (value : Nat) : Candidate := ⟨[trace value]⟩
def initial (value : Nat) (address : Location) : Byte :=
  (payloadByte loc (payload value) address).getD (byte 0)
def launch (value : Nat) : Launch := ⟨⟨.one, .one⟩, [], initial value⟩
def readId : EventId := ⟨EventTests.id0, 0⟩

theorem trace_produced (value : Nat) : (trace value).Produced code [] := by rfl

theorem wellFormed (value : Nat) : (graph value).WellFormed code (launch value) := by
  refine ⟨EventTests.return_candidate_wellFormed.1, by simp [graph, trace], ?_, ?_⟩
  · intro t ht
    simp only [graph, List.mem_singleton] at ht
    subst t
    exact ⟨(EventTests.return_candidate_wellFormed.2.2.1 EventTests.returnTrace
      (by simp)).1, trace_produced value⟩
  · intro id hid
    obtain ⟨t, ht, heq⟩ := EventTests.return_candidate_wellFormed.2.2.2 id hid
    simp only [List.mem_singleton] at ht
    subst t
    exact ⟨trace value, by simp [graph], heq⟩

theorem complete (value : Nat) : (graph value).Complete := by
  intro t ht
  simp only [graph, List.mem_singleton] at ht
  subst t
  rfl

theorem event_shape {value id kind} (he : (graph value).eventAt id = some kind) :
    kind = .read loc (payload value) ∧ id.serial = 0 := by
  obtain ⟨t, ht, hk, hn⟩ := eventAt_mem he
  simp only [graph, List.mem_singleton] at ht
  subst t
  simp only [trace, List.mem_singleton] at hk
  exact ⟨hk, by simpa [trace] using hn⟩

theorem no_writes (value : Nat) (writer address) :
    (graph value).writeByte writer address = none := by
  cases he : (graph value).eventAt writer with
  | none => simp [Candidate.writeByte, he]
  | some kind =>
    have hk := (event_shape he).1
    simp [Candidate.writeByte, he, hk, Kind.writeByte]

theorem no_edges (value : Nat) (a b) :
    ¬ (ProgramOrder (graph value) a b ∨ BarrierSync (graph value) a b) := by
  intro hedge
  rcases hedge with hp | hs
  · have hzero : ∀ id, (graph value).Present id → id.serial = 0 := by
      intro id h
      cases he : (graph value).eventAt id with
      | none => simp [Candidate.Present, he] at h
      | some kind => exact (event_shape he).2
    have ha := hzero a hp.1
    have hb := hzero b hp.2.1
    have := hp.2.2.2
    omega
  · obtain ⟨_, id, generation, ha, _⟩ := hs
    have hk := (event_shape ha).1
    cases hk

theorem acyclic (value : Nat) : BaseAcyclic (graph value) := by
  have hnone : ∀ a b, BaseCausality (graph value) a b → False := by
    intro a b hp
    induction hp with
    | single he => exact no_edges value _ _ he
    | trans _ _ ih _ => exact ih
  intro id hp
  exact hnone id id hp

theorem barriers (value : Nat) : BarrierParticipation (graph value) := by
  intro leave id generation he
  have hk := (event_shape he).1
  cases hk

theorem barrier_control (value : Nat) : BarrierControlAcyclic (graph value) := by
  apply barrier_control_of_no_returns (acyclic value)
  intro leave id generation he
  have hk := (event_shape he).1
  cases hk

theorem read_value {value read address v}
    (hr : (graph value).readByte read address = some v) : v = initial value address := by
  cases he : (graph value).eventAt read with
  | none => simp [Candidate.readByte, he] at hr
  | some kind =>
    have hk := (event_shape he).1
    have hb : payloadByte loc (payload value) address = some v := by
      simpa [Candidate.readByte, he, hk, Kind.readByte] using hr
    simp [initial, hb]

theorem read_only_consistent (value : Nat) :
    GenericMemoryConditions (graph value) (initial value)
      (fun _ _ => .initial) (fun _ _ _ => False) :=
  read_only_conditions (no_writes value) (acyclic value) (barriers value) (barrier_control value)
    (fun _ _ _ h => read_value h)

/-- A real oracle-driven execution for every scalar input, not a chosen finite
input set or a consistency premise supplied by the kernel specification. -/
theorem consistent_execution_exists (value : Nat) :
    ∃ c rf co, c.WellFormed code (launch value) ∧ c.Complete ∧
      GenericMemoryConditions c (launch value).initial rf co :=
  ⟨graph value, fun _ _ => .initial, fun _ _ _ => False,
    wellFormed value, complete value, read_only_consistent value⟩

/-- The generator permits this oracle, but memory conditions reject it for the
fixed zero initial map, for EVERY possible reads-from/coherence witness. -/
theorem wrong_oracle_rejected (rf : ReadsFrom) (co : Coherence) :
    ¬ GenericMemoryConditions (graph 42) (fun _ => byte 0) rf co := by
  intro hc
  have he := no_writes_eligible (rf := rf) (no_writes 42) readId loc
  have hr : (graph 42).readByte readId loc = some (byte 42) := by rfl
  have hv := unwritten_read_initial hc.agreement he hr (fun w => no_writes 42 w loc)
  exact (show byte 42 ≠ byte 0 by decide) hv

theorem nonexistent_source_rejected (rf : ReadsFrom) (co : Coherence) (writer : EventId)
    (hs : rf readId loc = .write writer) :
    ¬ GenericMemoryConditions (graph 7) (initial 7) rf co := by
  intro hc
  have he := no_writes_eligible (rf := rf) (no_writes 7) readId loc
  have hr : (graph 7).readByte readId loc = some (byte 7) := by rfl
  have hw := write_read_value hc.agreement he hr hs
  rw [no_writes 7] at hw
  cases hw

end Ptx.EventMemoryTests
