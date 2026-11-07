import Ptx.Event.Thread

/-! Launch-wide trace candidates. Coverage, unique thread identities and trace
provenance are obligations, not assumptions hidden in a kernel-specific meaning.
WellFormed and Complete do NOT establish PTX memory consistency or UB freedom.
Graph payload and oracle metadata types are parameters, with the original byte
and integer-oracle types as defaults. Final state records integer/control state;
scalar provenance separately checks the complete float register bank.
-/
namespace Ptx.Event
open Ptx.ISA

abbrev ByteMap (ByteValue : Type := Byte) := Location → ByteValue

structure Launch (ByteValue : Type := Byte) where
  geometry : Geometry
  params : Bindings := []
  initial : ByteMap ByteValue

structure ThreadTrace (ByteValue : Type := Byte) (Answers : Type := Oracle) where
  id : ThreadId
  oracle : Answers
  count : Nat
  final : State
  events : List (Kind ByteValue)

def ThreadTrace.Produced (code : List Instr) (params : Bindings) (t : ThreadTrace) : Prop :=
  run ⟨t.id, params⟩ t.oracle code t.count {} = .ok (t.final, t.events)

structure Candidate (ByteValue : Type := Byte) (Answers : Type := Oracle) where
  traces : List (ThreadTrace ByteValue Answers)

def Candidate.WellFormed (code : List Instr) (launch : Launch) (c : Candidate) : Prop :=
  launch.geometry.Valid ∧
  (c.traces.map ThreadTrace.id).Nodup ∧
  (∀ t ∈ c.traces, t.id.Valid launch.geometry ∧ t.Produced code launch.params) ∧
  (∀ id, id.Valid launch.geometry → ∃ t ∈ c.traces, t.id = id)

variable {ByteValue Answers : Type}

def Candidate.Complete (c : Candidate ByteValue Answers) : Prop :=
  ∀ t ∈ c.traces, t.final.thread.status = .done

structure EventId where
  thread : ThreadId
  serial : Nat
  deriving Repr, DecidableEq

/-- Event indices count emitted events, not instructions or oracle queries. -/
def Candidate.eventAt (c : Candidate ByteValue Answers) (id : EventId) : Option (Kind ByteValue) :=
  (c.traces.find? (fun t => t.id == id.thread)).bind (fun t => t.events[id.serial]?)

theorem unique_trace_id {traces : List (ThreadTrace ByteValue Answers)} (hn : (traces.map ThreadTrace.id).Nodup)
    {t u : ThreadTrace ByteValue Answers} (ht : t ∈ traces) (hu : u ∈ traces) (hid : t.id = u.id) : t = u := by
  induction traces with
  | nil => simp at ht
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons] at ht hu
    rcases ht with rfl | ht <;> rcases hu with rfl | hu
    · rfl
    · exact (hn.1 (List.mem_map.mpr ⟨u,hu,hid.symm⟩)).elim
    · exact (hn.1 (List.mem_map.mpr ⟨t,ht,hid⟩)).elim
    · exact ih hn.2 ht hu

theorem eventAt_of_trace {c : Candidate ByteValue Answers} {t : ThreadTrace ByteValue Answers} {id : EventId}
    (hn : (c.traces.map ThreadTrace.id).Nodup) (ht : t ∈ c.traces) (hid : id.thread = t.id) :
    c.eventAt id = t.events[id.serial]? := by
  unfold Candidate.eventAt
  cases hf : c.traces.find? (fun x => x.id == id.thread) with
  | none =>
    have hnone := List.find?_eq_none.mp hf t ht
    simp [hid] at hnone
  | some u =>
    have hu := List.mem_of_find?_eq_some hf
    have hui := List.find?_some (p := fun x : ThreadTrace ByteValue Answers => x.id == id.thread) hf
    have huid : u.id = id.thread := by simpa only [beq_iff_eq] using hui
    have heq : t.id = u.id := hid.symm.trans huid.symm
    have hut : t = u := unique_trace_id hn ht hu heq
    subst u
    rfl

theorem find_trace {c : Candidate ByteValue Answers} {t : ThreadTrace ByteValue Answers} {id : EventId}
    (hn : (c.traces.map ThreadTrace.id).Nodup) (ht : t ∈ c.traces) (hid : id.thread = t.id) :
    c.traces.find? (fun x => x.id == id.thread) = some t := by
  cases hf : c.traces.find? (fun x => x.id == id.thread) with
  | none =>
    have hh := List.find?_eq_none.mp hf t ht
    simp [hid] at hh
  | some u =>
    have hu := List.mem_of_find?_eq_some hf
    have hui := List.find?_some (p := fun x : ThreadTrace ByteValue Answers => x.id == id.thread) hf
    have huid : u.id = id.thread := by simpa only [beq_iff_eq] using hui
    have he : t = u := unique_trace_id hn ht hu (hid.symm.trans huid.symm)
    exact congrArg some he.symm

theorem eventAt_trace {c : Candidate ByteValue Answers} {id kind} (h : Candidate.eventAt c id = some kind) :
    ∃ t ∈ c.traces, t.id = id.thread ∧ t.events[id.serial]? = some kind := by
  unfold Candidate.eventAt at h
  cases hf : c.traces.find? (fun t => t.id == id.thread) with
  | none => simp [hf] at h
  | some t =>
    have ht := List.find?_some (p := fun x : ThreadTrace ByteValue Answers => x.id == id.thread) hf
    exact ⟨t, List.mem_of_find?_eq_some hf, by simpa only [beq_iff_eq] using ht,
      by simpa [hf] using h⟩

theorem eventAt_mem {c : Candidate ByteValue Answers} {id kind} (h : Candidate.eventAt c id = some kind) :
    ∃ t ∈ c.traces, kind ∈ t.events ∧ id.serial < t.events.length := by
  unfold Candidate.eventAt at h
  cases hf : c.traces.find? (fun t => t.id == id.thread) with
  | none => simp [hf] at h
  | some t =>
    have he : t.events[id.serial]? = some kind := by simpa [hf] using h
    exact ⟨t, List.mem_of_find?_eq_some hf, List.mem_of_getElem? he,
      (List.getElem?_eq_some_iff.mp he).1⟩

theorem produced_runs {code params t} (h : ThreadTrace.Produced code params t) :
    Runs ⟨t.id, params⟩ t.oracle code {} t.events t.final := run_sound h

theorem candidate_trace_runs {code launch c t} (hw : Candidate.WellFormed code launch c)
    (ht : t ∈ c.traces) : Runs ⟨t.id, launch.params⟩ t.oracle code {} t.events t.final :=
  produced_runs (hw.2.2.1 t ht).2

end Ptx.Event
