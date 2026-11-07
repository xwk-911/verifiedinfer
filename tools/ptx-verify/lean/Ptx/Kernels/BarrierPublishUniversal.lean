import Ptx.Kernels.BarrierPublish
import Ptx.Event.Equivalence
import Ptx.Event.Contracts

/-! All-candidate publication contracts. Trace lengths, trace-list ordering,
oracles and memory/observation witnesses are universally quantified. The external
allocation/UB, projected-observer and PTX-correspondence boundaries are unchanged.
-/
namespace Ptx.BarrierPublish
open Ptx.ISA Ptx.Event

theorem graph_eventAt (base value answer : Nat) (id : EventId) :
    (graph base value answer).eventAt id =
      if id.thread = writer then (producer base value).events[id.serial]?
      else if id.thread = reader then (consumer base value answer).events[id.serial]? else none := by
  by_cases hw : id.thread = writer
  · simp [Candidate.eventAt, graph, producer, consumer, hw]
  · by_cases hr : id.thread = reader
    · simp [Candidate.eventAt, graph, producer, consumer, hr, List.find?, beq_iff_eq,
        show writer ≠ reader by decide, show reader ≠ writer by decide]
    · simp [Candidate.eventAt, graph, producer, consumer, hw, hr, beq_iff_eq, Ne.symm hw, Ne.symm hr]

theorem candidate_view {base value initial c}
    (hw : Candidate.WellFormed code (launch base value initial) c) (hd : c.Complete) :
    ∃ answer, SameEvents c (graph base value answer) := by
  obtain ⟨consumerTrace, hconsumer, hcId⟩ := hw.2.2.2 reader
    (by simp [ThreadId.Valid, Dim3.Within, reader, Dim3.zero, launch, Dim3.one])
  let answer := consumerTrace.oracle 0
  refine ⟨answer, ?_⟩
  funext id
  rw [graph_eventAt]
  by_cases hiw : id.thread = writer
  · obtain ⟨t, ht, htid⟩ := hw.2.2.2 writer
      (by simp [ThreadId.Valid, Dim3.Within, writer, Dim3.zero, launch, Dim3.one])
    have hs := producer_trace_shape (hw.2.2.1 t ht).2 htid (hd t ht)
    rw [eventAt_of_trace hw.2.1 ht (hiw.trans htid.symm), hs.2.2]
    simp only [hiw, ↓reduceIte]
  · by_cases hir : id.thread = reader
    · have hs := consumer_trace_shape (hw.2.2.1 consumerTrace hconsumer).2 hcId (hd consumerTrace hconsumer)
      rw [eventAt_of_trace hw.2.1 hconsumer (hir.trans hcId.symm), hs.2.2]
      simp only [hir, show reader ≠ writer by decide, ↓reduceIte, answer]
    · have hn : c.eventAt id = none := by
        cases he : c.eventAt id with
        | none => rfl
        | some kind =>
          obtain ⟨t, ht, htid, _⟩ := eventAt_trace he
          rcases valid_id_cases (hw.2.2.1 t ht).1 with hwid | hrid
          · exact (hiw (htid.symm.trans hwid)).elim
          · exact (hir (htid.symm.trans hrid)).elim
      simp only [hiw, hir, ↓reduceIte, hn]

theorem control_acyclic (base value answer : Nat) : BarrierControlAcyclic (graph base value answer) := by
  intro id hp
  have hlt := hp.rank_lt rank (by
    intro a b h
    rcases h with h | h | h
    · exact po_rank h
    · exact sync_rank h
    · exact (no_exit_edges h).elim)
  exact Nat.lt_irrefl _ hlt

theorem candidate_output_correct {base value initial c sources order o}
    (hw : Candidate.WellFormed code (launch base value initial) c)
    (hc : GenericMemoryConditions c initial sources order)
    (ho : ObserverConditions c initial sources order o)
    (hd : o.domain = wordDomain base) : observedU32 o base = wrap 32 value := by
  obtain ⟨answer, heq⟩ := candidate_view hw ho.complete
  have hm := heq.memory (barriers base value answer) (control_acyclic base value answer) hc
  have hob := heq.observation (complete base value answer) ho
  exact observed_word_correct hm hob hd

def Pre (base value : Nat) (l : Launch) : Prop :=
  l.geometry = (launch base value l.initial).geometry ∧ l.params = params base value

def outputWord (output : ByteMap) (base : Nat) : Nat :=
  decodeLE [output ((loc base).add 0), output ((loc base).add 1),
    output ((loc base).add 2), output ((loc base).add 3)]

theorem pre_eq_launch {base value l} (hp : Pre base value l) : l = launch base value l.initial := by
  rcases l with ⟨geometry, parameters, initial⟩
  change geometry = ⟨Dim3.one, ⟨2,1,1⟩⟩ ∧ parameters = params base value at hp
  rcases hp with ⟨rfl, rfl⟩
  rfl

theorem correct (base value : Nat) :
    Event.Triple code (Pre base value) (fun _ => wordDomain base)
      (fun _ output => outputWord output base = wrap 32 value) := by
  intro l c sources order o hp hw hc ho hd
  have heq := pre_eq_launch hp
  have hlaunch : c.WellFormed code (launch base value l.initial) := heq ▸ hw
  exact candidate_output_correct hlaunch hc ho hd

theorem nonvacuous (base value : Nat) :
    Event.Nonvacuous code (Pre base value) (fun _ => wordDomain base) := by
  intro l hp
  obtain ⟨c, sources, order, o, hw, hc, ho, hd⟩ := observed_execution_exists base value l.initial
  have heq := pre_eq_launch hp
  exact ⟨c, sources, order, o, heq.symm ▸ hw, hc, ho, hd⟩

end Ptx.BarrierPublish
