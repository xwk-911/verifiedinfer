import Ptx.MemoryGraph.RankedObservation
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-! A model-level repeated-write witness with independent operation agents.
This checks the generic constructors; it is not a PTX source witness. -/
namespace Ptx.MemoryGraphRankedTests
open Ptx.ISA Ptx.MemoryGraph

abbrev Node := Fin 3
abbrev Source := Option Node
def owner : ThreadId := ⟨.zero,.zero⟩
def loc : Location := ⟨.global,0⟩
def kind (node : Node) : Option (Ptx.Event.Kind Nat) :=
  if node.val = 0 then some (.write loc [7])
  else if node.val = 1 then some (.read loc [7])
  else some (.write loc [42])
def graph : Graph Node Nat := {
  kind := kind
  present := fun _ => True
  agent := fun n => if n.val = 1 then .thread owner else .operation owner 0 n.val
  po := fun _ _ => False
  base := fun a b => a.val < b.val
  complete := True
}
def rf : ReadsFrom Node Source := fun _ _ => some 0
def initial : Ptx.Event.ByteMap Nat := fun _ => 0
def rank (node : Node) : Nat := node.val
def co : Coherence Source := RankedCo graph initial rank
def writers : List Node := [0,2]
def observer : Observation Nat Source := selectedObservation graph initial (rankedWriterSelector graph rank writers) [loc]

theorem read_inventory {node location value} (hr : graph.readByte node location = some value) :
    node = 1 ∧ Ptx.Event.payloadByte loc [7] location = some value := by
  fin_cases node <;> simp [Graph.readByte,graph,kind,Ptx.Event.Kind.readByte] at hr
  exact ⟨rfl,hr⟩

theorem race_free_any (arbitraryRF : ReadsFrom Node Source) (a b : Node) : ¬ DataRace graph arbitraryRF a b := by
  intro hr
  by_cases hab : a.val < b.val
  · exact hr.notForward (causal_of_base hr.overlap hab)
  by_cases hba : b.val < a.val
  · obtain ⟨location,ha,hb⟩ := hr.overlap
    exact hr.notBackward (causal_of_base ⟨location,hb,ha⟩ hba)
  have he : a = b := Fin.ext (by omega)
  subst b
  rcases hr.conflict with ⟨location,value,hw⟩ | ⟨location,value,hw⟩
  all_goals exact hr.notStrong (write_self_strong hw)

theorem race_free (a b : Node) : ¬ DataRace graph rf a b := race_free_any rf a b

theorem memory_witness : MemoryConditions graph initial rf co := by
  apply ranked_co_conditions rank
  · intro a b hp
    exact hp.elim
  · intro a b hb
    exact hb
  · exact race_free
  · intro location a b va vb ha hb he
    exact Fin.ext he
  · intro node location value hr
    obtain ⟨rfl,hp⟩ := read_inventory hr
    change graph.writeByte 0 location = some value
    exact hp
  · intro node writer location vr vw hr hw hs
    obtain ⟨rfl,_⟩ := read_inventory hr
    have hw' : writer = 0 := (Option.some.inj hs).symm
    subst writer
    decide
  · intro node writer location vr vw _ hr hw hc
    obtain ⟨rfl,_⟩ := read_inventory hr
    have hlt := ranked_co_write_lt hc
    fin_cases writer
    · change (0 : Nat) < 0 at hlt
      omega
    · simp [Graph.writeByte,graph,kind,Ptx.Event.Kind.writeByte] at hw
    · decide

theorem observer_witness : ObserverConditions graph initial rf co observer := by
  apply ranked_observation (by trivial)
  · intro location hm
    have he : location = loc := List.mem_singleton.mp hm
    subst location
    rfl
  · intro writer location value hw
    fin_cases writer <;> simp [writers]
    simp [Graph.writeByte,graph,kind,Ptx.Event.Kind.writeByte] at hw

theorem final_writer_selected : rankedWriterSelector graph rank writers loc = some 2 := by decide
theorem observed_last_write : observer.output loc = 42 := by decide
theorem first_write_before_second : co loc (some 0) (some 2) := ⟨rfl,rfl,by decide⟩
theorem distinct_async_agents : graph.agent 0 ≠ graph.agent 2 := by decide
theorem first_read_from_first_write : rf 1 loc = some 0 := rfl

def staleObserver : Observation Nat Source := selectedObservation graph initial (fun _ => some 0) [loc]

theorem stale_observer_rejected : ¬ ObserverConditions graph initial rf co staleObserver := by
  intro ho
  have he := race_free_eligible race_free (0 : Node) loc
  have hw : graph.writeByte 2 loc = some 42 := rfl
  exact ho.noStale loc (List.mem_singleton_self _) he.1 2 42 hw first_write_before_second

theorem unique_writer_premise_fails : ¬ (∀ location a b va vb,
    graph.writeByte a location = some va → graph.writeByte b location = some vb → a = b) := by
  intro h
  have he : (0 : Node) = 2 := h loc 0 2 7 42 rfl rfl
  have hn : (0 : Node) ≠ 2 := by decide
  exact hn he

theorem phase_source_for_all_witnesses (arbitraryRF : ReadsFrom Node Source) (arbitraryCo : Coherence Source)
    (hc : MemoryConditions graph initial arbitraryRF arbitraryCo) : arbitraryRF 1 loc = some 0 := by
  apply phase_writer_source hc (race_free_eligible (race_free_any arbitraryRF) 1 loc)
    (show graph.writeByte 0 loc = some 7 by rfl) (show graph.readByte 1 loc = some 7 by rfl)
  · exact causal_of_base ⟨loc,Or.inr rfl,Or.inl rfl⟩ (by change (0 : Nat) < 1; decide)
  · intro other value hw
    fin_cases other
    · exact Or.inl rfl
    · simp [Graph.writeByte,graph,kind,Ptx.Event.Kind.writeByte] at hw
    · exact Or.inr (Or.inr (causal_of_base ⟨loc,Or.inl rfl,Or.inr rfl⟩ (by change (1 : Nat) < 2; decide)))

theorem future_source_rejected (arbitraryCo : Coherence Source) :
    ¬ MemoryConditions graph initial (fun _ _ => some 2) arbitraryCo := by
  intro hc
  have hh := phase_source_for_all_witnesses _ _ hc
  have hn : (some (2 : Node) : Source) ≠ some 0 := by decide
  exact hn hh

end Ptx.MemoryGraphRankedTests
