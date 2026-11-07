import Ptx.MemoryGraph.Ordinary
import Ptx.MemoryGraph.ObservationWitness
import Ptx.Ampere.Memory

/-! A small model-level witness, independent of any kernel correctness claim.
It checks the generic construction on distinct async/scalar logical agents,
including an unordered counterexample. Actual source tests live in Ampere. -/
namespace Ptx.MemoryGraphTests
open Ptx.ISA Ptx.MemoryGraph

def owner : ThreadId := ⟨.zero,.zero⟩
def loc : Location := ⟨.global,0⟩
def graph (value : Nat) (ordered : Bool) : Graph Bool Nat := {
  kind := fun node => some (if node then .read loc [value] else .write loc [value])
  present := fun _ => True
  agent := fun node => if node then .thread owner else .operation owner 0 0
  po := fun _ _ => False
  base := fun a b => ordered = true ∧ a = false ∧ b = true
  complete := True
}
def rf : ReadsFrom Bool (Option Bool) := fun _ _ => some false
def initial : Ptx.Event.ByteMap Nat := fun _ => 0

theorem writer {value ordered node l v} (hw : (graph value ordered).writeByte node l = some v) : node = false := by
  cases node
  · rfl
  · simp [graph,Graph.writeByte,Ptx.Event.Kind.writeByte] at hw
theorem reader {value ordered node l v} (hr : (graph value ordered).readByte node l = some v) : node = true := by
  cases node
  · simp [graph,Graph.readByte,Ptx.Event.Kind.readByte] at hr
  · rfl
theorem unique {value ordered l a b va vb}
    (ha : (graph value ordered).writeByte a l = some va)
    (hb : (graph value ordered).writeByte b l = some vb) : a = b := (writer ha).trans (writer hb).symm

theorem legal_memory (value : Nat) :
    MemoryConditions (graph value true) initial rf (InitialCo (graph value true)) := by
  apply initial_co_conditions (fun b : Bool => if b then 1 else 0)
  · intro a b hp
    exact hp.elim
  · rintro a b ⟨_,rfl,rfl⟩
    decide
  · intro l a b va vb ha hb
    exact unique ha hb
  · intro r l v hr
    have he := reader hr
    subst r
    simpa [rf,writeSource,sourceByte,Sources.decode,graph,Graph.readByte,Graph.writeByte,
      Ptx.Event.Kind.readByte,Ptx.Event.Kind.writeByte] using hr
  · intro r w l vr vw hr hw _
    rw [reader hr,writer hw]
    decide
  · intro r w l vr vw _ _ hs
    cases hs

theorem race_free (value : Nat) (reads : ReadsFrom Bool (Option Bool)) (a b) :
    ¬ DataRace (graph value true) reads a b := by
  apply ordered_conflicts_no_races
  intro x y ho hc
  cases x <;> cases y
  · exact .inl ⟨.inl rfl,⟨loc,1⟩,rfl,rfl⟩
  · exact .inr (.inl (causal_of_base ho ⟨rfl,rfl,rfl⟩))
  · exact .inr (.inr (causal_of_base (by rcases ho with ⟨l,hx,hy⟩; exact ⟨l,hy,hx⟩) ⟨rfl,rfl,rfl⟩))
  · rcases hc with ⟨l,v,hw⟩ | ⟨l,v,hw⟩ <;> cases writer hw

theorem complete_observation_exists (value : Nat) (domain : List Location)
    (hg : ∀ l ∈ domain, l.space = .global) :
    ObserverConditions (graph value true) initial rf (InitialCo (graph value true))
      (selectedObservation (graph value true) initial (writerSelector (graph value true)) domain) :=
  unique_writers_observation True.intro hg (fun _ _ _ _ _ ha hb => unique ha hb)

theorem all_allowed_reads (value : Nat) (reads : ReadsFrom Bool (Option Bool)) (co : Coherence (Option Bool))
    (hc : MemoryConditions (graph value true) initial reads co) :
    reads true loc = some false := by
  have he := race_free_eligible (race_free value reads) true loc
  have hv : (graph value true).writeByte false loc = some value := by
    simp [graph,Graph.writeByte,Ptx.Event.Kind.writeByte,Ptx.Event.payloadByte]
  have hr : (graph value true).readByte true loc = some value := by
    simp [graph,Graph.readByte,Ptx.Event.Kind.readByte,Ptx.Event.payloadByte]
  rcases source_cases (reads true loc) with hs | ⟨w,hs⟩
  · exact (stale_initial_forbidden hc he.1 hv hr (causal_of_base
      ⟨loc,.inr (by rw [hv]; rfl),.inl (by rw [hr]; rfl)⟩ ⟨rfl,rfl,rfl⟩) hs).elim
  · have hw := write_read_value hc.agreement he hr hs
    have hid := writer hw
    simpa [hid,writeSource,Sources.encode] using hs

theorem unordered_access_races (value : Nat) (reads : ReadsFrom Bool (Option Bool)) :
    DataRace (graph value false) reads false true := by
  have hw : (graph value false).writeByte false loc = some value := by
    simp [graph,Graph.writeByte,Ptx.Event.Kind.writeByte,Ptx.Event.payloadByte]
  have hr : (graph value false).readByte true loc = some value := by
    simp [graph,Graph.readByte,Ptx.Event.Kind.readByte,Ptx.Event.payloadByte]
  refine ⟨⟨loc,.inr (by rw [hw]; rfl),.inl (by rw [hr]; rfl)⟩,.inl ⟨loc,value,hw⟩,?_,?_,?_⟩
  · rintro (⟨_,hb⟩ | ⟨_,_,_,hb⟩) <;> cases hb.1
  · rintro (⟨_,hb⟩ | ⟨_,_,_,hb⟩) <;> cases hb.1
  · rintro ⟨he | ⟨_,_,hs,_,_,_⟩,_⟩
    · cases he
    · simp [graph,Ptx.Event.Kind.strongScope] at hs

theorem unordered_read_ineligible (value : Nat) (reads : ReadsFrom Bool (Option Bool)) :
    ¬ Eligible (graph value false) reads true loc := by
  intro he
  apply he.2
  exact .inl ⟨false,by simp [graph,Graph.writeByte,Ptx.Event.Kind.writeByte,Ptx.Event.payloadByte],
    data_race_symm (unordered_access_races value reads)⟩

end Ptx.MemoryGraphTests
