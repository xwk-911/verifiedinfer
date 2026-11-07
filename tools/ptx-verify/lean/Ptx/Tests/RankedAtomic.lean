import Ptx.Tests.AtomicMemory
import Ptx.Event.RankedObservation

/-! The ranked witness construction admits a genuine unsplit RMW. In particular,
its internal read-to-write step does not require rank(event)<rank(event). This
does not substitute for the two-CTA atomic-dispatch existence proof. -/
namespace Ptx.RankedAtomicTests
open Ptx.ISA Ptx.Event
open Ptx.AtomicMemoryTests
noncomputable section

def rank : EventId → Nat := fun _ => 0
def writers : List EventId := [event]

theorem ranked_consistent : GenericMemoryConditions graph initial rf (RankedCo graph initial rank) := by
  apply ranked_co_conditions rank
  · intro a b hpo
    exact (no_base_edges a b (Or.inl hpo)).elim
  · rintro a b ⟨_,bid,generation,_,hreturn⟩
    exact (no_returns b bid generation hreturn).elim
  · rintro a b ⟨_,_,_,_,_,bid,generation,hreturn,_⟩
    exact (no_returns b bid generation hreturn).elim
  · exact consistent.barriers
  · exact no_races
  · intro loc a b va vb ha hb _
    exact (writer_shape ha).trans (writer_shape hb).symm
  · intro read loc value hr
    exact consistent.agreement read loc value (race_free_eligible no_races read loc) hr
  · intro read writer loc vr vw _ _ hs
    cases hs
  · intro read writer loc vr vw hne hr hw _
    have hread := present_shape (accesses_present (Or.inl (by rw [hr]; rfl)))
    exact (hne (hread.trans (writer_shape hw).symm)).elim

theorem ranked_observed : ObserverConditions graph initial rf (RankedCo graph initial rank)
    (selectedObservation graph initial (rankedWriterSelector graph rank writers) domain) := by
  apply ranked_observation complete
  · intro loc hmem
    obtain ⟨offset,_,rfl⟩ := List.mem_map.mp hmem
    rfl
  · intro writer loc value hw
    simp only [writers,List.mem_singleton]
    exact writer_shape hw

theorem ranked_observes_one :
    (selectedObservation graph initial (rankedWriterSelector graph rank writers) domain).output base = .bits (byte 1) := by rfl

end
end Ptx.RankedAtomicTests
