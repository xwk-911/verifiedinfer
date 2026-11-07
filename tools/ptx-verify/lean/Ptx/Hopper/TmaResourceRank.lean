import Ptx.Hopper.TmaControl
import Mathlib.Data.List.Pairwise

/-! Resource serialization admits a rank whenever every checked history has
strictly increasing origin ranks. This rule supports arbitrary finite histories
and does not equate resource serialization with memory visibility. -/
namespace Ptx.Hopper.Tma
noncomputable section

theorem before_rank_lt {entries : List Entry} {rank : Node → Nat} {left right : Origin}
    (hp : (entries.map Entry.origin).Pairwise (fun a b => rank a.node < rank b.node))
    (hb : Before entries left right) : rank left.node < rank right.node := by
  have hl := List.idxOf_lt_length_iff.mpr hb.1
  have hr := List.idxOf_lt_length_iff.mpr hb.2.1
  have hh := List.Pairwise.rel_getElem_of_lt hl hr hp hb.2.2
  simpa only [List.getElem_idxOf] using hh
theorem resource_edge_rank_of_pairwise {histories : Ptx.ISA.Location → List Entry} {rank : Node → Nat}
    (hp : ∀ location, ((histories location).map Entry.origin).Pairwise (fun a b => rank a.node < rank b.node))
    {left right} (he : ResourceEdge histories left right) : rank left < rank right := by
  obtain ⟨location,a,_,b,_,hb,ha,hb'⟩ := he
  rw [← ha,← hb']
  exact before_rank_lt (hp location) hb

end
end Ptx.Hopper.Tma
