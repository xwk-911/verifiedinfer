import Ptx.Hopper.TmaObservation

/-! A reusable list-order rule for source-matched resource constructions.
It grants source order only, not a memory happens-before or control edge. -/
namespace Ptx.Hopper.Tma
open Ptx.ISA
noncomputable section

def SourceForward (first last : Entry) : Prop :=
  match first.origin,last.origin with
  | .source a,.source b => a.thread = b.thread → a.serial < b.serial
  | _,_ => True

theorem source_forward_no_reverse {first last} (hf : SourceForward first last) : ¬SourceBefore last.origin first.origin := by
  cases ha : first.origin <;> cases hb : last.origin <;> simp_all only [SourceForward,SourceBefore,not_false_eq_true]
  next a b =>
    intro h
    have hh := hf h.1.symm
    omega

theorem source_before_irrefl (origin : Origin) : ¬SourceBefore origin origin := by
  cases origin <;> simp [SourceBefore]

theorem source_order_of_pairwise {entries : List Entry} (hu : (entries.map Entry.origin).Nodup)
    (hp : entries.Pairwise SourceForward) : SourceOrder entries := by
  intro first hf last hl hbefore
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hf
  obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hl
  rw [origin_index hu hi,origin_index hu hj]
  obtain ⟨hib,hiv⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjb,hjv⟩ := List.getElem?_eq_some_iff.mp hj
  by_contra hn
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_gt hn) with hlt | heq
  · have hh := hp.rel_getElem_of_lt hjb hib hlt
    rw [hiv,hjv] at hh
    exact source_forward_no_reverse hh hbefore
  · subst j
    have he : first = last := hiv.symm.trans hjv
    rw [← he] at hbefore
    exact source_before_irrefl _ hbefore

end
end Ptx.Hopper.Tma
