import Ptx.Hopper.TmaSourceOrder

/-! Adjacent resource-history swaps preserve actual inventory multiplicities.
Source-forward and protocol checks remain explicit; this rule does not grant
unified control, publication or memory admission to the swapped history. -/
namespace Ptx.Hopper.Tma
noncomputable section

theorem pairwise_adjacent_swap {α : Type} {relation : α → α → Prop} {beforeEntries rest : List α} {a b : α}
    (hp : (beforeEntries++a::b::rest).Pairwise relation) (hba : relation b a) :
    (beforeEntries++b::a::rest).Pairwise relation := by
  obtain ⟨hprefix,htail,hcross⟩ := List.pairwise_append.mp hp
  obtain ⟨ha,hbr⟩ := List.pairwise_cons.mp htail
  obtain ⟨hb,hr⟩ := List.pairwise_cons.mp hbr
  apply List.pairwise_append.mpr
  refine ⟨hprefix,?_,?_⟩
  · apply List.pairwise_cons.mpr
    refine ⟨?_,List.pairwise_cons.mpr ⟨?_,hr⟩⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hba
      · exact hb x hx
    · intro x hx
      exact ha x (List.mem_cons_of_mem _ hx)
  · intro x hx y hy
    apply hcross x hx y
    rcases List.mem_cons.mp hy with rfl | hy
    · simp
    · rcases List.mem_cons.mp hy with rfl | hy
      · simp
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy)

theorem history_adjacent_swap {resolve candidate loc beforeEntries rest a b}
    (hh : HistoryValid resolve candidate loc (beforeEntries++a::b::rest))
    (hp : (beforeEntries++a::b::rest).Pairwise SourceForward) (hba : SourceForward b a)
    (hprotocol : Mbarrier.Admitted ((beforeEntries++b::a::rest).map Entry.operation)) :
    HistoryValid resolve candidate loc (beforeEntries++b::a::rest) := by
  have hperm : (beforeEntries++b::a::rest).Perm (beforeEntries++a::b::rest) :=
    (List.Perm.refl beforeEntries).append (List.Perm.swap a b rest)
  have hu : ((beforeEntries++b::a::rest).map Entry.origin).Nodup := (hperm.map Entry.origin).nodup_iff.mpr hh.unique
  exact ⟨hu,hperm.trans hh.exhaustive,source_order_of_pairwise hu (pairwise_adjacent_swap hp hba),hprotocol⟩

end
end Ptx.Hopper.Tma
