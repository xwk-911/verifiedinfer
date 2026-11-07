import Ptx.Hopper.ControlPrefix
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card

/-! Finite valid downward-closed ranked cuts have actual one-node executions.
This is existence of a control-graph linearization, not physical scheduling
fairness, a memory-value transition simulation or runtime progress. -/
namespace Ptx.Hopper.Progress
open Ptx.ISA
noncomputable section

theorem finset_cut_reached {block candidate histories} (nodes : Finset Unified.ControlNode)
    (hv : Valid block candidate histories (fun node => node ∈ nodes))
    (rank : Unified.ControlNode → Nat)
    (hr : ∀ before after, Unified.ControlEdge block candidate histories before after → rank before < rank after) :
    Reached block candidate histories (fun node => node ∈ nodes) := by
  classical
  induction nodes using Finset.strongInductionOn with
  | _ nodes ih =>
    by_cases hn : nodes.Nonempty
    · obtain ⟨last,hlast,hmax⟩ := nodes.exists_max_image rank hn
      have hsub : nodes.erase last ⊂ nodes := Finset.erase_ssubset hlast
      have hvalid : Valid block candidate histories (fun node => node ∈ nodes.erase last) := by
        constructor
        · intro before after he ha
          have hb := hv.1 _ _ he (Finset.mem_of_mem_erase ha)
          have hne : before ≠ last := by
            intro heq
            subst before
            have hlt := hr last after he
            have hle := hmax after (Finset.mem_of_mem_erase ha)
            omega
          exact Finset.mem_erase.mpr ⟨hne,hb⟩
        · intro node hn
          exact hv.2 node (Finset.mem_of_mem_erase hn)
      have hbefore := ih _ hsub hvalid
      have hstep : Advance block candidate histories (fun node => node ∈ nodes.erase last)
          (fun node => node ∈ nodes.erase last ∨ node = last) := by
        refine .next last (hv.2 last hlast) (by simp) ?_
        intro before he
        have hb := hv.1 _ _ he hlast
        have hne : before ≠ last := by intro heq; subst before; have := hr last last he; omega
        exact Finset.mem_erase.mpr ⟨hne,hb⟩
      have heq : (fun node => node ∈ nodes.erase last ∨ node = last) = (fun node => node ∈ nodes) := by
        funext node
        apply propext
        constructor
        · rintro (hm | rfl)
          · exact Finset.mem_of_mem_erase hm
          · exact hlast
        · intro hm
          by_cases he : node = last
          · exact .inr he
          · exact .inl (Finset.mem_erase.mpr ⟨he,hm⟩)
      exact heq ▸ Reached.next hbefore hstep
    · have he : nodes = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst nodes
      simpa only [Finset.notMem_empty] using (Reached.empty (block := block) (candidate := candidate) (histories := histories))

theorem finite_valid_rank_reached {block candidate histories done}
    (inventory : List Unified.ControlNode) (hi : ∀ node, done node → node ∈ inventory)
    (hv : Valid block candidate histories done) (rank : Unified.ControlNode → Nat)
    (hr : ∀ before after, Unified.ControlEdge block candidate histories before after → rank before < rank after) :
    Reached block candidate histories done := by
  classical
  let nodes := inventory.toFinset.filter done
  have heq : (fun node => node ∈ nodes) = done := by
    funext node
    apply propext
    simp only [nodes,Finset.mem_filter,List.mem_toFinset]
    exact ⟨And.right,fun hd => ⟨hi node hd,hd⟩⟩
  rw [← heq] at hv ⊢
  exact finset_cut_reached nodes hv rank hr

end
end Ptx.Hopper.Progress
