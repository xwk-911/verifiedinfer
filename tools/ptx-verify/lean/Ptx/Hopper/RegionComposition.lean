import Ptx.Hopper.RegionLoans
import Mathlib.Data.List.Pairwise

/-! Composition of region certificates preserves exact use/mode coverage.
Renaming changes only logical buffers and tickets, never byte regions or work.
-/
namespace Ptx.Hopper.Progress.Regions
open Ptx.ISA
noncomputable section

def Region.Disjoint (left right : Region) : Prop :=
  left.base.space ≠ right.base.space ∨ left.base.address+left.bytes ≤ right.base.address ∨ right.base.address+right.bytes ≤ left.base.address

theorem holds_check {protocol bid loan} : Ptx.Async.Holds protocol bid loan ↔
    (protocol.buffers[bid]?.any (fun buffer => buffer.alive && decide (loan ∈ buffer.loans))) = true := by
  cases hget : protocol.buffers[bid]? <;> simp [Ptx.Async.Holds,hget,Option.any]

theorem disjoint_contains {left right loc} (hd : Region.Disjoint left right)
    (hl : left.Contains loc) (hr : right.Contains loc) : False := by
  rcases hd with hs | ha | hb
  · exact hs (hl.1.symm.trans hr.1)
  · have := hl.2; have := hr.2; omega
  · have := hl.2; have := hr.2; omega

theorem separated_of_pairwise (regions : List Region) (hd : regions.Pairwise Region.Disjoint) :
    Separated (fun bid => regions[bid]?) := by
  intro left right a b ha hb hne loc hla hlb
  obtain ⟨hl,hea⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hr,heb⟩ := List.getElem?_eq_some_iff.mp hb
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact disjoint_contains (hea ▸ heb ▸ (List.pairwise_iff_getElem.mp hd left right hl hr hlt)) hla hlb
  · exact disjoint_contains (heb ▸ hea ▸ (List.pairwise_iff_getElem.mp hd right left hr hl hgt)) hlb hla

def Binding.rename (buffers : Nat → Nat) (tickets : Ptx.Async.Ticket → Ptx.Async.Ticket) (binding : Binding) : Binding :=
  {binding with buffer := buffers binding.buffer,ticket := tickets binding.ticket}

theorem covers_rename {resolve descriptor candidate scope bindings}
    (hc : Covers resolve descriptor candidate scope bindings) (buffers tickets) :
    Covers resolve descriptor candidate scope (bindings.map (Binding.rename buffers tickets)) := by
  intro work control node loc mode hw hu
  obtain ⟨binding,hmem,hwork,hmode,hregion⟩ := hc _ _ _ _ _ hw hu
  exact ⟨binding.rename buffers tickets,List.mem_map.mpr ⟨binding,hmem,rfl⟩,hwork,hmode,hregion⟩

theorem covers_subset {resolve descriptor candidate scope before after}
    (hc : Covers resolve descriptor candidate scope before) (hsub : ∀ binding ∈ before, binding ∈ after) :
    Covers resolve descriptor candidate scope after := by
  intro work control node loc mode hw hu
  obtain ⟨binding,hmem,hwork,hmode,hregion⟩ := hc _ _ _ _ _ hw hu
  exact ⟨binding,hsub _ hmem,hwork,hmode,hregion⟩

end
end Ptx.Hopper.Progress.Regions
