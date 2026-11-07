import Ptx.Event.Cells

/-! Reusable cell/byte output agreement for a written u32 region with a frame.
These are representation lemmas, not execution assumptions. Kernel proofs must
derive both postconditions from their actual semantics. Unknown frame bytes use
the same initial fallback and cannot be silently initialized to zero.
-/
namespace Ptx.Event.Cells
open Ptx.ISA

def Outside (dst count cell : Nat) : Prop := cell < dst ∨ dst+count ≤ cell
def Destination (dst count : Nat) (loc : Location) : Prop :=
  loc.space = .global ∧ 4*dst ≤ loc.address ∧ loc.address < 4*(dst+count)
def allocatedDomain (length : Nat) : List Location :=
  (List.range (4*length)).map (fun address => ⟨.global,address⟩)

structure RegionCellPost (before after : List (Option Nat)) (dst count : Nat) (values : Nat → Nat) : Prop where
  size : after.length = before.length
  values : ∀ i, i < count → after[dst+i]? = some (some (values i))
  frame : ∀ cell, Outside dst count cell → after[cell]? = before[cell]?

structure RegionBytePost (length dst count : Nat) (values : Nat → Nat) (initial output : ByteMap) : Prop where
  values : ∀ i, i < count → ∀ offset, offset < 4 →
    output (location (dst+i) offset) = wordByte (values i) offset
  frame : ∀ loc ∈ allocatedDomain length, ¬ Destination dst count loc → output loc = initial loc

theorem region_cell_in_domain {length cell offset : Nat} (hc : cell < length) (ho : offset < 4) :
    location cell offset ∈ allocatedDomain length :=
  List.mem_map.mpr ⟨4*cell+offset,List.mem_range.mpr (by omega),rfl⟩

theorem outside_location {dst count cell offset : Nat} (hc : Outside dst count cell) (ho : offset < 4) :
    ¬ Destination dst count (location cell offset) := by
  intro h
  simp only [Destination,location] at h
  simp only [Outside] at hc
  omega

theorem region_represents {before after dst count values initial output}
    (hi : Represents before initial) (hb : RegionBytePost before.length dst count values initial output)
    (hc : RegionCellPost before after dst count values) : Represents after output := by
  intro cell value hcell offset hoffset
  have hbound : cell < before.length := by
    have := (List.getElem?_eq_some_iff.mp hcell).1
    rw [hc.size] at this
    exact this
  by_cases hout : Outside dst count cell
  · have hbefore := (hc.frame cell hout).symm.trans hcell
    exact (hb.frame _ (region_cell_in_domain hbound hoffset) (outside_location hout hoffset)).trans
      (hi cell value hbefore offset hoffset)
  · have hinside : dst ≤ cell ∧ cell < dst+count := by
      simp only [Outside] at hout
      omega
    let i := cell-dst
    have hin : i < count := by dsimp [i]; omega
    have hsum : dst+i = cell := by dsimp [i]; omega
    have hv := hc.values i hin
    rw [hsum] at hv
    have he : value = values i := Option.some.inj (Option.some.inj (hcell.symm.trans hv))
    rw [he,← hsum]
    exact hb.values i hin offset hoffset

theorem region_encoding_agreement {before after dst count values initial output}
    (hi : Represents before initial) (hb : RegionBytePost before.length dst count values initial output)
    (hc : RegionCellPost before after dst count values) {cell offset : Nat}
    (hcell : cell < before.length) (hoffset : offset < 4) :
    output (location cell offset) = encode after initial (location cell offset) := by
  have hbound : cell < after.length := by rw [hc.size]; exact hcell
  cases hv : after[cell]? with
  | none => simp [List.getElem?_eq_getElem hbound] at hv
  | some value =>
    cases value with
    | some value =>
      exact (region_represents hi hb hc cell value hv offset hoffset).trans
        ((encode_represents after initial cell value hv offset hoffset).symm)
    | none =>
      have hout : Outside dst count cell := by
        apply Classical.byContradiction
        intro hn
        simp only [Outside,not_or] at hn
        have ht : cell-dst < count := by omega
        have hs : dst+(cell-dst) = cell := by omega
        have hw := hc.values (cell-dst) ht
        rw [hs,hv] at hw
        cases hw
      rw [encode_uninitialized hv offset hoffset]
      exact hb.frame _ (region_cell_in_domain hcell hoffset) (outside_location hout hoffset)

theorem region_domain_encoding {before after dst count values initial output}
    (hi : Represents before initial) (hb : RegionBytePost before.length dst count values initial output)
    (hc : RegionCellPost before after dst count values)
    (loc : Location) (hmem : loc ∈ allocatedDomain before.length) : output loc = encode after initial loc := by
  obtain ⟨address,haddress,rfl⟩ := List.mem_map.mp hmem
  have hbound : address < 4*before.length := List.mem_range.mp haddress
  have hcell : address/4 < before.length := by omega
  have hoffset : address%4 < 4 := Nat.mod_lt _ (by decide)
  have hloc : location (address/4) (address%4) = ⟨.global,address⟩ := by
    simp only [location,Location.mk.injEq,true_and]
    omega
  simpa only [hloc] using region_encoding_agreement hi hb hc hcell hoffset

end Ptx.Event.Cells
