import Ptx.Scalar.IntegerMemory
import Ptx.Scalar.Regions
import Ptx.Scalar.Geometry

/-! Independent two-expert, normalized top-1 MoE specification. Gates have two
finite-real scores per token; ties choose expert zero. Each expert is a dense
linear map without bias. Top-1 combine gathers the selected result with unit
weight. Sparse expert planes do not imply packing, capacity limits or top-k>1. -/
namespace Ptx.Moe
open Ptx.ISA Ptx.Scalar
noncomputable section

abbrev Matrix := Nat → Nat → ℝ
abbrev Weights := Nat → Nat → Nat → ℝ

def selected (gates : Matrix) (row : Nat) : Nat := if gates row 0 < gates row 1 then 1 else 0
def linear (x : Matrix) (weights : Weights) (expert row col : Nat) : Nat → ℝ
  | 0 => 0
  | count+1 => x row count*weights expert count col+linear x weights expert row col count
def output (gates x : Matrix) (weights : Weights) (row col inner : Nat) : ℝ :=
  linear x weights (selected gates row) row col inner

def Routes (gates : Matrix) (rows base : Nat) (memory : Scalar.ByteMap) : Prop :=
  ∀ row, row < rows → RepresentsU32 memory ⟨.global,base+4*row⟩ (selected gates row)
def Experts (gates x : Matrix) (weights : Weights) (rows cols inner base : Nat) (memory : Scalar.ByteMap) : Prop :=
  ∀ row col, row < rows → col < cols → RepresentsReal .f32 memory
    ⟨.global,base+4*((selected gates row*rows+row)*cols+col)⟩ (output gates x weights row col inner)
def Post (gates x : Matrix) (weights : Weights) (rows cols inner base : Nat) (memory : Scalar.ByteMap) : Prop :=
  ∀ row col, row < rows → col < cols → RepresentsReal .f32 memory
    ⟨.global,base+4*(row*cols+col)⟩ (output gates x weights row col inner)

theorem selected_bound (gates : Matrix) (row : Nat) : selected gates row < 2 := by
  unfold selected
  split <;> decide
theorem selected_one {gates : Matrix} {row : Nat} (h : gates row 0 < gates row 1) : selected gates row = 1 := by
  simp [selected,h]
theorem selected_zero {gates : Matrix} {row : Nat} (h : gates row 1 ≤ gates row 0) : selected gates row = 0 := by
  simp [selected,not_lt.mpr h]
theorem tie_zero {gates : Matrix} {row : Nat} (h : gates row 0 = gates row 1) : selected gates row = 0 := by
  simp [selected,h]
theorem selected_maximal (gates : Matrix) (row : Nat) {expert : Nat} (he : expert < 2) :
    gates row expert ≤ gates row (selected gates row) := by
  rcases (show expert = 0 ∨ expert = 1 by omega) with rfl | rfl <;>
    unfold selected <;> split <;> simp_all [le_of_lt,le_of_not_gt]

theorem expert_index_injective {rows cols e f r s c d : Nat}
    (hr : r < rows) (hs : s < rows) (hc : c < cols) (hd : d < cols)
    (he : (e*rows+r)*cols+c = (f*rows+s)*cols+d) : e = f ∧ r = s ∧ c = d := by
  obtain ⟨hrow,hcol⟩ := matrix_index_injective hc hd he
  obtain ⟨hexpert,hlocal⟩ := tile_coordinate_injective hr hs hrow
  exact ⟨hexpert,hlocal,hcol⟩
theorem selected_index_bound (gates : Matrix) {rows cols row col : Nat}
    (hr : row < rows) (hc : col < cols) :
    (selected gates row*rows+row)*cols+col < (2*rows)*cols :=
  matrix_index_lt (matrix_index_lt (selected_bound gates row) hr) hc

@[simp] theorem zero_inner (gates x : Matrix) (weights : Weights) (row col : Nat) : output gates x weights row col 0 = 0 := rfl

end
end Ptx.Moe
