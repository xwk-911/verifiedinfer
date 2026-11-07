import Ptx.Kernels.AmpereTiledInit
import Mathlib.Tactic.Linarith

/-! Canonical-grid coordinates and guards derived from the independent Layout.
This states no physical GPU launch limit or memory/arithmetic correctness. -/
namespace Ptx.AmpereTiledGeometry
open Ptx.ISA Ptx.AmpereTiledSpec
noncomputable section

theorem tile_base_active {size width index : Nat} (hw : 0 < width) (hs : size%width = 0)
    (hi : index < max 1 (size/width)) (hp : 0 < size) : width*index < size := by
  have he : width*(size/width) = size := by simpa [hs] using Nat.mod_add_div size width
  have hq : 1 ≤ size/width := by nlinarith
  rw [max_eq_right hq] at hi
  have hm := Nat.mul_lt_mul_of_pos_left hi hw
  omega

theorem tile_base_bound {size width index : Nat} (hw : 0 < width) (hs : size%width = 0)
    (hi : index < max 1 (size/width)) (hb : size < 2^32) : width*index < 2^32 ∧ index < 2^32 := by
  by_cases hp : 0 < size
  · have hm := tile_base_active hw hs hi hp
    have hh : index ≤ width*index := by nlinarith
    omega
  · have hz : size = 0 := by omega
    subst size
    have hi0 : index = 0 := by simpa using hi
    subst index
    norm_num

theorem tile_rows {cfg : Config} (h : Layout cfg) {ctx : Scalar.Context}
    (hv : ctx.id.Valid (geometry cfg)) :
    AmpereTiledInit.tileRow ctx = 16*ctx.id.cta.y ∧ 16*ctx.id.cta.y < 2^32 := by
  have hi : ctx.id.cta.y < max 1 (cfg.m/16) := hv.1.2.1
  have hh := tile_base_bound (by decide : 0 < 16) h.tiles.1 hi h.dimensions.1
  refine ⟨?_,hh.1⟩
  simp only [AmpereTiledInit.tileRow,show wrap 32 ctx.id.cta.y = ctx.id.cta.y from Nat.mod_eq_of_lt hh.2]
  rw [Nat.mul_comm]
  exact Nat.mod_eq_of_lt hh.1

theorem tile_cols {cfg : Config} (h : Layout cfg) {ctx : Scalar.Context}
    (hv : ctx.id.Valid (geometry cfg)) :
    AmpereTiledInit.tileCol ctx = 8*ctx.id.cta.x ∧ 8*ctx.id.cta.x < 2^32 := by
  have hi : ctx.id.cta.x < max 1 (cfg.n/8) := hv.1.1
  have hh := tile_base_bound (by decide : 0 < 8) h.tiles.2.1 hi h.dimensions.2.1
  refine ⟨?_,hh.1⟩
  simp only [AmpereTiledInit.tileCol,show wrap 32 ctx.id.cta.x = ctx.id.cta.x from Nat.mod_eq_of_lt hh.2]
  rw [Nat.mul_comm]
  exact Nat.mod_eq_of_lt hh.1

theorem active_guards {cfg : Config} (h : Layout cfg) {ctx : Scalar.Context}
    (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg) :
    AmpereTiledInit.tileRow ctx < wrap 32 cfg.m ∧ AmpereTiledInit.tileCol ctx < wrap 32 cfg.n := by
  rw [(tile_rows h hv).1,(tile_cols h hv).1,
    show wrap 32 cfg.m = cfg.m from Nat.mod_eq_of_lt h.dimensions.1,
    show wrap 32 cfg.n = cfg.n from Nat.mod_eq_of_lt h.dimensions.2.1]
  exact ⟨tile_base_active (by decide) h.tiles.1 hv.1.2.1 ha.1,
    tile_base_active (by decide) h.tiles.2.1 hv.1.1 ha.2⟩

theorem lane_coordinates {cfg : Config} {ctx : Scalar.Context}
    (hv : ctx.id.Valid (geometry cfg)) : ctx.id.tid.x < 4 ∧ ctx.id.tid.y < 8 ∧ ctx.id.tid.z = 0 := by
  have hx : ctx.id.tid.x < 4 := hv.2.1
  have hy : ctx.id.tid.y < 8 := hv.2.2.1
  have hz : ctx.id.tid.z < 1 := hv.2.2.2
  exact ⟨hx,hy,by omega⟩

theorem element_bounds {cfg : Config} (h : Layout cfg) {ctx : Scalar.Context}
    (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg) :
    16*ctx.id.cta.y+ctx.id.tid.y+8 < cfg.m ∧
      8*ctx.id.cta.x+ctx.id.tid.y < cfg.n ∧ 8*ctx.id.cta.x+2*ctx.id.tid.x+1 < cfg.n := by
  have hm := tile_base_active (by decide : 0 < 16) h.tiles.1 hv.1.2.1 ha.1
  have hn := tile_base_active (by decide : 0 < 8) h.tiles.2.1 hv.1.1 ha.2
  have hmodm := h.tiles.1
  have hmodn := h.tiles.2.1
  have ht := lane_coordinates hv
  omega

end
end Ptx.AmpereTiledGeometry
