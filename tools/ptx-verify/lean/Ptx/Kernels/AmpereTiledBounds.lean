import Ptx.Kernels.AmpereTiledAddressRules

/-! Active copy bounds derived from Layout, including all eight bytes. There
are no extra bounds on zero-K inputs or unused one-past-end final pointers. -/
namespace Ptx.AmpereTiledBounds
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec
noncomputable section

theorem matrix_span {base rows stride row start count limit : Nat}
    (hr : row < rows) (hc : start+count ≤ stride) (hb : base+2*(rows*stride) ≤ limit) :
    base+2*(row*stride+start)+2*count ≤ limit := by
  have hm := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hr)
  rw [Nat.succ_mul] at hm
  omega

def copyStart (cfg : Config) (ctx : Scalar.Context) (step : Nat) (part : Fin 3) : Nat :=
  if part.val = 0 then cfg.a+2*((16*ctx.id.cta.y+ctx.id.tid.y)*cfg.k+16*step+4*ctx.id.tid.x)
  else if part.val = 1 then cfg.a+2*((16*ctx.id.cta.y+ctx.id.tid.y+8)*cfg.k+16*step+4*ctx.id.tid.x)
  else cfg.b+2*((8*ctx.id.cta.x+ctx.id.tid.y)*cfg.k+16*step+4*ctx.id.tid.x)

/-- Each live copy stays in its own input buffer, including the last byte.
The two input buffers may alias one another. -/
theorem copy_region {cfg : Config} (h : Layout cfg) {ctx : Scalar.Context}
    (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg) {step : Nat} (hs : step < cfg.k/16) (part : Fin 3) :
    (cfg.a ≤ copyStart cfg ctx step part ∧ copyStart cfg ctx step part+8 ≤ cfg.a+2*(cfg.m*cfg.k)) ∨
    (cfg.b ≤ copyStart cfg ctx step part ∧ copyStart cfg ctx step part+8 ≤ cfg.b+2*(cfg.n*cfg.k)) := by
  have ht := AmpereTiledGeometry.lane_coordinates hv
  have he := AmpereTiledGeometry.element_bounds h hv ha
  have hk := h.tiles.2.2
  have hi : 16*step+4*ctx.id.tid.x+4 ≤ cfg.k := by omega
  fin_cases part
  · left
    constructor
    · simp only [copyStart,ite_true]; omega
    · simpa [copyStart,Nat.add_assoc] using
        matrix_span (by omega : 16*ctx.id.cta.y+ctx.id.tid.y < cfg.m) hi (Nat.le_refl (cfg.a+2*(cfg.m*cfg.k)))
  · left
    constructor
    · simp [copyStart]
    · simpa [copyStart,Nat.add_assoc] using matrix_span he.1 hi (Nat.le_refl (cfg.a+2*(cfg.m*cfg.k)))
  · right
    constructor
    · simp [copyStart]
    · simpa [copyStart,Nat.add_assoc] using matrix_span he.2.1 hi (Nat.le_refl (cfg.b+2*(cfg.n*cfg.k)))

theorem copy_span {cfg : Config} (h : Layout cfg) {ctx : Scalar.Context}
    (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg) {step : Nat} (hs : step < cfg.k/16) (part : Fin 3) :
    copyStart cfg ctx step part+8 ≤ cfg.arenaBytes := by
  have ht := AmpereTiledGeometry.lane_coordinates hv
  have he := AmpereTiledGeometry.element_bounds h hv ha
  have hk := h.tiles.2.2
  have hkp : 0 < cfg.k := by omega
  have hi : 16*step+4*ctx.id.tid.x+4 ≤ cfg.k := by omega
  have hb := h.inputs ha hkp
  fin_cases part
  · simpa [copyStart,Nat.add_assoc] using matrix_span (by omega : 16*ctx.id.cta.y+ctx.id.tid.y < cfg.m) hi hb.1
  · simpa [copyStart,Nat.add_assoc] using matrix_span he.1 hi hb.1
  · simpa [copyStart,Nat.add_assoc] using matrix_span he.2.1 hi hb.2.1

theorem copy_pointer {cfg : Config} (h : Layout cfg) {ctx : Scalar.Context}
    (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg) (step : Nat) (part : Fin 3) :
    CopyStage.source (AmpereTiledLoop.pointersAt (AmpereTiledEntry.loopConfig cfg ctx) step) part =
      wrap 64 (copyStart cfg ctx step part) := by
  have hp := AmpereTiledAddressRules.global_formulas h hv ha
  fin_cases part <;>
    simp [CopyStage.source,AmpereTiledLoop.pointersAt,AmpereTiledEntry.loopConfig,copyStart,
      hp.1,hp.2.1,hp.2.2.1,Scalar.wrap_add_left] <;> congr 1 <;> ring

theorem copy_source {cfg : Config} (h : Layout cfg) {ctx : Scalar.Context}
    (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg) {step : Nat} (hs : step < cfg.k/16)
    (s : State) (payload : Fin 3 → List Symbolic.Byte) (part : Fin 3) :
    (CopyStage.operation ctx s (AmpereTiledLoop.pointersAt (AmpereTiledEntry.loopConfig cfg ctx) step) payload part).src =
      ⟨.global,copyStart cfg ctx step part⟩ := by
  have hb := copy_span h hv ha hs part
  have h64 : copyStart cfg ctx step part < 2^64 := by have hh := h.arena; omega
  simp only [CopyStage.operation,copy_pointer h hv ha,Scalar.wrap_idempotent]
  rw [show wrap 64 (copyStart cfg ctx step part) = copyStart cfg ctx step part from Nat.mod_eq_of_lt h64]

end
end Ptx.AmpereTiledBounds
