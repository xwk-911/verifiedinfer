import Ptx.Kernels.AmpereTiledSource
import Ptx.Ampere.TiledLayout
import Mathlib.Tactic.Ring

/-! Independent layout equations for the source-produced pointer formulas.
Global pointers remain modulo 2^64 here; read bounds remain separate duties. -/
namespace Ptx.AmpereTiledAddressRules
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec
open Ptx.AmpereTiledAddresses
noncomputable section
abbrev Config := AmpereTiledSpec.Config

theorem wrap_mul_left (width a b : Nat) : wrap width (wrap width a*b) = wrap width (a*b) := by
  simp [wrap,Nat.mul_mod]

theorem index_values {cfg : Config} (h : Layout cfg) {ctx : Scalar.Context}
    (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg) :
    x ctx = ctx.id.tid.x ∧ y ctx = ctx.id.tid.y ∧ row ctx = 16*ctx.id.cta.y+ctx.id.tid.y ∧
      col ctx = 8*ctx.id.cta.x+ctx.id.tid.y ∧ cCol ctx = 8*ctx.id.cta.x+2*ctx.id.tid.x := by
  have ht := AmpereTiledGeometry.lane_coordinates hv
  have hb := AmpereTiledGeometry.element_bounds h hv ha
  have h32 := h.dimensions
  have hx : x ctx = ctx.id.tid.x := Nat.mod_eq_of_lt (by omega)
  have hy : y ctx = ctx.id.tid.y := Nat.mod_eq_of_lt (by omega)
  refine ⟨hx,hy,?_,?_,?_⟩
  · simp only [row,(AmpereTiledGeometry.tile_rows h hv).1,hy]
    exact Nat.mod_eq_of_lt (by omega)
  · simp only [col,(AmpereTiledGeometry.tile_cols h hv).1,hy]
    exact Nat.mod_eq_of_lt (by omega)
  · simp only [cCol,(AmpereTiledGeometry.tile_cols h hv).1,hx]
    rw [show wrap 32 (ctx.id.tid.x*2) = 2*ctx.id.tid.x by
      rw [Nat.mul_comm]; exact Nat.mod_eq_of_lt (by omega)]
    exact Nat.mod_eq_of_lt (by omega)

theorem global_formulas {cfg : Config} (h : Layout cfg) {ctx : Scalar.Context}
    (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg) :
    a cfg ctx = wrap 64 (cfg.a+2*((16*ctx.id.cta.y+ctx.id.tid.y)*cfg.k+4*ctx.id.tid.x)) ∧
    ah cfg ctx = wrap 64 (cfg.a+2*((16*ctx.id.cta.y+ctx.id.tid.y+8)*cfg.k+4*ctx.id.tid.x)) ∧
    b cfg ctx = wrap 64 (cfg.b+2*((8*ctx.id.cta.x+ctx.id.tid.y)*cfg.k+4*ctx.id.tid.x)) ∧
    c cfg ctx = wrap 64 (cfg.c+4*((16*ctx.id.cta.y+ctx.id.tid.y)*cfg.n+8*ctx.id.cta.x+2*ctx.id.tid.x)) ∧
    ch cfg ctx = wrap 64 (cfg.c+4*((16*ctx.id.cta.y+ctx.id.tid.y+8)*cfg.n+8*ctx.id.cta.x+2*ctx.id.tid.x)) := by
  have hi := index_values h hv ha
  have hk : wrap 32 cfg.k = cfg.k := Nat.mod_eq_of_lt h.dimensions.2.2
  have hn : wrap 32 cfg.n = cfg.n := Nat.mod_eq_of_lt h.dimensions.2.1
  simp only [a,ah,b,c,ch,aOffset,bOffset,cOffset,smallA,hi.1,hi.2.2.1,hi.2.2.2.1,hi.2.2.2.2,hk,hn,
    wrap_mul_left,Scalar.wrap_add,Scalar.wrap_add_left,Scalar.wrap_add_right]
  constructor
  · congr 1 <;> ring
  constructor
  · congr 1 <;> ring
  constructor
  · congr 1 <;> ring
  constructor <;> congr 1 <;> ring

theorem shared_formulas (ctx : Scalar.Context) (hx : ctx.id.tid.x < 4) (hy : ctx.id.tid.y < 8) :
    sa ctx = 32*ctx.id.tid.y+8*ctx.id.tid.x ∧ sah ctx = 256+32*ctx.id.tid.y+8*ctx.id.tid.x ∧
      sb ctx = 512+32*ctx.id.tid.y+8*ctx.id.tid.x ∧ la ctx = 32*ctx.id.tid.y+4*ctx.id.tid.x ∧
      lb ctx = 512+32*ctx.id.tid.y+4*ctx.id.tid.x := by
  simp only [sa,sah,sb,la,lb,copyOffset,readOffset,x,y,wrap]
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  omega

theorem copy_destination {cfg : Config} {ctx : Scalar.Context} (hx : ctx.id.tid.x < 4) (hy : ctx.id.tid.y < 8)
    (s : State) (payload : Fin 3 → List Symbolic.Byte) (step : Nat) (part : Fin 3) :
    (CopyStage.operation ctx s (AmpereTiledLoop.pointersAt (AmpereTiledEntry.loopConfig cfg ctx) step) payload part).dst =
      ⟨.shared ctx.id.cta,Tiled.copyBase ⟨ctx.id.tid.x,hx⟩ ⟨ctx.id.tid.y,hy⟩ part⟩ := by
  have hs := shared_formulas ctx hx hy
  fin_cases part <;>
    simp [CopyStage.operation,CopyStage.destination,AmpereTiledLoop.pointersAt,AmpereTiledEntry.loopConfig,
      hs.1,hs.2.1,hs.2.2.1,Tiled.copyBase,wrap] <;>
    omega

theorem a_load_event {ctx : Scalar.Context} (hx : ctx.id.tid.x < 4) (hy : ctx.id.tid.y < 8)
    (wa : Fin 4 → PackedF16) (wb : Fin 2 → PackedF16) (reg : Fin 4) :
    (MmaBlock.readEvents ctx (la ctx) (lb ctx) wa wb)[reg.val]? =
      some (.ordinary (.read ⟨.shared ctx.id.cta,Tiled.aRead ⟨ctx.id.tid.x,hx⟩ ⟨ctx.id.tid.y,hy⟩ reg⟩ (wa reg).encode)) := by
  have hs := (shared_formulas ctx hx hy).2.2.2.1
  fin_cases reg <;> simp [MmaBlock.readEvents,hs,Tiled.aRead,wrap] <;>
    omega

theorem b_load_event {ctx : Scalar.Context} (hx : ctx.id.tid.x < 4) (hy : ctx.id.tid.y < 8)
    (wa : Fin 4 → PackedF16) (wb : Fin 2 → PackedF16) (reg : Fin 2) :
    (MmaBlock.readEvents ctx (la ctx) (lb ctx) wa wb)[4+reg.val]? =
      some (.ordinary (.read ⟨.shared ctx.id.cta,Tiled.bRead ⟨ctx.id.tid.x,hx⟩ ⟨ctx.id.tid.y,hy⟩ reg⟩ (wb reg).encode)) := by
  have hs := (shared_formulas ctx hx hy).2.2.2.2
  fin_cases reg <;> simp [MmaBlock.readEvents,hs,Tiled.bRead,wrap] <;>
    omega

end
end Ptx.AmpereTiledAddressRules
