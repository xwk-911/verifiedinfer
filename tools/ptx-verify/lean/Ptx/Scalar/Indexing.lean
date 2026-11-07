import Ptx.Scalar.Geometry

/-! Shared fixed-width bounds for runtime 2-D indexing. These constrain index
arithmetic, not GPU launch limits or allocation validity. -/
namespace Ptx.Scalar.Indexing
open Ptx.ISA

structure Bounds (ctx : Scalar.Context) : Prop where
  bx : ctx.id.cta.x < 2^32
  byBound : ctx.id.cta.y < 2^32
  sx : ctx.block.x < 2^32
  sy : ctx.block.y < 2^32
  tx : ctx.id.tid.x < 2^32
  ty : ctx.id.tid.y < 2^32
  rowBound : row ctx.block ctx.id < 2^32
  colBound : col ctx.block ctx.id < 2^32

theorem row_below_grid {g : Geometry} {id : ThreadId} (hv : id.Valid g) :
    row g.block id < g.grid.y*g.block.y := by
  have hcta := hv.1.2.1
  have hm := Nat.mul_le_mul_right g.block.y (by omega : id.cta.y+1 ≤ g.grid.y)
  have ht := Nat.add_lt_add_left hv.2.2.1 (id.cta.y*g.block.y)
  simp only [row,Nat.add_mul,Nat.one_mul] at *
  omega

theorem col_below_grid {g : Geometry} {id : ThreadId} (hv : id.Valid g) :
    col g.block id < g.grid.x*g.block.x := by
  have hcta := hv.1.1
  have hm := Nat.mul_le_mul_right g.block.x (by omega : id.cta.x+1 ≤ g.grid.x)
  have ht := Nat.add_lt_add_left hv.2.1 (id.cta.x*g.block.x)
  simp only [col,Nat.add_mul,Nat.one_mul] at *
  omega

theorem bounds_of_launch {g : Geometry}
    (gx : g.grid.x < 2^32) (gy : g.grid.y < 2^32)
    (bx : g.block.x < 2^32) (byBound : g.block.y < 2^32)
    (hx : g.grid.x*g.block.x ≤ 2^32) (hy : g.grid.y*g.block.y ≤ 2^32)
    {id : ThreadId} (hv : id.Valid g) (params : Bindings) :
    Bounds {id := id,params := params,block := g.block} := by
  have hr := row_below_grid hv
  have hc := col_below_grid hv
  constructor
  · change id.cta.x < 2^32
    have h := hv.1.1
    omega
  · change id.cta.y < 2^32
    have h := hv.1.2.1
    omega
  · exact bx
  · exact byBound
  · change id.tid.x < 2^32
    have h := hv.2.1
    omega
  · change id.tid.y < 2^32
    have h := hv.2.2.1
    omega
  · change row g.block id < 2^32
    omega
  · change col g.block id < 2^32
    omega


end Ptx.Scalar.Indexing
