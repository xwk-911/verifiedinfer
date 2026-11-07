import Ptx.Kernels.ScalarMatmulLoopTrace
import Ptx.Scalar.Indexing

/-! Runtime input and thread-index bounds for the actual scalar matmul source.
These are explicit value/geometry preconditions, not memory-consistency premises
or assumptions that the kernel result equals its specification.
-/
namespace Ptx.ScalarMatmul
open Ptx.ISA Ptx.Scalar

structure Inputs where
  a : Nat
  b : Nat
  c : Nat
  m : Nat
  n : Nat
  k : Nat
  a64 : a < 2^64
  b64 : b < 2^64
  c64 : c < 2^64
  m32 : m < 2^32
  n32 : n < 2^32
  k32 : k < 2^32

structure Params (i : Inputs) (params : Bindings) : Prop where
  a : lookup "A" params = some i.a
  b : lookup "B" params = some i.b
  c : lookup "C" params = some i.c
  m : lookup "M" params = some i.m
  n : lookup "N" params = some i.n
  k : lookup "K" params = some i.k

abbrev IndexBounds := Scalar.Indexing.Bounds

theorem row_below_grid {g : Geometry} {id : ThreadId} (hv : id.Valid g) :
    row g.block id < g.grid.y*g.block.y := Scalar.Indexing.row_below_grid hv

theorem col_below_grid {g : Geometry} {id : ThreadId} (hv : id.Valid g) :
    col g.block id < g.grid.x*g.block.x := Scalar.Indexing.col_below_grid hv

theorem index_bounds_of_launch {g : Geometry}
    (gx : g.grid.x < 2^32) (gy : g.grid.y < 2^32)
    (bx : g.block.x < 2^32) (byBound : g.block.y < 2^32)
    (hx : g.grid.x*g.block.x ≤ 2^32) (hy : g.grid.y*g.block.y ≤ 2^32)
    {id : ThreadId} (hv : id.Valid g) (params : Bindings) :
    IndexBounds {id := id,params := params,block := g.block} :=
  Scalar.Indexing.bounds_of_launch gx gy bx byBound hx hy hv params


end Ptx.ScalarMatmul
