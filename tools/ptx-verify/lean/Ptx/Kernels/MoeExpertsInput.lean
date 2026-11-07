import Ptx.Kernels.MoeExpertsLoop
import Ptx.Scalar.Indexing

/-! Runtime words and the declared source parameter bindings. Address/region
and memory-agreement duties are separate from input and index typing. -/
namespace Ptx.MoeExperts
open Ptx.ISA Ptx.Scalar

structure Inputs where
  x : Nat
  w : Nat
  r : Nat
  h : Nat
  m : Nat
  n : Nat
  k : Nat
  x64 : x < 2^64
  w64 : w < 2^64
  r64 : r < 2^64
  h64 : h < 2^64
  m32 : m < 2^32
  n32 : n < 2^32
  k32 : k < 2^32
structure Params (i : Inputs) (params : Bindings) : Prop where
  x : lookup "X" params = some i.x
  w : lookup "W" params = some i.w
  r : lookup "R" params = some i.r
  h : lookup "H" params = some i.h
  m : lookup "M" params = some i.m
  n : lookup "N" params = some i.n
  k : lookup "K" params = some i.k

abbrev IndexBounds := Indexing.Bounds

end Ptx.MoeExperts
