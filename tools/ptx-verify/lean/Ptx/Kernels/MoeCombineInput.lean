import Ptx.Generated.MoeCombine
import Ptx.Kernels.MoeSpec
import Ptx.Scalar.Indexing
import Ptx.Scalar.Control

/-! Source parameters of the normalized top-1 gather. Gate selection and the
expert recurrence stay in the independent MoE specification. -/
namespace Ptx.MoeCombine
open Ptx.ISA Ptx.Scalar

abbrev code := Generated.moe_combine.program
structure Inputs where
  r : Nat
  h : Nat
  y : Nat
  m : Nat
  n : Nat
  r64 : r < 2^64
  h64 : h < 2^64
  y64 : y < 2^64
  m32 : m < 2^32
  n32 : n < 2^32
structure Params (i : Inputs) (params : Bindings) : Prop where
  r : lookup "R" params = some i.r
  h : lookup "H" params = some i.h
  y : lookup "Y" params = some i.y
  m : lookup "M" params = some i.m
  n : lookup "N" params = some i.n
abbrev IndexBounds := Indexing.Bounds

end Ptx.MoeCombine
