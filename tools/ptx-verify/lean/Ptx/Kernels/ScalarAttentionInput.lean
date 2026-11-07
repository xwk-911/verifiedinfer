import Ptx.Generated.ScalarFlashAttention
import Ptx.Scalar.Indexing
import Ptx.Scalar.RegisterFrame

/-! Runtime inputs for the actual attention source. Width/index hypotheses are
explicit; they do not assert memory consistency or the desired kernel output. -/
namespace Ptx.ScalarAttention
open Ptx.ISA Ptx.Scalar

abbrev code := Generated.scalar_flash_attention.program
abbrev IndexBounds := Scalar.Indexing.Bounds

structure Inputs where
  q : Nat
  key : Nat
  value : Nat
  output : Nat
  scale : Nat
  m : Nat
  n : Nat
  dim : Nat
  q64 : q < 2^64
  key64 : key < 2^64
  value64 : value < 2^64
  output64 : output < 2^64
  scale64 : scale < 2^64
  m32 : m < 2^32
  n32 : n < 2^32
  dim32 : dim < 2^32

structure Params (i : Inputs) (params : Bindings) : Prop where
  q : lookup "Q" params = some i.q
  key : lookup "K" params = some i.key
  value : lookup "V" params = some i.value
  output : lookup "O" params = some i.output
  scale : lookup "Scale" params = some i.scale
  m : lookup "M" params = some i.m
  n : lookup "N" params = some i.n
  dim : lookup "D" params = some i.dim

end Ptx.ScalarAttention
