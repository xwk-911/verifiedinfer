/-! Pure mathematical tensor-map view shared by opaque symbolic storage and
Hopper instructions. This is not the CUDA binary tensor-map layout. -/
namespace Ptx.ISA.TensorMap
structure Descriptor2D where
  base : Nat := 0
  width : Nat := 8
  height : Nat := 1
  rowStride : Nat := 16
  boxWidth : Nat := 8
  boxHeight : Nat := 1
  elementBytes : Nat := 2
  deriving Repr, DecidableEq

end Ptx.ISA.TensorMap
