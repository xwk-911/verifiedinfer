import Ptx.Kernels.AmpereTiledSpec
import Mathlib.Tactic.NormNum

/-! Specification boundary checks. These do not assert source correctness. -/
namespace Ptx.AmpereTiledSpecTests
open Ptx.ISA Ptx.AmpereTiledSpec
noncomputable section

def zeroK : Config := ⟨16,8,0,1,1,4,520⟩
def inactive : Config := ⟨0,16,4294967280,1,1,1,64⟩
def initial : Ptx.Event.ByteMap Symbolic.Byte := fun _ => .bits (byte 165)

theorem zero_k_layout : Layout zeroK := by
  constructor
  · decide
  · decide
  · decide
  · decide
  · intro _
    decide
  · intro _ hk
    change (0 : Nat) < 0 at hk
    omega

theorem inactive_layout : Layout inactive := by
  constructor
  · decide
  · decide
  · decide
  · decide
  · intro ha
    have hh := ha.1
    change (0 : Nat) < 0 at hh
    omega
  · intro ha _
    have hh := ha.1
    change (0 : Nat) < 0 at hh
    omega

theorem zero_k_arbitrary_input_spec (a b : Matrix) : Input zeroK a b initial := zero_k_no_input rfl a b initial
theorem inactive_arbitrary_input_spec (a b : Matrix) : Input inactive a b initial := empty_output_no_input (.inl rfl) a b initial

theorem zero_k_pre_inhabited (a b : Matrix) :
    Pre zeroK a b ⟨geometry zeroK,params zeroK,initial⟩ :=
  ⟨zero_k_layout,zero_k_arbitrary_input_spec a b,rfl,rfl⟩

def nonzero : Config := ⟨16,8,32,0,2048,4096,4612⟩
theorem b_column_major : (bLocation nonzero 3 5).address = 2374 := by rfl
theorem output_row_major : (cLocation nonzero 3 5).address = 4212 := by rfl
theorem full_tiles : 16*(nonzero.k/16) = 32 := by decide

def a : Matrix := fun _ t => (t+1 : Nat)
def b : Matrix := fun _ _ => 1
theorem one_block_sum : partialProduct a b 0 0 1 = 136 := by
  norm_num [partialProduct,product,a,b,Finset.sum_range_succ]
theorem two_block_sum : partialProduct a b 0 0 2 = 528 := by
  norm_num [partialProduct,product,a,b,Finset.sum_range_succ]

end
end Ptx.AmpereTiledSpecTests
