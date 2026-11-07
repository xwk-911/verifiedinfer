import Ptx.Kernels.ShuffleProbe

/-! Independent modular interpretation of the actual 3-D index and input
arithmetic. Input-word equality needs no no-overflow premise: u32 arithmetic
is a homomorphism modulo 2^32. Distinct output addresses need separate bounds. -/
namespace Ptx.Kernels.ShuffleProbe
open Ptx.ISA Ptx.Shuffle
noncomputable section

theorem raw_index_is_linear_mod_u32 (ctx : Scalar.Context) : rawIndex ctx = w32 (linear ctx.block ctx.id) := by
  simp [rawIndex,xProduct,yzIndex,yzProduct,w32,wrap,linear,Dim3.linear,
    Nat.add_mod,Nat.mul_mod,Nat.add_comm,Nat.mul_comm]

theorem input_word_is_linear_mod_u32 (input : Inputs) (ctx : Scalar.Context) :
    inputWord input ctx = w32 (input.base + linear ctx.block ctx.id) := by
  rw [inputWord,raw_index_is_linear_mod_u32]
  simp [w32,wrap,Nat.add_mod]

theorem same_warp_selected_linear {block origin peer mode b c}
    (hw : SameWarp block origin peer)
    (hl : lane block peer = (select mode (lane block origin) b c).source) :
    linear block peer = 32*(linear block origin/32) + (select mode (lane block origin) b c).source.toNat := by
  have hm := congrArg BitVec.toNat hl
  simp only [lane,BitVec.toNat_ofNat] at hm
  have hd := Nat.mod_add_div (linear block peer) 32
  have hwarp := hw.2
  simp only [lane] at ⊢
  omega

def expectedWord (mode : Mode) (input : Inputs) (ctx : Scalar.Context) : Nat :=
  w32 (input.base + 32*(linear ctx.block ctx.id/32) +
    (select mode (lane ctx.block ctx.id) (w32 input.b) (w32 input.c)).source.toNat)
def expectedPredicate (mode : Mode) (input : Inputs) (ctx : Scalar.Context) : Bool :=
  (select mode (lane ctx.block ctx.id) (w32 input.b) (w32 input.c)).predicate

theorem selected_peer_input_is_spec {mode input ctx peer}
    (hw : SameWarp ctx.block ctx.id peer)
    (hl : lane ctx.block peer = (select mode (lane ctx.block ctx.id) (w32 input.b) (w32 input.c)).source) :
    inputWord input {ctx with id := peer} = expectedWord mode input ctx := by
  rw [input_word_is_linear_mod_u32]
  simp only [same_warp_selected_linear hw hl,expectedWord,Nat.add_assoc]

end
end Ptx.Kernels.ShuffleProbe
