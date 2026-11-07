import Ptx.Kernels.ScalarMatmulThread
import Mathlib.Tactic.NormNum

/-! Arbitrary-K full-source and masking regressions. The input matrices are real
oracle data here; these are not global memory-consistency or GPU executions. -/
namespace Ptx.ScalarMatmulInitTests
open Ptx.ISA Ptx.Scalar Ptx.ScalarMatmul Ptx.ScalarMatmulInit Ptx.ScalarMatmulLoop
noncomputable section

def inputs (k : Nat) (hk : k < 2^32) : Inputs := {
  a := 0, b := 2^39, c := 2^40, m := 3, n := 5, k := k
  a64 := by decide, b64 := by decide, c64 := by decide
  m32 := by decide, n32 := by decide, k32 := hk
}
def ctx (k junk : Nat) : Scalar.Context := {
  id := ⟨⟨1,1,0⟩,.zero⟩
  block := ⟨4,2,1⟩
  params := [("extra",junk),("N",5),("B",2^39),("K",k),("M",3),("C",2^40),("A",0)]
}

theorem params (k junk : Nat) (hk : k < 2^32) : Params (inputs k hk) (ctx k junk).params := by
  constructor <;> rfl

theorem bounds (k junk : Nat) : IndexBounds (ctx k junk) := by
  constructor <;> norm_num [ctx,row,col,Dim3.zero]

theorem addresses (k junk : Nat) (hk : k < 2^32) : AddressBounds (inputs k hk) (ctx k junk) := by
  constructor
  · change 2^40+4*(2*5+4) < 2^64
    decide
  · intro j hj
    change j < k at hj
    change 0+4*(2*k)+4*j < 2^64
    omega
  · intro j hj
    change j < k at hj
    change 2^39+4*4+(4*5)*j < 2^64
    omega

/-- Runtime K, real matrix values and an unrelated parameter are all arbitrary.
This connects initialization and loop proofs on a nontrivial 2-D CTA/thread. -/
theorem arbitrary_k_program (k junk : Nat) (hk : k < 2^32) (a b : Matrix) :
    ∃ final, Scalar.run (ctx k junk) (inputOracle a b 2 4) code (36+9*k) {} =
      .ok (final,loopReads (threadLayout (inputs k hk) (ctx k junk) (addresses k junk hk)) a b 2 4 0 k ++
        [.write ⟨.global,2^40+56⟩ (Symbolic.encode .f32 (prefixProduct a b 2 4 k))]) ∧
      final.core.thread.status = .done ∧ final.core.queries = 2*k := by
  obtain ⟨final,hr,hf⟩ := active_execution (inputs k hk) (ctx k junk) a b (params k junk hk)
    (bounds k junk) (by norm_num [ctx,inputs,row,Dim3.zero]) (by norm_num [ctx,inputs,col,Dim3.zero]) (addresses k junk hk)
  exact ⟨final,hr,hf.done,hf.queries⟩

theorem any_completed_count (k junk : Nat) (hk : k < 2^32) (oracle : Scalar.Oracle)
    {n final events} (hr : Scalar.run (ctx k junk) oracle code n {} = .ok (final,events))
    (hd : final.core.thread.status = .done) : n = 36+9*k := by
  have h := active_completed_shape (inputs k hk) (ctx k junk) oracle (params k junk hk)
    (bounds k junk) (by norm_num [ctx,inputs,row,Dim3.zero]) (by norm_num [ctx,inputs,col,Dim3.zero]) (addresses k junk hk) hr hd
  exact h.1

def rowEdge (k junk : Nat) : Scalar.Context := {ctx k junk with id := ⟨⟨1,1,0⟩,⟨0,1,0⟩⟩}
def colEdge (k junk : Nat) : Scalar.Context := {ctx k junk with id := ⟨⟨1,1,0⟩,⟨1,0,0⟩⟩}

theorem masked_row_edge (k junk : Nat) (hk : k < 2^32) (oracle : Scalar.Oracle) :
    ∃ final, Scalar.run (rowEdge k junk) oracle code 19 {} = .ok (final,[]) ∧
      final.core.thread.status = .done ∧ final.core.queries = 0 := by
  apply masked_row (inputs k hk) (rowEdge k junk) oracle
  · exact params k junk hk
  · constructor <;> norm_num [rowEdge,ctx,row,col,Dim3.zero]
  · norm_num [rowEdge,ctx,inputs,row,Dim3.zero]

theorem masked_col_edge (k junk : Nat) (hk : k < 2^32) (oracle : Scalar.Oracle) :
    ∃ final, Scalar.run (colEdge k junk) oracle code 21 {} = .ok (final,[]) ∧
      final.core.thread.status = .done ∧ final.core.queries = 0 := by
  apply masked_col (inputs k hk) (colEdge k junk) oracle
  · exact params k junk hk
  · constructor <;> norm_num [colEdge,ctx,row,col,Dim3.zero]
  · norm_num [colEdge,ctx,inputs,row,Dim3.zero]
  · norm_num [colEdge,ctx,inputs,col,Dim3.zero]

def overflow : Scalar.Context := {
  id := ⟨⟨4194304,0,0⟩,.zero⟩
  block := ⟨1024,1,1⟩
  params := [("A",0),("B",64),("C",128),("M",1),("N",1),("K",0)]
}

theorem overflowing_column_is_not_safe : ¬ IndexBounds overflow := by
  intro h
  have hc := h.colBound
  norm_num [overflow,col] at hc

/-- Every component fits u32, but the mathematical coordinate 2^32 wraps to
column 0 in the actual source. A proof must retain the coordinate-product bound. -/
theorem actual_column_wrap :
    (Scalar.run overflow (fun _ => .integer 0) code 16 {}).map
      (fun result => lookup "%col" result.1.core.thread.regs) = .ok (some 0) := rfl

end
end Ptx.ScalarMatmulInitTests
