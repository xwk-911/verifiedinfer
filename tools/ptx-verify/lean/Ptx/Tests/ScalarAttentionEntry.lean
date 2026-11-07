import Ptx.Kernels.ScalarAttentionThread

/-! Integrated parameterized source tests: non-unit CTA geometry, arbitrary
real inputs, extra parameters, empty inputs and both masks. No GPU claim. -/
namespace Ptx.ScalarAttentionEntryTests
open Ptx.ISA Ptx.Scalar Ptx.ScalarAttention Ptx.ScalarAttentionInit
noncomputable section

def input : Inputs := {
  q := 0, key := 1024, value := 2048, output := 4096, scale := 8192, m := 3, n := 2, dim := 4
  q64 := by decide, key64 := by decide, value64 := by decide, output64 := by decide, scale64 := by decide
  m32 := by decide, n32 := by decide, dim32 := by decide
}
def context (i : Inputs) : Scalar.Context := {
  id := ⟨⟨1,1,0⟩,⟨1,0,0⟩⟩
  block := ⟨2,2,1⟩
  params := [("unrelated",31337),("Q",i.q),("K",i.key),("V",i.value),("O",i.output),
    ("Scale",i.scale),("M",i.m),("N",i.n),("D",i.dim)]
}

theorem parameters (i : Inputs) : Params i (context i).params := by constructor <;> rfl
theorem geometry (i : Inputs) : IndexBounds (context i) := by constructor <;> norm_num [context,row,col]

theorem addresses : AddressBounds input (context input) := by
  constructor
  · decide
  · intro k hk
    change k < 4 at hk
    change 0+4*(2*4)+4*k < 2^64
    omega
  · intro j k hj hk
    change j < 2 at hj
    change k < 4 at hk
    change 1024+4*4*j+4*k < 2^64
    omega
  · intro j hj
    change j < 2 at hj
    change 2048+4*3+4*4*j < 2^64
    omega

theorem nonunit_source (q key value : Attention.Matrix) (scale : ℝ) :
    ∃ final, Scalar.run (context input) (ScalarAttentionOracle.answers q key value 2 3 4 scale) code 159 {} = .ok
      (final,[.read ⟨.global,8192⟩ (Symbolic.encode .f32 scale)] ++
        (ScalarAttentionOuter.suffixReads (threadLayout input (context input) addresses) q key value 2 3 0 2 ++
          [.write ⟨.global,4140⟩ (Symbolic.encode .f32 (Attention.output q key value (Real.log 2*scale) 2 3 2 4))])) ∧
      final.core.thread.status = .done :=
  active_execution input (context input) q key value scale (parameters input) (geometry input)
    (by decide) (by decide) (by decide) addresses

def emptyInput : Inputs := {input with
  q := 2^64-1, key := 2^64-1, value := 2^64-1, scale := 2^64-1, n := 0
  q64 := by decide, key64 := by decide, value64 := by decide, scale64 := by decide, n32 := by decide
}

theorem empty_without_read_bounds (oracle : Scalar.Oracle) :
    ∃ final, Scalar.run (context emptyInput) oracle code 32 {} =
      .ok (final,[.write ⟨.global,4140⟩ (Symbolic.encode .f32 0)]) ∧
      final.core.thread.status = .done ∧ final.core.queries = 0 :=
  empty_execution emptyInput (context emptyInput) oracle (parameters emptyInput) (geometry emptyInput)
    (by decide) (by decide) rfl (by decide)

/-- This fixture cannot satisfy the nonempty read-start bounds. Empty-key
completion therefore cannot rely on assuming unused Q/K/V/scale words readable. -/
theorem empty_read_bounds_false : ¬ AddressBounds emptyInput (context emptyInput) := by
  intro h
  have hq := h.qRead64 0 (by decide)
  norm_num [emptyInput,input,context,row] at hq

theorem every_complete_empty_trace (oracle : Scalar.Oracle) {n final events}
    (h : Scalar.run (context emptyInput) oracle code n {} = .ok (final,events))
    (hd : final.core.thread.status = .done) : n = 32 ∧
      events = [.write ⟨.global,4140⟩ (Symbolic.encode .f32 0)] :=
  empty_completed_shape emptyInput (context emptyInput) oracle (parameters emptyInput) (geometry emptyInput)
    (by decide) (by decide) rfl (by decide) h hd

def rowMasked : Inputs := {input with m := 2,m32 := by decide}
def colMasked : Inputs := {input with dim := 3,dim32 := by decide}

theorem row_mask_source (oracle : Scalar.Oracle) :
    ∃ final, Scalar.run (context rowMasked) oracle code 21 {} = .ok (final,[]) ∧
      final.core.thread.status = .done ∧ final.core.queries = 0 :=
  masked_row rowMasked (context rowMasked) oracle (parameters rowMasked) (geometry rowMasked) (by decide)

theorem col_mask_source (oracle : Scalar.Oracle) :
    ∃ final, Scalar.run (context colMasked) oracle code 23 {} = .ok (final,[]) ∧
      final.core.thread.status = .done ∧ final.core.queries = 0 :=
  masked_col colMasked (context colMasked) oracle (parameters colMasked) (geometry colMasked) (by decide) (by decide)

def overflowContext : Scalar.Context := {(context input) with id := ⟨⟨2^31,1,0⟩,⟨1,0,0⟩⟩}
theorem index_overflow_rejected : ¬ IndexBounds overflowContext := by
  intro h
  have hc := h.colBound
  norm_num [overflowContext,context,col] at hc

end
end Ptx.ScalarAttentionEntryTests
