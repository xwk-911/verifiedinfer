import Ptx.Kernels.ScalarAttentionSourceTrace
import Ptx.Tests.ScalarAttentionOuter

/-! Positive arbitrary-reply reconstruction and late wrong-type regressions.
Repeated Q reads may differ locally; this example is not asserted globally
consistent and demonstrates why memory correspondence remains necessary. -/
namespace Ptx.ScalarAttentionTraceTests
open Ptx.ISA Ptx.Scalar Ptx.ScalarAttention Ptx.ScalarAttentionInit
noncomputable section
abbrev l := ScalarAttentionOuterTests.layout
abbrev ctx := ScalarAttentionOuterTests.ctx
abbrev ready := ScalarAttentionOuterTests.ready

def input : Inputs := {
  q := 0, key := 64, value := 128, output := 256, scale := 320, m := 1, n := 2, dim := 1
  q64 := by decide, key64 := by decide, value64 := by decide, output64 := by decide, scale64 := by decide
  m32 := by decide, n32 := by decide, dim32 := by decide
}
theorem parameters : Params input ctx.params := by constructor <;> rfl
theorem geometry : IndexBounds ctx := by constructor <;> decide
theorem addresses : AddressBounds input ctx := by
  constructor
  · decide
  · intro k hk; change k < 1 at hk; change 0+4*(0*1)+4*k < 2^64; omega
  · intro j k hj hk
    change j < 2 at hj; change k < 1 at hk
    change 64+4*1*j+4*k < 2^64
    omega
  · intro j hj; change j < 2 at hj; change 128+4*0+4*1*j < 2^64; omega

def qReads : Attention.Matrix := fun item _ => if item = 0 then 0 else 1
def keys : Attention.Matrix := fun _ _ => 1
def vals : Nat → ℝ := fun item => if item = 0 then 4 else 10
def oracle : Scalar.Oracle := fun query => .real .f32
  (if query = 1 then 0 else if query = 3 then 4 else if query = 6 then 10 else 1)

theorem ready_inv : ScalarAttentionOuter.Inv l (ScalarAttentionReads.score l qReads keys 1) vals 1 0 ready := by
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro h; exact (h rfl).elim
  · exact ScalarAttentionOuterTests.ready_inv.banks

theorem q_replies : ∀ j k, j < l.keys → k < l.dim →
    oracle (ScalarAttentionOuter.queryIndex l j+2*k) = .real .f32 (qReads j k) := by
  intro j k hj hk
  have he : k = 0 := by change k < 1 at hk; omega
  subst k
  have he : j = 0 ∨ j = 1 := by change j < 2 at hj; omega
  rcases he with rfl | rfl <;> rfl
theorem key_replies : ∀ j k, j < l.keys → k < l.dim →
    oracle (ScalarAttentionOuter.queryIndex l j+2*k+1) = .real .f32 (keys j k) := by
  intro j k hj hk
  have he : k = 0 := by change k < 1 at hk; omega
  subst k
  have he : j = 0 ∨ j = 1 := by change j < 2 at hj; omega
  rcases he with rfl | rfl <;> rfl
theorem value_replies : ∀ j, j < l.keys → oracle (ScalarAttentionOuter.queryIndex l j+2*l.dim) = .real .f32 (vals j) := by
  intro j hj
  have he : j = 0 ∨ j = 1 := by change j < 2 at hj; omega
  rcases he with rfl | rfl <;> rfl

theorem reply_average : OnlineSoftmax.average (ScalarAttentionReads.score l qReads keys 1) vals l.keys = 8 := by
  norm_num [OnlineSoftmax.average,OnlineSoftmax.numerator,OnlineSoftmax.denominator,ScalarAttentionReads.score,
    Attention.dot,ScalarAttentionOuterTests.layout,qReads,keys,vals,Finset.sum_range_succ,
    RealMath.exp2,Real.exp_log (by norm_num : (0 : ℝ) < 2)]

def inputEvents : List Scalar.Kind := [
  .read ⟨.global,320⟩ (Symbolic.encode .f32 1),
  .read ⟨.global,0⟩ (Symbolic.encode .f32 0),.read ⟨.global,64⟩ (Symbolic.encode .f32 1),
  .read ⟨.global,128⟩ (Symbolic.encode .f32 4),
  .read ⟨.global,0⟩ (Symbolic.encode .f32 1),.read ⟨.global,68⟩ (Symbolic.encode .f32 1),
  .read ⟨.global,132⟩ (Symbolic.encode .f32 10)]

theorem nonuniform_q_locally_completes : ∃ final, Scalar.run ctx oracle code 105 {} =
    .ok (final,inputEvents ++ [.write ⟨.global,256⟩ (Symbolic.encode .f32 8)]) ∧
    final.core.thread.status = .done := by
  have hprefix : Scalar.run ctx oracle code 37 {} = .ok
      (ready,[.read ⟨.global,320⟩ (Symbolic.encode .f32 1)]) := rfl
  obtain ⟨final,hr,hf⟩ := ScalarAttentionReads.complete_from_entry l ctx oracle qReads keys vals 1 (by decide)
    q_replies key_replies value_replies ready_inv
  rw [reply_average] at hr
  have ht : Scalar.run ctx oracle code 68 ready = .ok
      (final,inputEvents.drop 1 ++ [.write ⟨.global,256⟩ (Symbolic.encode .f32 8)]) := by
    simpa [ScalarAttentionReads.reads,ScalarAttentionReads.itemReads,ScalarAttentionOuter.iterationReads,
      ScalarAttentionDot.loopReads,ScalarAttentionDot.reads,ScalarAttentionOuter.dotLayout,
      ScalarAttentionOuterTests.layout,qReads,keys,vals,inputEvents] using hr
  refine ⟨final,?_,hf⟩
  rw [show 105 = 37+68 by decide,Scalar.run_add,hprefix]
  simp [Except.bind,ht,inputEvents]

theorem reconstructed_q_differs : ScalarAttentionTrace.qValues l oracle 0 0 = 0 ∧
    ScalarAttentionTrace.qValues l oracle 1 0 = 1 := ⟨rfl,rfl⟩

theorem uniform_input_spec_differs : Attention.output (fun _ _ => 1) keys (fun item _ => vals item)
    (Real.log 2) 0 0 2 1 = 7 := by
  norm_num [Attention.output,Attention.numerator,Attention.denominator,Attention.score,Attention.dot,keys,vals,
    Finset.sum_range_succ,Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem every_completed_source (answers : Scalar.Oracle) {n final events}
    (hr : Scalar.run ctx answers code n {} = .ok (final,events)) (hd : final.core.thread.status = .done) :
    ∃ scale, answers 0 = .real .f32 scale ∧ n = 105 ∧
      events = [.read ⟨.global,320⟩ (Symbolic.encode .f32 scale)] ++
        (ScalarAttentionReads.reads (threadLayout input ctx addresses)
          (ScalarAttentionTrace.qValues (threadLayout input ctx addresses) answers)
          (ScalarAttentionTrace.keyValues (threadLayout input ctx addresses) answers)
          (ScalarAttentionTrace.values (threadLayout input ctx addresses) answers) 0 2 ++
        [.write ⟨.global,256⟩ (Symbolic.encode .f32
          (OnlineSoftmax.average (ScalarAttentionTrace.scores (threadLayout input ctx addresses) answers scale)
            (ScalarAttentionTrace.values (threadLayout input ctx addresses) answers) 2))]) :=
  active_completed_shape input ctx answers parameters geometry (by decide) (by decide) (by decide) addresses hr hd

theorem wrong_scale_not_complete (answers : Scalar.Oracle) (hq : answers 0 = .integer 17)
    {n final events} (hr : Scalar.run ctx answers code n {} = .ok (final,events)) : final.core.thread.status ≠ .done := by
  intro hd
  obtain ⟨scale,hs⟩ := completed_scale_reply input ctx answers parameters geometry
    (by decide) (by decide) (by decide) (by decide) hr hd
  rw [hq] at hs; cases hs

theorem wrong_late_value_format_not_complete (answers : Scalar.Oracle) (hq : answers 6 = .real .f64 999)
    {n final events} (hr : Scalar.run ctx answers code n {} = .ok (final,events)) : final.core.thread.status ≠ .done := by
  intro hd
  obtain ⟨scale,_,hqueries⟩ := active_completed_replies input ctx answers parameters geometry
    (by decide) (by decide) (by decide) addresses hr hd
  have hv : answers 6 = .real .f32 (ScalarAttentionTrace.values (threadLayout input ctx addresses) answers 1) :=
    (hqueries 1 (by decide)).2
  rw [hq] at hv; cases hv

end
end Ptx.ScalarAttentionTraceTests
