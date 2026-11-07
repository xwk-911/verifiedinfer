import Ptx.Kernels.ScalarAttentionDot

/-! Local actual-source loop regressions. Addresses and oracle offsets are
explicit; none of these tests asserts launch-wide memory consistency. -/
namespace Ptx.ScalarAttentionDotTests
open Ptx.ISA Ptx.Scalar Ptx.ScalarAttentionDot
noncomputable section

def base (l : Layout) : Scalar.State := {
  core := {queries := l.firstQuery,thread := {pc := 38,regs := [
    ("%qp",wrap 64 l.qBase),("%kp",wrap 64 l.keyBase),("%k",0),("%d",l.count),
    ("%j",5),("%op",256),("%extra",123)]}}
}
def initial (l : Layout) (scale maximum normalizer accumulator : ℝ) : Scalar.State :=
  writeFloat (writeFloat (writeFloat (writeFloat (writeFloat (base l)
    "%score" .f32 0) "%scale" .f32 scale) "%max" .f32 maximum)
    "%l" .f32 normalizer) "%u" .f32 accumulator

theorem initial_banks (l : Layout) (scale maximum normalizer accumulator : ℝ) :
    BanksDisjoint (initial l scale maximum normalizer accumulator) := by
  unfold initial
  repeat' apply write_float_disjoint
  intro name; right; rfl

theorem initial_inv (l : Layout) (scale maximum normalizer accumulator : ℝ) :
    Inv l 0 0 (initial l scale maximum normalizer accumulator) := by
  constructor
  · rfl
  · rfl
  · simp [initial,base,writeFloat]
  · simp [initial,base,lookup]
  · simp [initial,base,lookup]
  · simp [initial,base,lookup]
  · simp [initial,base,lookup]
  · simp [initial,base]
  · exact initial_banks _ _ _ _ _

def boundary : Layout := {
  count := 1, qBase := 2^64-4, keyBase := 64, firstQuery := 7
  count32 := by decide
  qRead64 := by
    intro k hk
    have : k = 0 := by omega
    subst k
    norm_num
  keyRead64 := by
    intro k hk
    have : k = 0 := by omega
    subst k
    norm_num
}
def answers (a b : ℝ) : Scalar.Oracle := fun query => .real .f32 (if query = 7 then a else b)

/-- Read at the final aligned u64 word, then wrap ONLY the unused one-past
pointer. The initial query is 7, and arbitrary outer-loop float state survives. -/
theorem boundary_and_frame (ctx : Scalar.Context) (a b scale maximum normalizer accumulator : ℝ) :
    ∃ final, Scalar.run ctx (answers a b) code 11 (initial boundary scale maximum normalizer accumulator) =
      .ok (final,[.read ⟨.global,2^64-4⟩ (Symbolic.encode .f32 a),
        .read ⟨.global,64⟩ (Symbolic.encode .f32 b)]) ∧
      final.core.thread.pc = 52 ∧ final.core.queries = 9 ∧
      lookup "%qp" final.core.thread.regs = some 0 ∧ lookup "%kp" final.core.thread.regs = some 68 ∧
      declarationLookup "%score" final.floats = some (.f32,a*b) ∧
      declarationLookup "%scale" final.floats = some (.f32,scale) ∧
      declarationLookup "%max" final.floats = some (.f32,maximum) ∧
      declarationLookup "%l" final.floats = some (.f32,normalizer) ∧
      declarationLookup "%u" final.floats = some (.f32,accumulator) ∧
      lookup "%j" final.core.thread.regs = some 5 ∧ lookup "%extra" final.core.thread.regs = some 123 := by
  have ha : ∀ k, k < boundary.count → answers a b (boundary.firstQuery+2*k) = .real .f32 a := by
    intro k hk; have : k = 0 := by change k < 1 at hk; omega
    subst k; rfl
  have hb : ∀ k, k < boundary.count → answers a b (boundary.firstQuery+2*k+1) = .real .f32 b := by
    intro k hk; have : k = 0 := by change k < 1 at hk; omega
    subst k; rfl
  obtain ⟨final,hr,hf,hframe⟩ := complete_from_entry boundary ctx (answers a b)
    (fun _ => a) (fun _ => b) ha hb (initial_inv boundary scale maximum normalizer accumulator)
  refine ⟨final,?_,hf.pc,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [loopReads,reads,boundary] using hr
  · exact hf.queries
  · simpa [boundary,wrap] using hf.qPointer
  · simpa [boundary,wrap] using hf.keyPointer
  · simpa [dotPrefix,boundary] using hf.accumulator
  · simpa [initial] using (hframe "%scale" (by decide)).2
  · simpa [initial] using (hframe "%max" (by decide)).2
  · simpa [initial] using (hframe "%l" (by decide)).2
  · simpa [initial] using (hframe "%u" (by decide)).2
  · simpa [initial,base,lookup] using (hframe "%j" (by decide)).1
  · simpa [initial,base,lookup] using (hframe "%extra" (by decide)).1

def empty : Layout := {
  count := 0, qBase := 2^64-1, keyBase := 2^64-1, firstQuery := 7
  count32 := by decide
  qRead64 := by intro k hk; omega
  keyRead64 := by intro k hk; omega
}

theorem zero_dimension_reads_nothing (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (scale maximum normalizer accumulator : ℝ) :
    ∃ final, Scalar.run ctx oracle code 2 (initial empty scale maximum normalizer accumulator) = .ok (final,[]) ∧
      final.core.thread.pc = 52 ∧ final.core.thread.status = .running ∧ final.core.queries = 7 ∧
      declarationLookup "%score" final.floats = some (.f32,0) := by
  obtain ⟨final,hr,hf,_⟩ := complete_from_entry empty ctx oracle (fun _ => 0) (fun _ => 0)
    (by intro k hk; change k < 0 at hk; omega) (by intro k hk; change k < 0 at hk; omega)
    (initial_inv empty scale maximum normalizer accumulator)
  exact ⟨final,hr,hf.pc,hf.running,hf.queries,hf.accumulator⟩

theorem scaled_boundary_score (ctx : Scalar.Context) (a b scale maximum normalizer accumulator : ℝ) :
    ∃ final, Scalar.run ctx (answers a b) code 12 (initial boundary scale maximum normalizer accumulator) =
      .ok (final,[.read ⟨.global,2^64-4⟩ (Symbolic.encode .f32 a),
        .read ⟨.global,64⟩ (Symbolic.encode .f32 b)]) ∧
      final.core.thread.pc = 53 ∧ final.core.queries = 9 ∧
      declarationLookup "%score" final.floats = some (.f32,scale*(a*b)) := by
  have ha : ∀ k, k < boundary.count → answers a b (boundary.firstQuery+2*k) = .real .f32 a := by
    intro k hk
    have : k = 0 := by change k < 1 at hk; omega
    subst k; rfl
  have hb : ∀ k, k < boundary.count → answers a b (boundary.firstQuery+2*k+1) = .real .f32 b := by
    intro k hk
    have : k = 0 := by change k < 1 at hk; omega
    subst k; rfl
  obtain ⟨final,hr,hf,_⟩ := complete_scaled_score boundary ctx (answers a b)
    (fun _ _ => a) (fun _ _ => b) 3 4 scale ha hb
    (initial_inv boundary scale maximum normalizer accumulator) (by simp [initial])
  refine ⟨final,?_,hf.pc,hf.queries,?_⟩
  · simpa [loopReads,reads,boundary] using hr
  · simpa [Attention.dot,boundary] using hf.scoreValue

end
end Ptx.ScalarAttentionDotTests
