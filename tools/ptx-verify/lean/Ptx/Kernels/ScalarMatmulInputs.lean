import Ptx.Kernels.ScalarMatmulMemory

/-! Arbitrary-candidate oracle answers are derived from actual represented input
memory. No initial-value oracle is prescribed by the kernel's precondition.
-/
namespace Ptx.ScalarMatmulEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.ScalarMatmul Ptx.ScalarMatmulLoop
noncomputable section

theorem active_read_a {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) {k : Nat} (hk : k < cfg.input.k) :
    execution.eventAt ⟨t.id,2*k⟩ = some
      (.read (aLoc cfg (row cfg.geometry.block t.id) k) (Symbolic.encode .f32 (realReply t.oracle (2*k)))) := by
  rw [eventAt_of_trace hw.2.1 ht rfl,active_trace hw hd hg hp ht ha]
  dsimp only
  unfold eventsFor
  rw [List.getElem?_append_left (by rw [loopReads_length]; omega),loopReads_a hk]
  simp only [Nat.zero_add,replyA,layout_a cfg launch.params ha k]

theorem active_read_b {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) {k : Nat} (hk : k < cfg.input.k) :
    execution.eventAt ⟨t.id,2*k+1⟩ = some
      (.read (bLoc cfg k (col cfg.geometry.block t.id)) (Symbolic.encode .f32 (realReply t.oracle (2*k+1)))) := by
  rw [eventAt_of_trace hw.2.1 ht rfl,active_trace hw hd hg hp ht ha]
  dsimp only
  unfold eventsFor
  rw [List.getElem?_append_left (by rw [loopReads_length]; omega),loopReads_b hk]
  simp only [Nat.zero_add,replyB,layout_b cfg launch.params ha k]

theorem active_write {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) :
    execution.eventAt ⟨t.id,2*cfg.input.k⟩ = some
      (.write (cLoc cfg (row cfg.geometry.block t.id) (col cfg.geometry.block t.id)) (Symbolic.encode .f32 (answer cfg t.oracle))) := by
  rw [eventAt_of_trace hw.2.1 ht rfl,active_trace hw hd hg hp ht ha]
  dsimp only
  unfold eventsFor
  rw [List.getElem?_append_right (by simp)]
  simp only [loopReads_length,Nat.sub_self,List.getElem?_cons_zero]

theorem a_read_value {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    {rf : ReadsFrom} {co : Coherence} {a b : Matrix}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg a b launch.initial) (hc : GenericMemoryConditions execution launch.initial rf co)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) {k : Nat} (hk : k < cfg.input.k) :
    realReply t.oracle (2*k) = a (row cfg.geometry.block t.id) k := by
  apply immutable_real_load hc.agreement (active_read_a hw hd hg hp ht ha hk)
  · exact race_free_eligible (no_races hw hd hg hp rf) _ _
  · exact input_unwritten hw hd hg hp (.inl (word_base_in_region (a_index_bound cfg ha.1 hk)))
  · exact hi.1 _ _ ha.1 hk

theorem b_read_value {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    {rf : ReadsFrom} {co : Coherence} {a b : Matrix}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg a b launch.initial) (hc : GenericMemoryConditions execution launch.initial rf co)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) {k : Nat} (hk : k < cfg.input.k) :
    realReply t.oracle (2*k+1) = b k (col cfg.geometry.block t.id) := by
  apply immutable_real_load hc.agreement (active_read_b hw hd hg hp ht ha hk)
  · exact race_free_eligible (no_races hw hd hg hp rf) _ _
  · exact input_unwritten hw hd hg hp (.inr (word_base_in_region (b_index_bound cfg hk ha.2)))
  · exact hi.2 _ _ hk ha.2

theorem answer_correct {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    {rf : ReadsFrom} {co : Coherence} {a b : Matrix}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg a b launch.initial) (hc : GenericMemoryConditions execution launch.initial rf co)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) :
    answer cfg t.oracle = prefixProduct a b (row cfg.geometry.block t.id) (col cfg.geometry.block t.id) cfg.input.k := by
  have hprefix : ∀ count, count ≤ cfg.input.k → prefixProduct (replyA t.oracle) (replyB t.oracle) 0 0 count =
      prefixProduct a b (row cfg.geometry.block t.id) (col cfg.geometry.block t.id) count := by
    intro count
    induction count with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      have hk : n < cfg.input.k := by omega
      simp only [prefixProduct,replyA,replyB,a_read_value hw hd hg hp hi hc ht ha hk,
        b_read_value hw hd hg hp hi hc ht ha hk,ih (by omega)]
  exact hprefix cfg.input.k (Nat.le_refl _)

end
end Ptx.ScalarMatmulEvent
