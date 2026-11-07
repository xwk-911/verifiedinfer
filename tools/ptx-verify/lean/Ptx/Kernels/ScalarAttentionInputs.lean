import Ptx.Kernels.ScalarAttentionMemory

/-! Actual event reads force initialized input values in every complete memory-
consistent source candidate. No correct-input oracle is a precondition. -/
namespace Ptx.ScalarAttentionEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.ScalarAttention Ptx.ScalarAttentionInit
noncomputable section

theorem active_item_read {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) (hn : 0 < cfg.input.n)
    {j slot : Nat} (hj : j < cfg.input.n) (hs : slot < 2*cfg.input.dim+1) :
    execution.eventAt ⟨t.id,1+(2*cfg.input.dim+1)*j+slot⟩ =
      (ScalarAttentionReads.itemReads (layout cfg launch.params t.id ha hn)
        (ScalarAttentionTrace.qValues (layout cfg launch.params t.id ha hn) t.oracle)
        (ScalarAttentionTrace.keyValues (layout cfg launch.params t.id ha hn) t.oracle)
        (ScalarAttentionTrace.values (layout cfg launch.params t.id ha hn) t.oracle) j hj)[slot]? := by
  have hmul := Nat.mul_le_mul_left (2*cfg.input.dim+1) (by omega : j+1 ≤ cfg.input.n)
  simp only [Nat.mul_succ] at hmul
  have hindex : 1+(2*cfg.input.dim+1)*j+slot < writeSerial cfg := by
    simp only [writeSerial,ite_eq_right hn.ne']
    omega
  rw [eventAt_of_trace hw.2.1 ht rfl,active_trace hw hd hg hp ht ha]
  dsimp only
  unfold eventsFor
  rw [List.getElem?_append_left (by simpa only [readEventsFor_length] using hindex)]
  rw [readEventsFor,dite_eq_left hn]
  simp only [List.cons_append,List.nil_append]
  rw [show 1+(2*cfg.input.dim+1)*j+slot = ((2*cfg.input.dim+1)*j+slot)+1 by omega,List.getElem?_cons_succ]
  simpa only [layout,threadLayout,Nat.zero_add] using
    ScalarAttentionReads.reads_at (l := layout cfg launch.params t.id ha hn)
      (start := 0) (count := cfg.input.n) (j := j) (serial := slot) (by simp [layout,threadLayout]) hj hs

theorem active_read_scale {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) (hn : 0 < cfg.input.n) :
    execution.eventAt ⟨t.id,0⟩ = some (.read (scaleLoc cfg) (Symbolic.encode .f32 (replyReal t.oracle 0))) := by
  rw [eventAt_of_trace hw.2.1 ht rfl,active_trace hw hd hg hp ht ha]
  simp [eventsFor,readEventsFor,hn]

theorem active_read_q {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) (hn : 0 < cfg.input.n)
    {j k : Nat} (hj : j < cfg.input.n) (hk : k < cfg.input.dim) :
    execution.eventAt ⟨t.id,1+(2*cfg.input.dim+1)*j+2*k⟩ = some
      (.read (qLoc cfg (row cfg.geometry.block t.id) k)
        (Symbolic.encode .f32 (ScalarAttentionTrace.qValues (layout cfg launch.params t.id ha hn) t.oracle j k))) := by
  rw [active_item_read hw hd hg hp ht ha hn hj (by omega),ScalarAttentionReads.item_q hj hk,layout_q cfg launch.params ha hn k]

theorem active_read_key {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) (hn : 0 < cfg.input.n)
    {j k : Nat} (hj : j < cfg.input.n) (hk : k < cfg.input.dim) :
    execution.eventAt ⟨t.id,1+(2*cfg.input.dim+1)*j+(2*k+1)⟩ = some
      (.read (keyLoc cfg j k)
        (Symbolic.encode .f32 (ScalarAttentionTrace.keyValues (layout cfg launch.params t.id ha hn) t.oracle j k))) := by
  rw [active_item_read hw hd hg hp ht ha hn hj (by omega),ScalarAttentionReads.item_key hj hk,layout_key cfg launch.params ha hn j k]

theorem active_read_value {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) (hn : 0 < cfg.input.n)
    {j : Nat} (hj : j < cfg.input.n) :
    execution.eventAt ⟨t.id,1+(2*cfg.input.dim+1)*j+2*cfg.input.dim⟩ = some
      (.read (valueLoc cfg j (col cfg.geometry.block t.id))
        (Symbolic.encode .f32 (ScalarAttentionTrace.values (layout cfg launch.params t.id ha hn) t.oracle j))) := by
  rw [active_item_read hw hd hg hp ht ha hn hj (by omega)]
  have hv := ScalarAttentionReads.item_value (l := layout cfg launch.params t.id ha hn)
      (q := ScalarAttentionTrace.qValues (layout cfg launch.params t.id ha hn) t.oracle)
      (key := ScalarAttentionTrace.keyValues (layout cfg launch.params t.id ha hn) t.oracle)
      (value := ScalarAttentionTrace.values (layout cfg launch.params t.id ha hn) t.oracle) hj
  rw [layout_value cfg launch.params ha hn j] at hv
  exact hv

theorem active_write {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) :
    execution.eventAt ⟨t.id,writeSerial cfg⟩ = some
      (.write (outputLoc cfg (row cfg.geometry.block t.id) (col cfg.geometry.block t.id))
        (Symbolic.encode .f32 (answer cfg launch.params t.id t.oracle ha))) := by
  rw [eventAt_of_trace hw.2.1 ht rfl,active_trace hw hd hg hp ht ha]
  dsimp only
  unfold eventsFor
  rw [List.getElem?_append_right (by simp)]
  simp only [readEventsFor_length,Nat.sub_self,List.getElem?_cons_zero]

theorem scale_read_value {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    {rf : ReadsFrom} {co : Coherence} {q key value : Attention.Matrix} {scale : ℝ}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg q key value scale launch.initial) (hc : GenericMemoryConditions execution launch.initial rf co)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) (hn : 0 < cfg.input.n) : replyReal t.oracle 0 = scale := by
  have hen := reads_enabled ha hn
  apply immutable_real_load hc.agreement (active_read_scale hw hd hg hp ht ha hn)
  · exact race_free_eligible (no_races hw hd hg hp rf) _ _
  · exact input_unwritten hw hd hg hp ⟨hen,.inl (by simpa only [scaleLoc,Nat.mul_zero,Nat.add_zero] using
      (word_base_in_region (base := cfg.input.scale) (count := 1) (index := 0) (by decide)))⟩
  · exact (hi hen).1

theorem q_read_value {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    {rf : ReadsFrom} {co : Coherence} {q key value : Attention.Matrix} {scale : ℝ}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg q key value scale launch.initial) (hc : GenericMemoryConditions execution launch.initial rf co)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) (hn : 0 < cfg.input.n)
    {j k : Nat} (hj : j < cfg.input.n) (hk : k < cfg.input.dim) :
    ScalarAttentionTrace.qValues (layout cfg launch.params t.id ha hn) t.oracle j k = q (row cfg.geometry.block t.id) k := by
  have hen := reads_enabled ha hn
  apply immutable_real_load hc.agreement (active_read_q hw hd hg hp ht ha hn hj hk)
  · exact race_free_eligible (no_races hw hd hg hp rf) _ _
  · exact input_unwritten hw hd hg hp ⟨hen,.inr (.inl (word_base_in_region (q_index_bound cfg ha.1 hk)))⟩
  · exact (hi hen).2.1 _ _ ha.1 hk

theorem key_read_value {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    {rf : ReadsFrom} {co : Coherence} {q key value : Attention.Matrix} {scale : ℝ}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg q key value scale launch.initial) (hc : GenericMemoryConditions execution launch.initial rf co)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) (hn : 0 < cfg.input.n)
    {j k : Nat} (hj : j < cfg.input.n) (hk : k < cfg.input.dim) :
    ScalarAttentionTrace.keyValues (layout cfg launch.params t.id ha hn) t.oracle j k = key j k := by
  have hen := reads_enabled ha hn
  apply immutable_real_load hc.agreement (active_read_key hw hd hg hp ht ha hn hj hk)
  · exact race_free_eligible (no_races hw hd hg hp rf) _ _
  · exact input_unwritten hw hd hg hp ⟨hen,.inr (.inr (.inl (word_base_in_region (key_index_bound cfg hj hk))))⟩
  · exact (hi hen).2.2.1 _ _ hj hk

theorem value_read_value {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    {rf : ReadsFrom} {co : Coherence} {q key value : Attention.Matrix} {scale : ℝ}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg q key value scale launch.initial) (hc : GenericMemoryConditions execution launch.initial rf co)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) (hn : 0 < cfg.input.n)
    {j : Nat} (hj : j < cfg.input.n) :
    ScalarAttentionTrace.values (layout cfg launch.params t.id ha hn) t.oracle j = value j (col cfg.geometry.block t.id) := by
  have hen := reads_enabled ha hn
  apply immutable_real_load hc.agreement (active_read_value hw hd hg hp ht ha hn hj)
  · exact race_free_eligible (no_races hw hd hg hp rf) _ _
  · exact input_unwritten hw hd hg hp ⟨hen,.inr (.inr (.inr (word_base_in_region (key_index_bound cfg hj ha.2))))⟩
  · exact (hi hen).2.2.2 _ _ hj ha.2

theorem answer_correct {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    {rf : ReadsFrom} {co : Coherence} {q key value : Attention.Matrix} {scale : ℝ}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg q key value scale launch.initial) (hc : GenericMemoryConditions execution launch.initial rf co)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) :
    answer cfg launch.params t.id t.oracle ha = Attention.output q key value (Real.log 2*scale)
      (row cfg.geometry.block t.id) (col cfg.geometry.block t.id) cfg.input.n cfg.input.dim := by
  by_cases hn : 0 < cfg.input.n
  · rw [answer,dite_eq_left hn,← OnlineSoftmax.attention_bridge]
    apply OnlineSoftmax.average_congr
    · intro j hj
      simp only [ScalarAttentionTrace.scores,ScalarAttentionReads.score,
        scale_read_value hw hd hg hp hi hc ht ha hn]
      congr 1
      exact Attention.dot_congr (fun k hk => q_read_value hw hd hg hp hi hc ht ha hn hj hk)
        (fun k hk => key_read_value hw hd hg hp hi hc ht ha hn hj hk)
    · intro j hj
      exact value_read_value hw hd hg hp hi hc ht ha hn hj
  · have hz : cfg.input.n = 0 := by omega
    simp [answer,hz]

end
end Ptx.ScalarAttentionEvent
