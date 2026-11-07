import Ptx.Kernels.MoeExpertsMemory

/-! Actual R, X and W replies identified using shared value agreement. Race
freedom is already derived for arbitrary candidates, including invalid routes. -/
namespace Ptx.MoeExpertsEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeExperts Ptx.MoeExpertsLoop
noncomputable section

theorem active_route_read {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) :
    execution.eventAt ⟨t.id,0⟩ = some (routeKind cfg t.id t.oracle) := by
  have hv : t.id.Valid cfg.geometry := by simpa only [hg] using (hw.2.2.1 t ht).1
  obtain ⟨floats,hrun⟩ := trace_run hw hg ht
  obtain ⟨hprefix,hi⟩ := route_prefix cfg.input (context cfg launch.params t.id) t.oracle (routeValue t.oracle)
    hp (index_bounds cfg hv launch.params) ha.1 ha.2 (route_pointer_bound cfg ha) (active_route_reply hw hd hg hp ht ha)
  obtain ⟨_,_,_,_,he⟩ := complete_after_prefix hrun (hd t ht) hprefix hi.running
  rw [eventAt_of_trace hw.2.1 ht rfl,he]
  rfl

theorem expert_correct {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    {rf : ReadsFrom} {co : Coherence} {gates x : Moe.Matrix} {weights : Moe.Weights}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg gates x weights launch.initial) (hc : GenericMemoryConditions execution launch.initial rf co)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) :
    expert t.oracle = Moe.selected gates (row cfg.geometry.block t.id) := by
  apply immutable_u32_load hc.agreement (active_route_read hw hd hg hp ht ha)
  · intro offset ho
    exact race_free_eligible (no_races hw hd hg hp rf) _ _
  · intro offset ho writer
    apply input_unwritten hw hd hg hp (.inl ?_) writer
    change InWords cfg.input.r cfg.input.m ⟨.global,cfg.input.r+4*row cfg.geometry.block t.id+offset⟩
    exact word_in_region ha.1 (by omega) (by omega)
  · exact hi.1 _ ha.1 (by have := ha.2; omega)
  · exact expert_bound _
  · have h := Moe.selected_bound gates (row cfg.geometry.block t.id); omega

theorem expert_valid {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    {rf : ReadsFrom} {co : Coherence} {gates x : Moe.Matrix} {weights : Moe.Weights}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg gates x weights launch.initial) (hc : GenericMemoryConditions execution launch.initial rf co)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) : expert t.oracle < 2 := by
  rw [expert_correct hw hd hg hp hi hc ht ha]
  exact Moe.selected_bound _ _

theorem active_read_x {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) (he : expert t.oracle < 2) {k : Nat} (hk : k < cfg.input.k) :
    execution.eventAt ⟨t.id,1+2*k⟩ = some (.read (xLoc cfg (row cfg.geometry.block t.id) k)
      (Symbolic.encode .f32 (FmaLoop.realReply t.oracle (1+2*k)))) := by
  rw [eventAt_of_trace hw.2.1 ht rfl,active_trace hw hd hg hp ht ha he]
  simp only [eventsFor,Nat.add_comm 1 (2*k),List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by simp only [FmaLoop.loopReads_length]; omega),
    FmaLoop.loopReads_a hk]
  simp only [Nat.zero_add,FmaLoop.replyA,layout_x cfg launch.params ha he k,Nat.add_comm 1 (2*k)]

theorem active_read_w {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) (he : expert t.oracle < 2) {k : Nat} (hk : k < cfg.input.k) :
    execution.eventAt ⟨t.id,1+(2*k+1)⟩ = some (.read (wLoc cfg (expert t.oracle) k (col cfg.geometry.block t.id))
      (Symbolic.encode .f32 (FmaLoop.realReply t.oracle (1+2*k+1)))) := by
  rw [eventAt_of_trace hw.2.1 ht rfl,active_trace hw hd hg hp ht ha he]
  simp only [eventsFor,Nat.add_comm 1 (2*k+1),List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by simp only [FmaLoop.loopReads_length]; omega),FmaLoop.loopReads_b hk]
  simp only [Nat.zero_add,FmaLoop.replyB,layout_w cfg launch.params ha he k]

theorem active_write {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) (he : expert t.oracle < 2) :
    execution.eventAt ⟨t.id,1+2*cfg.input.k⟩ = some
      (.write (hLoc cfg (expert t.oracle) (row cfg.geometry.block t.id) (col cfg.geometry.block t.id))
        (Symbolic.encode .f32 (answer cfg t.oracle))) := by
  rw [eventAt_of_trace hw.2.1 ht rfl,active_trace hw hd hg hp ht ha he]
  simp only [eventsFor,Nat.add_comm 1 (2*cfg.input.k),List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by simp)]
  simp only [FmaLoop.loopReads_length,Nat.sub_self,List.getElem?_cons_zero]

theorem x_read_value {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    {rf : ReadsFrom} {co : Coherence} {gates x : Moe.Matrix} {weights : Moe.Weights}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg gates x weights launch.initial) (hc : GenericMemoryConditions execution launch.initial rf co)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) {k : Nat} (hk : k < cfg.input.k) :
    FmaLoop.realReply t.oracle (1+2*k) = x (row cfg.geometry.block t.id) k := by
  apply immutable_real_load hc.agreement (active_read_x hw hd hg hp ht ha (expert_valid hw hd hg hp hi hc ht ha) hk)
  · exact race_free_eligible (no_races hw hd hg hp rf) _ _
  · exact input_unwritten hw hd hg hp (.inr (.inl (word_base_in_region (x_index_bound cfg ha.1 hk))))
  · exact hi.2.1 _ _ ha.1 hk (by have := ha.2; omega)

theorem w_read_value {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    {rf : ReadsFrom} {co : Coherence} {gates x : Moe.Matrix} {weights : Moe.Weights}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg gates x weights launch.initial) (hc : GenericMemoryConditions execution launch.initial rf co)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) {k : Nat} (hk : k < cfg.input.k) :
    FmaLoop.realReply t.oracle (1+2*k+1) = weights (Moe.selected gates (row cfg.geometry.block t.id)) k (col cfg.geometry.block t.id) := by
  have he := expert_valid hw hd hg hp hi hc ht ha
  have hvalue : FmaLoop.realReply t.oracle (1+2*k+1) = weights (expert t.oracle) k (col cfg.geometry.block t.id) := by
    apply immutable_real_load hc.agreement (active_read_w hw hd hg hp ht ha he hk)
    · exact race_free_eligible (no_races hw hd hg hp rf) _ _
    · exact input_unwritten hw hd hg hp (.inr (.inr (word_base_in_region (w_index_bound cfg he hk ha.2))))
    · exact hi.2.2 _ _ _ he hk ha.2 (by have := ha.1; omega)
  simpa only [expert_correct hw hd hg hp hi hc ht ha] using hvalue

theorem answer_correct {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    {rf : ReadsFrom} {co : Coherence} {gates x : Moe.Matrix} {weights : Moe.Weights}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg gates x weights launch.initial) (hc : GenericMemoryConditions execution launch.initial rf co)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) :
    answer cfg t.oracle = Moe.output gates x weights (row cfg.geometry.block t.id) (col cfg.geometry.block t.id) cfg.input.k := by
  have hprefix : ∀ count, count ≤ cfg.input.k →
      ScalarMatmul.prefixProduct (FmaLoop.replyA 1 t.oracle) (FmaLoop.replyB 1 t.oracle) 0 0 count =
      Moe.linear x weights (Moe.selected gates (row cfg.geometry.block t.id)) (row cfg.geometry.block t.id) (col cfg.geometry.block t.id) count := by
    intro count
    induction count with
    | zero => intro _; rfl
    | succ k ih =>
      intro hcount
      have hk : k < cfg.input.k := by omega
      simp only [ScalarMatmul.prefixProduct,Moe.linear,FmaLoop.replyA,FmaLoop.replyB,
        x_read_value hw hd hg hp hi hc ht ha hk,w_read_value hw hd hg hp hi hc ht ha hk,ih (by omega)]
  exact hprefix _ (Nat.le_refl _)

end
end Ptx.MoeExpertsEvent
