import Ptx.Kernels.MoeCombineMemory

/-! Initial R agreement fixes expert selection before selected H input
representation is used. No unselected H value is required. -/
namespace Ptx.MoeCombineEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeCombine
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
    {rf : ReadsFrom} {co : Coherence} {gates values : Moe.Matrix}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg gates values launch.initial) (hc : GenericMemoryConditions execution launch.initial rf co)
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
    {rf : ReadsFrom} {co : Coherence} {gates values : Moe.Matrix}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg gates values launch.initial) (hc : GenericMemoryConditions execution launch.initial rf co)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) : expert t.oracle < 2 := by
  rw [expert_correct hw hd hg hp hi hc ht ha]
  exact Moe.selected_bound _ _

theorem active_read {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) (he : expert t.oracle < 2) :
    execution.eventAt ⟨t.id,1⟩ = some (.read (hLoc cfg (expert t.oracle) (row cfg.geometry.block t.id) (col cfg.geometry.block t.id))
      (Symbolic.encode .f32 (answer t.oracle))) := by
  rw [eventAt_of_trace hw.2.1 ht rfl,active_trace hw hd hg hp ht ha he]
  rfl

theorem active_write {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) (he : expert t.oracle < 2) :
    execution.eventAt ⟨t.id,2⟩ = some (.write (yLoc cfg (row cfg.geometry.block t.id) (col cfg.geometry.block t.id))
      (Symbolic.encode .f32 (answer t.oracle))) := by
  rw [eventAt_of_trace hw.2.1 ht rfl,active_trace hw hd hg hp ht ha he]
  rfl

theorem answer_correct {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    {rf : ReadsFrom} {co : Coherence} {gates values : Moe.Matrix}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg gates values launch.initial) (hc : GenericMemoryConditions execution launch.initial rf co)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) :
    answer t.oracle = values (row cfg.geometry.block t.id) (col cfg.geometry.block t.id) := by
  have he := expert_valid hw hd hg hp hi hc ht ha
  have hread := active_read hw hd hg hp ht ha he
  rw [expert_correct hw hd hg hp hi hc ht ha] at hread
  apply immutable_real_load hc.agreement hread
  · exact race_free_eligible (no_races hw hd hg hp rf) _ _
  · exact input_unwritten hw hd hg hp (.inr (word_base_in_region (h_index_bound cfg (Moe.selected_bound _ _) ha.1 ha.2)))
  · exact hi.2 _ _ ha.1 ha.2

end
end Ptx.MoeCombineEvent
