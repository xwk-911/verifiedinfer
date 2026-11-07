import Ptx.Hopper.UnifiedSource
import Ptx.Hopper.TmaSource

/-! Actual base-event provenance through the extended executor. No new base
event is invented by WGMMA fence/MMA/commit/wait; only a successful delegated
ordinary/TMA instruction can emit Event.base. -/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

theorem base_step_origin {ctx oracle code before after emitted event}
    (hs : Wgmma.step ctx oracle code before = .ok (after,emitted)) (hm : Wgmma.Event.base event ∈ emitted) :
    ∃ next events, Hopper.step ctx oracle.base code before.base = .ok (next,events) ∧
      event ∈ events ∧ after.base = next := by
  simp only [Wgmma.step,Wgmma.liftBase,Wgmma.liftInteger,bind,Except.bind,pure,Except.pure] at hs
  repeat' first | split at hs | cases hs
  all_goals simp_all
  all_goals
    cases hd : Hopper.step ctx oracle.base code before.base with
    | error fault => simp_all
    | ok value =>
      rcases value with ⟨next,events⟩
      simp_all
      exact ⟨_,rfl,hm⟩

theorem source_base_event {candidate : Candidate} {code launch id event}
    (hw : WellFormed code launch candidate) (he : candidate.eventAt id = some (.base event)) :
    ∃ located, candidate.componentSourceAt code launch.params launch.geometry.block id = some located ∧ located.kind = event ∧
      ∃ oracle before after emitted,
        Hopper.step {id := id.thread,params := launch.params,block := launch.geometry.block} oracle code before = .ok (after,emitted) ∧
        event ∈ emitted ∧ located.pc = before.scalar.core.thread.pc := by
  obtain ⟨located,hsource,hkind,oracle,before,after,emitted,hs,hm,hpc⟩ := source_event hw he
  obtain ⟨next,baseEvents,hdelegate,hmem,hnext⟩ := base_step_origin hs hm
  refine ⟨locatedView located,?_,?_,oracle.base,before.base,next,baseEvents,hdelegate,hmem,hpc⟩
  · simp only [Candidate.componentSourceAt,hsource,Option.map_some]
  · simp only [locatedView,hkind,eventView]

theorem tma_copy_has_source {candidate : Candidate} {code launch id copy}
    (hw : WellFormed code launch candidate) (he : Tma.copyAt candidate.view id = some copy) :
    ∃ located, candidate.componentSourceAt code launch.params launch.geometry.block id.issue = some located ∧ located.kind = .tmaIssue copy ∧
      ∃ oracle before after emitted,
        Hopper.step {id := id.issue.thread,params := launch.params,block := launch.geometry.block} oracle code before = .ok (after,emitted) ∧
        Hopper.Event.tmaIssue copy ∈ emitted ∧ located.pc = before.scalar.core.thread.pc :=
  source_base_event hw (view_tma_iff.mp (Tma.copyAt_iff.mp he))
theorem tma_copy_payload_length {candidate : Candidate} {code launch id copy}
    (hw : WellFormed code launch candidate) (he : Tma.copyAt candidate.view id = some copy) :
    copy.payload.length = copy.descriptor.bytes := by
  obtain ⟨_,_,_,oracle,before,after,events,hs,hm,_⟩ := tma_copy_has_source hw he
  exact (Hopper.step_tma_shape hs hm).1
theorem tma_copy_actual_query {candidate : Candidate} {code launch id copy}
    (hw : WellFormed code launch candidate) (he : Tma.copyAt candidate.view id = some copy) :
    ∃ oracle before after events,
      Hopper.step {id := id.issue.thread,params := launch.params,block := launch.geometry.block} oracle code before = .ok (after,events) ∧
      Hopper.Event.tmaIssue copy ∈ events ∧ copy.queryBase = before.scalar.core.queries ∧
      copy.payload = oracle.tmaBytes (before.scalar.core.queries+1) ∧ after.scalar.core.queries = before.scalar.core.queries+2 := by
  obtain ⟨_,_,_,oracle,before,after,events,hs,hm,_⟩ := tma_copy_has_source hw he
  have hh := Hopper.step_tma_shape hs hm
  exact ⟨oracle,before,after,events,hs,hm,hh.2.1,hh.2.2.2.1,hh.2.2.2.2⟩

end
end Ptx.Hopper.Unified
