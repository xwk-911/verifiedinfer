import Ptx.Kernels.AmpereTiledAccumulation

/-! All-candidate exact-real tiled matmul correctness under the original Pre,
including inactive outputs and zero K. This does not provide a nonvacuity
witness or prove the physical GPU/runtime/compiler correspondence. -/
namespace Ptx.AmpereTiledCorrect
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledGraph
noncomputable section

theorem inactive_trace {cfg a b launch candidate t} (hp : Pre cfg a b launch)
    (hw : WellFormed code launch candidate) (hc : Complete candidate) (ha : ¬ Active cfg)
    (ht : t ∈ candidate.traces) : t.events = [] := by
  have hv : (context launch t.id).id.Valid (geometry cfg) := by simpa only [context,hp.2.2.1] using (hw.2.2.1 t ht).1
  have hparams : AmpereTiledInit.Params cfg launch.params := by
    rw [hp.2.2.2]
    exact AmpereTiledInit.canonical_params cfg
  obtain ⟨last,hr,hd,_⟩ := AmpereTiledSource.inactive_run hp.1 (context launch t.id) t.oracle hparams hv ha
  exact (Ampere.complete_run_unique (hw.2.2.1 t ht).2 (hc t ht) hr hd).2.2

theorem inactive_events {cfg a b launch candidate} (hp : Pre cfg a b launch)
    (hw : WellFormed code launch candidate) (hc : Complete candidate) (ha : ¬ Active cfg) (event) :
    candidate.eventAt event = none := by
  cases he : candidate.eventAt event with
  | none => rfl
  | some kind =>
    obtain ⟨t,ht,_,hget⟩ := eventAt_trace he
    rw [inactive_trace hp hw hc ha ht] at hget
    simp at hget

theorem inactive_copies {cfg a b launch candidate} (hp : Pre cfg a b launch)
    (hw : WellFormed code launch candidate) (hc : Complete candidate) (ha : ¬ Active cfg) (operation) :
    candidate.copyAt operation = none := by
  cases he : candidate.copyAt operation with
  | none => rfl
  | some op =>
    obtain ⟨serial,hissue⟩ := copy_has_source_issue hw he
    rw [inactive_events hp hw hc ha] at hissue
    cases hissue

theorem inactive_write {cfg a b launch candidate} (hp : Pre cfg a b launch)
    (hw : WellFormed code launch candidate) (hc : Complete candidate) (ha : ¬ Active cfg) (node loc) :
    candidate.writeByte node loc = none := by
  cases node <;> simp [Candidate.writeByte,Candidate.memoryKind,inactive_events hp hw hc ha,inactive_copies hp hw hc ha]

theorem inactive_race_free {cfg a b launch candidate} (hp : Pre cfg a b launch)
    (hw : WellFormed code launch candidate) (hc : Complete candidate) (ha : ¬ Active cfg)
    (rf : Ampere.ReadsFrom) (x y) : ¬ MemoryGraph.DataRace candidate.memoryGraph rf x y := by
  intro race
  rcases race.conflict with ⟨loc,v,hwrite⟩ | ⟨loc,v,hwrite⟩ <;>
    rw [graph_writeByte,inactive_write hp hw hc ha] at hwrite <;> cases hwrite

theorem inactive_post {cfg a b launch candidate rf co o} (hp : Pre cfg a b launch)
    (hw : WellFormed code launch candidate) (ho : ObserverConstraints candidate launch.initial rf co o)
    (hd : o.domain = domain cfg) (ha : ¬ Active cfg) : Post cfg a b launch.initial o.output := by
  constructor
  · intro row col hr hc
    exact (ha ⟨by omega,by omega⟩).elim
  · intro loc hl _
    exact MemoryGraph.observer_unwritten ho (hd ▸ hl)
      (MemoryGraph.race_free_observer_eligible (inactive_race_free hp hw ho.complete ha rf) loc)
      (fun writer => inactive_write hp hw ho.complete ha writer loc)

theorem correct (cfg : Config) (a b : Matrix) : CheckedTriple code (Pre cfg a b) (fun _ => domain cfg)
    (fun launch output => Post cfg a b launch.initial output) := by
  intro launch candidate rf co o hp checked ho hd
  by_cases ha : Active cfg
  · exact AmpereTiledAccumulation.active_post (source_of_pre hp ha checked.provenance ho.complete)
      checked.memory hp.2.1 checked.mma ho hd
  · exact inactive_post hp checked.provenance ho hd ha

end
end Ptx.AmpereTiledCorrect
