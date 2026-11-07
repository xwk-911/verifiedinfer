import Ptx.Kernels.AmpereTiledSourceCandidate
import Ptx.MemoryGraph.ObservationWitness

/-! Independent actual inactive-launch witnesses. The source returns through
the real M/N guard, emits no events and observes the unchanged global arena.
Unused inputs need no extra alignment, representation or separation premise. -/
namespace Ptx.AmpereTiledWitnessInactive
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledGraph
noncomputable section

def oracle : Oracle := { scalar := fun _ => .integer 0, bytes := fun _ => [] }
def trace (cfg : Config) (launch : Scalar.Launch) (id : ThreadId) : ThreadTrace :=
  ⟨id,oracle,if cfg.m = 0 then 15 else 17,AmpereTiledInit.maskedFinal cfg (context launch id),[]⟩
def execution (cfg : Config) (launch : Scalar.Launch) : Candidate := ⟨launch.geometry.threads.map (trace cfg launch)⟩
def rf : Ampere.ReadsFrom := fun _ _ => none
def co (cfg : Config) (launch : Scalar.Launch) : Ampere.Coherence := MemoryGraph.InitialCo (execution cfg launch).memoryGraph
def observation (cfg : Config) (launch : Scalar.Launch) : Ampere.Observation :=
  MemoryGraph.selectedObservation (execution cfg launch).memoryGraph launch.initial (fun _ => none) (domain cfg)

theorem formed {cfg launch a b} (hp : Pre cfg a b launch) (ha : ¬ Active cfg) : WellFormed code launch (execution cfg launch) := by
  refine ⟨by rw [hp.2.2.1]; exact geometry_valid cfg,?_,?_,?_⟩
  · have he : (execution cfg launch).traces.map ThreadTrace.id = launch.geometry.threads := by simp [execution,trace,List.map_map,Function.comp_def]
    rw [he]
    exact Geometry.threads_nodup _
  · intro t ht
    obtain ⟨id,hmem,rfl⟩ := List.mem_map.mp ht
    have hv := Geometry.mem_threads.mp hmem
    refine ⟨hv,?_⟩
    have hparams : AmpereTiledInit.Params cfg launch.params := by rw [hp.2.2.2]; exact AmpereTiledInit.canonical_params cfg
    change Ampere.run (context launch id) oracle code (if cfg.m = 0 then 15 else 17) {} = _
    by_cases hm : cfg.m = 0
    · simpa only [hm,ite_true,trace] using AmpereTiledSource.row_masked_run (context launch id) oracle hparams hm
    · have hn : cfg.n = 0 := by by_contra hn; exact ha ⟨by omega,by omega⟩
      simpa only [hm,ite_false,trace] using AmpereTiledSource.col_masked_run hp.1 (context launch id) oracle hparams
        (by simpa only [context,hp.2.2.1] using hv) (by omega) hn
  · intro id hv
    exact ⟨trace cfg launch id,List.mem_map.mpr ⟨id,Geometry.mem_threads.mpr hv,rfl⟩,rfl⟩

theorem complete (cfg : Config) (launch : Scalar.Launch) : Complete (execution cfg launch) := by
  intro t ht
  obtain ⟨id,_,rfl⟩ := List.mem_map.mp ht
  rfl

theorem event_none (cfg : Config) (launch : Scalar.Launch) (event) : (execution cfg launch).eventAt event = none := by
  unfold Candidate.eventAt
  cases hf : (execution cfg launch).traceAt event.thread with
  | none => simp [hf]
  | some t =>
    have ht := List.mem_of_find?_eq_some hf
    obtain ⟨id,_,rfl⟩ := List.mem_map.mp ht
    simp [hf,trace]
theorem copy_none (cfg : Config) (launch : Scalar.Launch) (operation) : (execution cfg launch).copyAt operation = none := by
  unfold Candidate.copyAt
  cases hf : (execution cfg launch).traceAt operation.thread with
  | none => simp [hf]
  | some t =>
    have ht := List.mem_of_find?_eq_some hf
    obtain ⟨id,_,rfl⟩ := List.mem_map.mp ht
    simp [hf,trace,AmpereTiledInit.maskedFinal,AmpereTiledInit.indexed,intAssign]
theorem write_none (cfg : Config) (launch : Scalar.Launch) (node loc) : (execution cfg launch).writeByte node loc = none := by
  cases node <;> simp [Candidate.writeByte,Candidate.memoryKind,event_none,copy_none]
theorem read_none (cfg : Config) (launch : Scalar.Launch) (node loc) : (execution cfg launch).readByte node loc = none := by
  cases node <;> simp [Candidate.readByte,Candidate.memoryKind,event_none,copy_none]

theorem base_false (cfg : Config) (launch : Scalar.Launch) (x y) : ¬ BaseEdge (execution cfg launch) x y := by
  cases x <;> cases y <;>
    simp [BaseEdge,ProgramOrder,BarrierSync,IssueBefore,CopyInternal,Completion,WaitCovers,Candidate.Present,event_none,copy_none]
theorem aligned (cfg : Config) (launch : Scalar.Launch) : SourceAligned code launch (execution cfg launch) := by
  rintro a b ⟨_,bid,generation,ha,_⟩
  rw [event_none] at ha
  cases ha
theorem barriers (cfg : Config) (launch : Scalar.Launch) : BarrierParticipation (execution cfg launch) := by
  intro event bid generation he
  rw [event_none] at he
  cases he
theorem control (cfg : Config) (launch : Scalar.Launch) : ControlAcyclic (execution cfg launch) := by
  apply control_acyclic_of_rank (fun _ => 0)
  · exact fun x y he => (base_false cfg launch x y he).elim
  · intro x y he
    cases x <;> cases y <;> simp [ExitBeforeReturn,Candidate.Present,event_none] at he
  · intro x y he
    cases x <;> cases y <;> simp [MmaControl,event_none] at he
theorem mma (cfg : Config) (launch : Scalar.Launch) : MmaConditions code launch (execution cfg launch) := by
  intro event call he
  rw [event_none] at he
  cases he

theorem memory (cfg : Config) (launch : Scalar.Launch) : MemoryConstraints (execution cfg launch) launch.initial rf (co cfg launch) := by
  apply MemoryGraph.initial_co_conditions (fun _ => 0)
  · exact fun x y he => (base_false cfg launch x y (.inl he)).elim
  · intro x y he
    exact he.rank_lt (fun _ => 0) (fun a b hab => (base_false cfg launch a b hab).elim)
  · intro loc x y vx vy hx _
    rw [graph_writeByte,write_none] at hx
    cases hx
  · intro read loc value hr
    rw [graph_readByte,read_none] at hr
    cases hr
  · intro read writer loc vr vw hr _ _
    rw [graph_readByte,read_none] at hr
    cases hr
  · intro read writer loc vr vw hr _ _
    rw [graph_readByte,read_none] at hr
    cases hr

theorem observer (cfg : Config) (launch : Scalar.Launch) :
    ObserverConstraints (execution cfg launch) launch.initial rf (co cfg launch) (observation cfg launch) := by
  apply MemoryGraph.selected_observation_on_domain (complete cfg launch)
  · exact fun loc hl => domain_global hl
  · intro loc _ writer value hw
    rw [graph_writeByte,write_none] at hw
    cases hw

theorem checked {cfg launch a b} (hp : Pre cfg a b launch) (ha : ¬ Active cfg) : CheckedConditions code launch (execution cfg launch) rf (co cfg launch) :=
  ⟨formed hp ha,aligned cfg launch,barriers cfg launch,control cfg launch,memory cfg launch,mma cfg launch⟩

end
end Ptx.AmpereTiledWitnessInactive
