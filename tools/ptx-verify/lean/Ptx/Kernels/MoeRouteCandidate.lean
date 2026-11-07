import Ptx.Kernels.MoeRouteOutput
import Ptx.ISA.Enumeration

/-! Independent PC=0 completion construction for every launched thread. The
chosen gate oracle is used for existence only, never as a universal premise. -/
namespace Ptx.MoeRouteEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeRouteThread
noncomputable section

structure CompletedRun (ctx : Scalar.Context) (oracle : Scalar.Oracle) where
  count : Nat
  final : Scalar.State
  events : List Scalar.Kind
  executes : Scalar.run ctx oracle code count {} = .ok (final,events)
  done : final.core.thread.status = .done

def gateOracle (cfg : Config) (gates : Moe.Matrix) (id : ThreadId) : Scalar.Oracle :=
  fun gate => .real .f32 (gates (index cfg id) gate)

theorem thread_completes (cfg : Config) (gates : Moe.Matrix) (params : Bindings)
    (hp : Params cfg.input params) {id : ThreadId} (hv : id.Valid cfg.geometry) :
    Nonempty (CompletedRun (context cfg params id) (gateOracle cfg gates id)) := by
  have hb := index_bounds cfg hv params
  by_cases ha : Active cfg id
  · have h := active_run cfg.input (context cfg params id) (gateOracle cfg gates id) gates hp hb ha
      (gate_end cfg ha) (route_end cfg ha) rfl rfl
    exact ⟨⟨22,_,_,h,MoeRouteSelect.final_done _ _⟩⟩
  · have h := masked_run cfg.input (context cfg params id) (gateOracle cfg gates id) hp hb (Nat.le_of_not_gt ha)
    exact ⟨⟨11,_,[],h,rfl⟩⟩

def completedRun (cfg : Config) (gates : Moe.Matrix) (params : Bindings)
    (hp : Params cfg.input params) {id : ThreadId} (hv : id.Valid cfg.geometry) :
    CompletedRun (context cfg params id) (gateOracle cfg gates id) :=
  Classical.choice (thread_completes cfg gates params hp hv)

def canonicalTrace (cfg : Config) (gates : Moe.Matrix) (params : Bindings)
    (hp : Params cfg.input params) (id : ThreadId) : Scalar.ThreadTrace := by
  classical
  exact if hv : id.Valid cfg.geometry then
      let run := completedRun cfg gates params hp hv
      ⟨id,gateOracle cfg gates id,run.count,run.final.core,run.events⟩
    else ⟨id,gateOracle cfg gates id,0,{},[]⟩

@[simp] theorem canonical_trace_id (cfg : Config) (gates : Moe.Matrix) (params : Bindings)
    (hp : Params cfg.input params) (id : ThreadId) : (canonicalTrace cfg gates params hp id).id = id := by
  unfold canonicalTrace; split <;> rfl
@[simp] theorem canonical_trace_oracle (cfg : Config) (gates : Moe.Matrix) (params : Bindings)
    (hp : Params cfg.input params) (id : ThreadId) :
    (canonicalTrace cfg gates params hp id).oracle = gateOracle cfg gates id := by
  unfold canonicalTrace; split <;> rfl

theorem canonical_trace_produced (cfg : Config) (gates : Moe.Matrix) (params : Bindings)
    (hp : Params cfg.input params) {id : ThreadId} (hv : id.Valid cfg.geometry) :
    Scalar.Produced code params (canonicalTrace cfg gates params hp id) cfg.geometry.block := by
  unfold canonicalTrace
  rw [dite_eq_left hv]
  exact ⟨(completedRun cfg gates params hp hv).final.floats,(completedRun cfg gates params hp hv).executes⟩
theorem canonical_trace_done (cfg : Config) (gates : Moe.Matrix) (params : Bindings)
    (hp : Params cfg.input params) {id : ThreadId} (hv : id.Valid cfg.geometry) :
    (canonicalTrace cfg gates params hp id).final.thread.status = .done := by
  unfold canonicalTrace
  rw [dite_eq_left hv]
  exact (completedRun cfg gates params hp hv).done

def canonical (cfg : Config) (gates : Moe.Matrix) (params : Bindings) (hp : Params cfg.input params) : Scalar.Candidate :=
  ⟨cfg.geometry.threads.map (canonicalTrace cfg gates params hp)⟩

theorem canonical_member (cfg : Config) (gates : Moe.Matrix) (params : Bindings)
    (hp : Params cfg.input params) {id : ThreadId} (hv : id.Valid cfg.geometry) :
    canonicalTrace cfg gates params hp id ∈ (canonical cfg gates params hp).traces :=
  List.mem_map.mpr ⟨id,Geometry.mem_threads.mpr hv,rfl⟩
theorem canonical_ids (cfg : Config) (gates : Moe.Matrix) (params : Bindings) (hp : Params cfg.input params) :
    ((canonical cfg gates params hp).traces.map Event.ThreadTrace.id).Nodup := by
  simpa [canonical,List.map_map,Function.comp_def] using cfg.geometry.threads_nodup

theorem canonical_wellFormed (cfg : Config) (gates : Moe.Matrix) {launch : Scalar.Launch}
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params) :
    Scalar.WellFormed code launch (canonical cfg gates launch.params hp) := by
  refine ⟨hg ▸ cfg.valid,canonical_ids cfg gates launch.params hp,?_,?_⟩
  · intro t ht
    obtain ⟨id,hin,rfl⟩ := List.mem_map.mp ht
    have hv := Geometry.mem_threads.mp hin
    refine ⟨by simpa [hg] using hv,?_⟩
    simpa only [hg] using canonical_trace_produced cfg gates launch.params hp hv
  · intro id hv
    have hv' : id.Valid cfg.geometry := by simpa only [hg] using hv
    exact ⟨_,canonical_member cfg gates launch.params hp hv',canonical_trace_id cfg gates launch.params hp id⟩

theorem canonical_complete (cfg : Config) (gates : Moe.Matrix) (params : Bindings) (hp : Params cfg.input params) :
    (canonical cfg gates params hp).Complete := by
  intro t ht
  obtain ⟨id,hin,rfl⟩ := List.mem_map.mp ht
  exact canonical_trace_done cfg gates params hp (Geometry.mem_threads.mp hin)

end
end Ptx.MoeRouteEvent
