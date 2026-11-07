import Ptx.Kernels.MoeCombineOutput
import Ptx.ISA.Enumeration

/-! A complete launch candidate built from actual source executions. The chosen
input oracle is used only for this existence witness; universal correctness
continues to quantify over arbitrary oracles. Memory consistency is separate. -/
namespace Ptx.MoeCombineEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeCombine
noncomputable section

structure CompletedRun (ctx : Scalar.Context) (oracle : Scalar.Oracle) where
  count : Nat
  final : Scalar.State
  events : List Scalar.Kind
  executes : Scalar.run ctx oracle code count {} = .ok (final,events)
  done : final.core.thread.status = .done

def expertOracle (cfg : Config) (gates values : Moe.Matrix) (id : ThreadId) : Scalar.Oracle := fun query =>
  if query = 0 then .integer (Moe.selected gates (row cfg.geometry.block id))
  else .real .f32 (values (row cfg.geometry.block id) (col cfg.geometry.block id))

@[simp] theorem expertOracle_route (cfg : Config) (gates values : Moe.Matrix) (id : ThreadId) :
    expertOracle cfg gates values id 0 = .integer (Moe.selected gates (row cfg.geometry.block id)) := rfl

@[simp] theorem expertOracle_value (cfg : Config) (gates values : Moe.Matrix) (id : ThreadId) :
    expertOracle cfg gates values id 1 = .real .f32 (values (row cfg.geometry.block id) (col cfg.geometry.block id)) := rfl

theorem selected_wrap (gates : Moe.Matrix) (row : Nat) : wrap 32 (Moe.selected gates row) = Moe.selected gates row :=
  Nat.mod_eq_of_lt (by have := Moe.selected_bound gates row; omega)

theorem expertOracle_expert (cfg : Config) (gates values : Moe.Matrix) (id : ThreadId) :
    expert (expertOracle cfg gates values id) = Moe.selected gates (row cfg.geometry.block id) := by
  simp only [expert,routeValue,expertOracle_route]
  exact selected_wrap gates (row cfg.geometry.block id)

theorem thread_completes (cfg : Config) (gates values : Moe.Matrix) (params : Bindings)
    (hp : Params cfg.input params) {id : ThreadId} (hv : id.Valid cfg.geometry) :
    Nonempty (CompletedRun (context cfg params id) (expertOracle cfg gates values id)) := by
  have hb := index_bounds cfg hv params
  have he : wrap 32 (Moe.selected gates (row cfg.geometry.block id)) < 2 := by
    rw [selected_wrap gates (row cfg.geometry.block id)]
    exact Moe.selected_bound _ _
  by_cases hr : row cfg.geometry.block id < cfg.input.m
  · by_cases hc : col cfg.geometry.block id < cfg.input.n
    · obtain ⟨final,hex,hd,_⟩ := active_execution cfg.input (context cfg params id) (expertOracle cfg gates values id)
        (Moe.selected gates (row cfg.geometry.block id)) (values (row cfg.geometry.block id) (col cfg.geometry.block id))
        hp hb hr hc (route_pointer_bound cfg ⟨hr,hc⟩) (expertOracle_route cfg gates values id) he
        (address_bounds cfg params ⟨hr,hc⟩ he) (expertOracle_value cfg gates values id)
      exact ⟨⟨_,final,_,hex,hd⟩⟩
    · obtain ⟨final,hex,hd,_⟩ := masked_col cfg.input (context cfg params id) (expertOracle cfg gates values id)
        hp hb hr (Nat.le_of_not_gt hc)
      exact ⟨⟨20,final,[],hex,hd⟩⟩
  · obtain ⟨final,hex,hd,_⟩ := masked_row cfg.input (context cfg params id) (expertOracle cfg gates values id)
      hp hb (Nat.le_of_not_gt hr)
    exact ⟨⟨18,final,[],hex,hd⟩⟩

def completedRun (cfg : Config) (gates values : Moe.Matrix) (params : Bindings)
    (hp : Params cfg.input params) {id : ThreadId} (hv : id.Valid cfg.geometry) :
    CompletedRun (context cfg params id) (expertOracle cfg gates values id) :=
  Classical.choice (thread_completes cfg gates values params hp hv)

def canonicalTrace (cfg : Config) (gates values : Moe.Matrix) (params : Bindings)
    (hp : Params cfg.input params) (id : ThreadId) : Scalar.ThreadTrace := by
  classical
  exact if hv : id.Valid cfg.geometry then
      let run := completedRun cfg gates values params hp hv
      ⟨id,expertOracle cfg gates values id,run.count,run.final.core,run.events⟩
    else ⟨id,expertOracle cfg gates values id,0,{},[]⟩

@[simp] theorem canonical_trace_id (cfg : Config) (gates values : Moe.Matrix) (params : Bindings)
    (hp : Params cfg.input params) (id : ThreadId) : (canonicalTrace cfg gates values params hp id).id = id := by
  unfold canonicalTrace; split <;> rfl

@[simp] theorem canonical_trace_oracle (cfg : Config) (gates values : Moe.Matrix) (params : Bindings)
    (hp : Params cfg.input params) (id : ThreadId) :
    (canonicalTrace cfg gates values params hp id).oracle = expertOracle cfg gates values id := by
  unfold canonicalTrace; split <;> rfl

theorem canonical_trace_produced (cfg : Config) (gates values : Moe.Matrix) (params : Bindings)
    (hp : Params cfg.input params) {id : ThreadId} (hv : id.Valid cfg.geometry) :
    Scalar.Produced code params (canonicalTrace cfg gates values params hp id) cfg.geometry.block := by
  unfold canonicalTrace
  rw [dite_eq_left hv]
  exact ⟨(completedRun cfg gates values params hp hv).final.floats,(completedRun cfg gates values params hp hv).executes⟩

theorem canonical_trace_done (cfg : Config) (gates values : Moe.Matrix) (params : Bindings)
    (hp : Params cfg.input params) {id : ThreadId} (hv : id.Valid cfg.geometry) :
    (canonicalTrace cfg gates values params hp id).final.thread.status = .done := by
  unfold canonicalTrace
  rw [dite_eq_left hv]
  exact (completedRun cfg gates values params hp hv).done

def canonical (cfg : Config) (gates values : Moe.Matrix) (params : Bindings) (hp : Params cfg.input params) : Scalar.Candidate :=
  ⟨cfg.geometry.threads.map (canonicalTrace cfg gates values params hp)⟩

theorem canonical_member (cfg : Config) (gates values : Moe.Matrix) (params : Bindings)
    (hp : Params cfg.input params) {id : ThreadId} (hv : id.Valid cfg.geometry) :
    canonicalTrace cfg gates values params hp id ∈ (canonical cfg gates values params hp).traces :=
  List.mem_map.mpr ⟨id,Geometry.mem_threads.mpr hv,rfl⟩

theorem canonical_ids (cfg : Config) (gates values : Moe.Matrix) (params : Bindings) (hp : Params cfg.input params) :
    ((canonical cfg gates values params hp).traces.map Event.ThreadTrace.id).Nodup := by
  simpa [canonical,List.map_map,Function.comp_def] using cfg.geometry.threads_nodup

theorem canonical_wellFormed (cfg : Config) (gates values : Moe.Matrix) {launch : Scalar.Launch}
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params) :
    Scalar.WellFormed code launch (canonical cfg gates values launch.params hp) := by
  refine ⟨hg ▸ cfg.valid,canonical_ids cfg gates values launch.params hp,?_,?_⟩
  · intro t ht
    obtain ⟨id,hin,rfl⟩ := List.mem_map.mp ht
    have hv := Geometry.mem_threads.mp hin
    refine ⟨by simpa [hg] using hv,?_⟩
    simpa only [hg] using canonical_trace_produced cfg gates values launch.params hp hv
  · intro id hv
    have hv' : id.Valid cfg.geometry := by simpa only [hg] using hv
    exact ⟨_,canonical_member cfg gates values launch.params hp hv',canonical_trace_id cfg gates values launch.params hp id⟩

theorem canonical_complete (cfg : Config) (gates values : Moe.Matrix) (params : Bindings) (hp : Params cfg.input params) :
    (canonical cfg gates values params hp).Complete := by
  intro t ht
  obtain ⟨id,hin,rfl⟩ := List.mem_map.mp ht
  exact canonical_trace_done cfg gates values params hp (Geometry.mem_threads.mp hin)

end
end Ptx.MoeCombineEvent
