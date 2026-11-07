import Ptx.Kernels.ScalarMatmulOutput
import Ptx.ISA.Enumeration

/-! A complete launch candidate built from actual source executions. The chosen
input oracle is used only for this existence witness; universal correctness
continues to quantify over arbitrary oracles. Memory consistency is separate. -/
namespace Ptx.ScalarMatmulEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.ScalarMatmul Ptx.ScalarMatmulInit Ptx.ScalarMatmulLoop
noncomputable section

structure CompletedRun (ctx : Scalar.Context) (oracle : Scalar.Oracle) where
  count : Nat
  final : Scalar.State
  events : List Scalar.Kind
  executes : Scalar.run ctx oracle code count {} = .ok (final,events)
  done : final.core.thread.status = .done

def matrixOracle (cfg : Config) (a b : Matrix) (id : ThreadId) : Scalar.Oracle :=
  inputOracle a b (row cfg.geometry.block id) (col cfg.geometry.block id)

theorem thread_completes (cfg : Config) (a b : Matrix) (params : Bindings)
    (hp : Params cfg.input params) {id : ThreadId} (hv : id.Valid cfg.geometry) :
    Nonempty (CompletedRun (context cfg params id) (matrixOracle cfg a b id)) := by
  have hb := index_bounds cfg hv params
  by_cases hr : row cfg.geometry.block id < cfg.input.m
  · by_cases hc : col cfg.geometry.block id < cfg.input.n
    · obtain ⟨final,hex,hf⟩ := active_execution cfg.input (context cfg params id) a b hp hb hr hc
        (address_bounds cfg params ⟨hr,hc⟩)
      exact ⟨⟨36+9*cfg.input.k,final,_,hex,hf.done⟩⟩
    · obtain ⟨final,hex,hd,_⟩ := masked_col cfg.input (context cfg params id) (matrixOracle cfg a b id)
        hp hb hr (Nat.le_of_not_gt hc)
      exact ⟨⟨21,final,[],hex,hd⟩⟩
  · obtain ⟨final,hex,hd,_⟩ := masked_row cfg.input (context cfg params id) (matrixOracle cfg a b id)
      hp hb (Nat.le_of_not_gt hr)
    exact ⟨⟨19,final,[],hex,hd⟩⟩

def completedRun (cfg : Config) (a b : Matrix) (params : Bindings)
    (hp : Params cfg.input params) {id : ThreadId} (hv : id.Valid cfg.geometry) :
    CompletedRun (context cfg params id) (matrixOracle cfg a b id) :=
  Classical.choice (thread_completes cfg a b params hp hv)

def canonicalTrace (cfg : Config) (a b : Matrix) (params : Bindings)
    (hp : Params cfg.input params) (id : ThreadId) : Scalar.ThreadTrace := by
  classical
  exact if hv : id.Valid cfg.geometry then
      let run := completedRun cfg a b params hp hv
      ⟨id,matrixOracle cfg a b id,run.count,run.final.core,run.events⟩
    else ⟨id,matrixOracle cfg a b id,0,{},[]⟩

@[simp] theorem canonical_trace_id (cfg : Config) (a b : Matrix) (params : Bindings)
    (hp : Params cfg.input params) (id : ThreadId) : (canonicalTrace cfg a b params hp id).id = id := by
  unfold canonicalTrace; split <;> rfl

@[simp] theorem canonical_trace_oracle (cfg : Config) (a b : Matrix) (params : Bindings)
    (hp : Params cfg.input params) (id : ThreadId) :
    (canonicalTrace cfg a b params hp id).oracle = matrixOracle cfg a b id := by
  unfold canonicalTrace; split <;> rfl

theorem canonical_trace_produced (cfg : Config) (a b : Matrix) (params : Bindings)
    (hp : Params cfg.input params) {id : ThreadId} (hv : id.Valid cfg.geometry) :
    Scalar.Produced code params (canonicalTrace cfg a b params hp id) cfg.geometry.block := by
  unfold canonicalTrace
  rw [dite_eq_left hv]
  exact ⟨(completedRun cfg a b params hp hv).final.floats,(completedRun cfg a b params hp hv).executes⟩

theorem canonical_trace_done (cfg : Config) (a b : Matrix) (params : Bindings)
    (hp : Params cfg.input params) {id : ThreadId} (hv : id.Valid cfg.geometry) :
    (canonicalTrace cfg a b params hp id).final.thread.status = .done := by
  unfold canonicalTrace
  rw [dite_eq_left hv]
  exact (completedRun cfg a b params hp hv).done

def canonical (cfg : Config) (a b : Matrix) (params : Bindings) (hp : Params cfg.input params) : Scalar.Candidate :=
  ⟨cfg.geometry.threads.map (canonicalTrace cfg a b params hp)⟩

theorem canonical_member (cfg : Config) (a b : Matrix) (params : Bindings)
    (hp : Params cfg.input params) {id : ThreadId} (hv : id.Valid cfg.geometry) :
    canonicalTrace cfg a b params hp id ∈ (canonical cfg a b params hp).traces :=
  List.mem_map.mpr ⟨id,Geometry.mem_threads.mpr hv,rfl⟩

theorem canonical_ids (cfg : Config) (a b : Matrix) (params : Bindings) (hp : Params cfg.input params) :
    ((canonical cfg a b params hp).traces.map Event.ThreadTrace.id).Nodup := by
  simpa [canonical,List.map_map,Function.comp_def] using cfg.geometry.threads_nodup

theorem canonical_wellFormed (cfg : Config) (a b : Matrix) {launch : Scalar.Launch}
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params) :
    Scalar.WellFormed code launch (canonical cfg a b launch.params hp) := by
  refine ⟨hg ▸ cfg.valid,canonical_ids cfg a b launch.params hp,?_,?_⟩
  · intro t ht
    obtain ⟨id,hin,rfl⟩ := List.mem_map.mp ht
    have hv := Geometry.mem_threads.mp hin
    refine ⟨by simpa [hg] using hv,?_⟩
    simpa only [hg] using canonical_trace_produced cfg a b launch.params hp hv
  · intro id hv
    have hv' : id.Valid cfg.geometry := by simpa only [hg] using hv
    exact ⟨_,canonical_member cfg a b launch.params hp hv',canonical_trace_id cfg a b launch.params hp id⟩

theorem canonical_complete (cfg : Config) (a b : Matrix) (params : Bindings) (hp : Params cfg.input params) :
    (canonical cfg a b params hp).Complete := by
  intro t ht
  obtain ⟨id,hin,rfl⟩ := List.mem_map.mp ht
  exact canonical_trace_done cfg a b params hp (Geometry.mem_threads.mp hin)

end
end Ptx.ScalarMatmulEvent
