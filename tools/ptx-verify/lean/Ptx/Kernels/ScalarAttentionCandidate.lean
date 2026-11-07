import Ptx.Kernels.ScalarAttentionOutput
import Ptx.ISA.Enumeration

/-! A complete candidate enumerating every valid launch thread and executing the
actual source from PC=0. The selected oracle is used only for existence, not the
universal output contract. Memory consistency/observation remain separate. -/
namespace Ptx.ScalarAttentionEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.ScalarAttention Ptx.ScalarAttentionInit
noncomputable section

structure CompletedRun (ctx : Scalar.Context) (oracle : Scalar.Oracle) where
  count : Nat
  final : Scalar.State
  events : List Scalar.Kind
  executes : Scalar.run ctx oracle code count {} = .ok (final,events)
  done : final.core.thread.status = .done

def inputOracle (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (id : ThreadId) : Scalar.Oracle :=
  ScalarAttentionOracle.answers q key value (row cfg.geometry.block id) (col cfg.geometry.block id) cfg.input.dim scale

theorem thread_completes (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (params : Bindings)
    (hp : Params cfg.input params) {id : ThreadId} (hv : id.Valid cfg.geometry) :
    Nonempty (CompletedRun (context cfg params id) (inputOracle cfg q key value scale id)) := by
  have hb := index_bounds cfg hv params
  by_cases hr : row cfg.geometry.block id < cfg.input.m
  · by_cases hc : col cfg.geometry.block id < cfg.input.dim
    · by_cases hn : 0 < cfg.input.n
      · obtain ⟨final,hex,hf⟩ := active_execution cfg.input (context cfg params id) q key value scale hp hb hr hc hn
          (address_bounds cfg params ⟨hr,hc⟩ hn)
        exact ⟨⟨35+cfg.input.n*(9*cfg.input.dim+26),final,_,hex,hf⟩⟩
      · obtain ⟨final,hex,hf,_⟩ := empty_execution cfg.input (context cfg params id) (inputOracle cfg q key value scale id)
          hp hb hr hc (by omega) (output_bound cfg params ⟨hr,hc⟩)
        exact ⟨⟨32,final,_,hex,hf⟩⟩
    · obtain ⟨final,hex,hd,_⟩ := masked_col cfg.input (context cfg params id) (inputOracle cfg q key value scale id)
        hp hb hr (Nat.le_of_not_gt hc)
      exact ⟨⟨23,final,[],hex,hd⟩⟩
  · obtain ⟨final,hex,hd,_⟩ := masked_row cfg.input (context cfg params id) (inputOracle cfg q key value scale id)
      hp hb (Nat.le_of_not_gt hr)
    exact ⟨⟨21,final,[],hex,hd⟩⟩

def completedRun (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (params : Bindings)
    (hp : Params cfg.input params) {id : ThreadId} (hv : id.Valid cfg.geometry) :
    CompletedRun (context cfg params id) (inputOracle cfg q key value scale id) :=
  Classical.choice (thread_completes cfg q key value scale params hp hv)

def canonicalTrace (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (params : Bindings)
    (hp : Params cfg.input params) (id : ThreadId) : Scalar.ThreadTrace := by
  classical
  exact if hv : id.Valid cfg.geometry then
      let run := completedRun cfg q key value scale params hp hv
      ⟨id,inputOracle cfg q key value scale id,run.count,run.final.core,run.events⟩
    else ⟨id,inputOracle cfg q key value scale id,0,{},[]⟩

@[simp] theorem canonical_trace_id (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (params : Bindings)
    (hp : Params cfg.input params) (id : ThreadId) : (canonicalTrace cfg q key value scale params hp id).id = id := by
  unfold canonicalTrace; split <;> rfl

@[simp] theorem canonical_trace_oracle (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (params : Bindings)
    (hp : Params cfg.input params) (id : ThreadId) :
    (canonicalTrace cfg q key value scale params hp id).oracle = inputOracle cfg q key value scale id := by
  unfold canonicalTrace; split <;> rfl

theorem canonical_trace_produced (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (params : Bindings)
    (hp : Params cfg.input params) {id : ThreadId} (hv : id.Valid cfg.geometry) :
    Scalar.Produced code params (canonicalTrace cfg q key value scale params hp id) cfg.geometry.block := by
  unfold canonicalTrace
  rw [dite_eq_left hv]
  exact ⟨(completedRun cfg q key value scale params hp hv).final.floats,(completedRun cfg q key value scale params hp hv).executes⟩

theorem canonical_trace_done (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (params : Bindings)
    (hp : Params cfg.input params) {id : ThreadId} (hv : id.Valid cfg.geometry) :
    (canonicalTrace cfg q key value scale params hp id).final.thread.status = .done := by
  unfold canonicalTrace
  rw [dite_eq_left hv]
  exact (completedRun cfg q key value scale params hp hv).done

def canonical (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (params : Bindings)
    (hp : Params cfg.input params) : Scalar.Candidate :=
  ⟨cfg.geometry.threads.map (canonicalTrace cfg q key value scale params hp)⟩

theorem canonical_member (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (params : Bindings)
    (hp : Params cfg.input params) {id : ThreadId} (hv : id.Valid cfg.geometry) :
    canonicalTrace cfg q key value scale params hp id ∈ (canonical cfg q key value scale params hp).traces :=
  List.mem_map.mpr ⟨id,Geometry.mem_threads.mpr hv,rfl⟩

theorem canonical_ids (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (params : Bindings) (hp : Params cfg.input params) :
    ((canonical cfg q key value scale params hp).traces.map Event.ThreadTrace.id).Nodup := by
  simpa [canonical,List.map_map,Function.comp_def] using cfg.geometry.threads_nodup

theorem canonical_wellFormed (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) {launch : Scalar.Launch}
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params) :
    Scalar.WellFormed code launch (canonical cfg q key value scale launch.params hp) := by
  refine ⟨hg ▸ cfg.valid,canonical_ids cfg q key value scale launch.params hp,?_,?_⟩
  · intro t ht
    obtain ⟨id,hin,rfl⟩ := List.mem_map.mp ht
    have hv := Geometry.mem_threads.mp hin
    refine ⟨by simpa [hg] using hv,?_⟩
    simpa only [hg] using canonical_trace_produced cfg q key value scale launch.params hp hv
  · intro id hv
    have hv' : id.Valid cfg.geometry := by simpa only [hg] using hv
    exact ⟨_,canonical_member cfg q key value scale launch.params hp hv',canonical_trace_id cfg q key value scale launch.params hp id⟩

theorem canonical_complete (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (params : Bindings) (hp : Params cfg.input params) :
    (canonical cfg q key value scale params hp).Complete := by
  intro t ht
  obtain ⟨id,hin,rfl⟩ := List.mem_map.mp ht
  exact canonical_trace_done cfg q key value scale params hp (Geometry.mem_threads.mp hin)

end
end Ptx.ScalarAttentionEvent
