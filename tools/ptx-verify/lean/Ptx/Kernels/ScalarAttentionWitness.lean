import Ptx.Kernels.ScalarAttentionCandidate

/-! Independent complete consistency/observation witnesses for every attention
precondition. They use actual PC=0 executions, initialized input payloads,
initial reads-from and unique output writers, not the desired output theorem.
Physical allocation/runtime and full PTX-model correspondence remain external. -/
namespace Ptx.ScalarAttentionEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.ScalarAttention Ptx.ScalarAttentionInit
noncomputable section

theorem input_scale (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (id : ThreadId) :
    replyReal (inputOracle cfg q key value scale id) 0 = scale := rfl

theorem input_q (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (params : Bindings)
    {id : ThreadId} (ha : Active cfg id) (hn : 0 < cfg.input.n) (j k : Nat) (hk : k < cfg.input.dim) :
    ScalarAttentionTrace.qValues (layout cfg params id ha hn) (inputOracle cfg q key value scale id) j k = q (row cfg.geometry.block id) k :=
  replyReal_of_typed (ScalarAttentionOracle.q_reply q key value _ _ cfg.input.dim j k scale hk)

theorem input_key (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (params : Bindings)
    {id : ThreadId} (ha : Active cfg id) (hn : 0 < cfg.input.n) (j k : Nat) (hk : k < cfg.input.dim) :
    ScalarAttentionTrace.keyValues (layout cfg params id ha hn) (inputOracle cfg q key value scale id) j k = key j k :=
  replyReal_of_typed (ScalarAttentionOracle.key_reply q key value _ _ cfg.input.dim j k scale hk)

theorem input_value (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (params : Bindings)
    {id : ThreadId} (ha : Active cfg id) (hn : 0 < cfg.input.n) (j : Nat) :
    ScalarAttentionTrace.values (layout cfg params id ha hn) (inputOracle cfg q key value scale id) j = value j (col cfg.geometry.block id) :=
  replyReal_of_typed (ScalarAttentionOracle.value_reply q key value _ _ cfg.input.dim j scale)

theorem input_read_payload (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (params : Bindings)
    {id : ThreadId} (ha : Active cfg id) {initial : Scalar.ByteMap}
    (hi : Initialized cfg q key value scale initial) {serial : Nat} {kind : Scalar.Kind}
    (he : (readEventsFor cfg params id (inputOracle cfg q key value scale id) ha)[serial]? = some kind)
    {loc : Location} {byte : Symbolic.Byte} (hr : kind.readByte loc = some byte) : initial loc = byte := by
  by_cases hn : 0 < cfg.input.n
  · have hen := reads_enabled ha hn
    rw [readEventsFor,dite_eq_left hn] at he
    cases serial with
    | zero =>
      simp only [List.cons_append,List.nil_append,List.getElem?_cons_zero] at he
      have hk := (Option.some.inj he).symm
      subst kind
      simp only [Kind.readByte,input_scale] at hr
      exact represented_payload (hi hen).1 hr
    | succ serial =>
      simp only [List.cons_append,List.nil_append,List.getElem?_cons_succ] at he
      obtain ⟨j,_,_,hj,hkind⟩ := ScalarAttentionReads.reads_event (by simp [layout,threadLayout]) he
      rcases hkind with ⟨k,hk,rfl⟩ | ⟨k,hk,rfl⟩ | rfl
      · simp only [Kind.readByte,input_q cfg q key value scale params ha hn j k hk,
          layout_q cfg params ha hn k] at hr
        exact represented_payload ((hi hen).2.1 _ _ ha.1 hk) hr
      · simp only [Kind.readByte,input_key cfg q key value scale params ha hn j k hk,
          layout_key cfg params ha hn j k] at hr
        exact represented_payload ((hi hen).2.2.1 _ _ hj hk) hr
      · rw [input_value cfg q key value scale params ha hn j,layout_value cfg params ha hn j] at hr
        exact represented_payload ((hi hen).2.2.2 _ _ hj ha.2) hr
  · simp [readEventsFor,hn] at he

theorem no_barrier_returns {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (event : EventId) (bid generation : Nat) : execution.eventAt event ≠ some (.barrierReturn bid generation) := by
  intro he
  obtain ⟨_,_,_,hs⟩ := event_shape hw hd hg hp he
  rcases hs with ⟨_,_,_,_,hk⟩ | ⟨_,hk⟩ <;> cases hk

theorem canonical_read_value (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) {launch : Scalar.Launch}
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg q key value scale launch.initial)
    {read : EventId} {loc : Location} {byte : Symbolic.Byte}
    (hr : (canonical cfg q key value scale launch.params hp).readByte read loc = some byte) : launch.initial loc = byte := by
  let execution := canonical cfg q key value scale launch.params hp
  have hw := canonical_wellFormed cfg q key value scale hg hp
  have hd := canonical_complete cfg q key value scale launch.params hp
  change execution.readByte read loc = some byte at hr
  cases he : execution.eventAt read with
  | none => simp [Candidate.readByte,he] at hr
  | some kind =>
    obtain ⟨t,ht,htid,hindex⟩ := eventAt_trace he
    have hread : kind.readByte loc = some byte := by simpa only [Candidate.readByte,he,Option.bind_some] using hr
    rcases trace_form hw hd hg hp ht with hempty | ⟨ha,hshape⟩
    · simp [hempty] at hindex
    · rw [hshape] at hindex
      unfold eventsFor at hindex
      by_cases hs : read.serial < writeSerial cfg
      · rw [List.getElem?_append_left (by simpa only [readEventsFor_length] using hs)] at hindex
        obtain ⟨id,hin,htcan⟩ := List.mem_map.mp ht
        have horacle : t.oracle = inputOracle cfg q key value scale t.id := by
          rw [← htcan,canonical_trace_id,canonical_trace_oracle]
        rw [horacle] at hindex
        exact input_read_payload cfg q key value scale launch.params ha hi hindex hread
      · rw [List.getElem?_append_right (by simp only [readEventsFor_length]; omega)] at hindex
        have hb := (List.getElem?_eq_some_iff.mp hindex).1
        simp only [List.length_cons,List.length_nil] at hb
        have hz : read.serial-(readEventsFor cfg launch.params t.id t.oracle ha).length = 0 := by omega
        rw [hz,List.getElem?_cons_zero] at hindex
        have hk := (Option.some.inj hindex).symm
        subst kind
        simp [Kind.readByte] at hread

theorem canonical_memory (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) {launch : Scalar.Launch}
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg q key value scale launch.initial) :
    GenericMemoryConditions (canonical cfg q key value scale launch.params hp) launch.initial
      (fun _ _ => .initial) (InitialCo (canonical cfg q key value scale launch.params hp)) := by
  have hw := canonical_wellFormed cfg q key value scale hg hp
  have hd := canonical_complete cfg q key value scale launch.params hp
  have hn := no_barrier_returns hw hd hg hp
  apply initial_co_conditions (fun event => event.serial)
  · intro _ _ hpo; exact hpo.2.2.2
  · rintro _ _ ⟨_,bid,generation,_,hreturn⟩
    exact (hn _ bid generation hreturn).elim
  · rintro _ _ ⟨_,_,_,_,_,bid,generation,hreturn,_⟩
    exact (hn _ bid generation hreturn).elim
  · intro event bid generation he
    exact (hn event bid generation he).elim
  · intro loc x y vx vy hx hy
    exact overlapping_writers_equal hw hd hg hp hx hy
  · intro read loc byte hr
    exact congrArg some (canonical_read_value cfg q key value scale hg hp hi hr)
  · intro _ _ _ _ _ _ _ he
    cases he
  · intro read writer loc vr vw hr hwrite _
    have hu := input_unwritten hw hd hg hp (read_region hw hd hg hp hr) writer
    rw [hu] at hwrite
    cases hwrite

theorem nonvacuous (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (domain : List Location)
    (hglobal : ∀ loc ∈ domain, loc.space = .global) :
    Scalar.Nonvacuous code (Pre cfg q key value scale) (fun _ => domain) := by
  intro launch hp
  let execution := canonical cfg q key value scale launch.params hp.2.1
  refine ⟨execution,(fun _ _ => .initial),InitialCo execution,
    selectedObservation execution launch.initial (writerSelector execution) domain,
    canonical_wellFormed cfg q key value scale hp.1 hp.2.1,
    canonical_memory cfg q key value scale hp.1 hp.2.1 hp.2.2,?_,rfl⟩
  apply unique_writers_observation (canonical_complete cfg q key value scale launch.params hp.2.1) hglobal
  intro loc x y vx vy hx hy
  exact overlapping_writers_equal (canonical_wellFormed cfg q key value scale hp.1 hp.2.1)
    (canonical_complete cfg q key value scale launch.params hp.2.1) hp.1 hp.2.1 hx hy

end
end Ptx.ScalarAttentionEvent
