import Ptx.Kernels.ScalarMatmulCandidate

/-! A separate complete consistent execution and observation witness for every
matrix precondition. This discharges model-relative nonvacuity, not physical
allocation/runtime correctness or full correspondence with the PTX standard. -/
namespace Ptx.ScalarMatmulEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.ScalarMatmul Ptx.ScalarMatmulLoop
noncomputable section

theorem no_barrier_returns {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (event : EventId) (bid generation : Nat) : execution.eventAt event ≠ some (.barrierReturn bid generation) := by
  intro he
  obtain ⟨_,_,_,hs⟩ := event_shape hw hd hg hp he
  rcases hs with ⟨_,_,_,hk⟩ | ⟨_,_,_,hk⟩ | ⟨_,hk⟩ <;> cases hk

theorem canonical_read_value (cfg : Config) (a b : Matrix) {launch : Scalar.Launch}
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg a b launch.initial)
    {read : EventId} {loc : Location} {value : Symbolic.Byte}
    (hr : (canonical cfg a b launch.params hp).readByte read loc = some value) : launch.initial loc = value := by
  let execution := canonical cfg a b launch.params hp
  have hw := canonical_wellFormed cfg a b hg hp
  have hd := canonical_complete cfg a b launch.params hp
  change execution.readByte read loc = some value at hr
  cases he : execution.eventAt read with
  | none => simp [Candidate.readByte,he] at hr
  | some kind =>
    obtain ⟨oracle,hv,ha,hcases⟩ := event_shape hw hd hg hp he
    have ht := canonical_member cfg a b launch.params hp hv
    have hat : Active cfg (canonicalTrace cfg a b launch.params hp read.thread).id := by simpa using ha
    rcases hcases with ⟨k,hk,hs,_⟩ | ⟨k,hk,hs,_⟩ | ⟨_,rfl⟩
    · have hev := active_read_a hw hd hg hp ht hat hk
      simp only [canonical_trace_id,canonical_trace_oracle,matrixOracle,
        realReply_of_typed (inputOracle_even a b _ _ k)] at hev
      have hid : read = ⟨read.thread,2*k⟩ := by cases read; simp_all
      rw [← hid] at hev
      change execution.eventAt read = _ at hev
      have hb : payloadByte (aLoc cfg (row cfg.geometry.block read.thread) k)
          (Symbolic.encode .f32 (a (row cfg.geometry.block read.thread) k)) loc = some value := by
        simpa only [Candidate.readByte,hev,Option.bind_some,Kind.readByte] using hr
      exact represented_payload (hi.1 _ _ ha.1 hk) hb
    · have hev := active_read_b hw hd hg hp ht hat hk
      simp only [canonical_trace_id,canonical_trace_oracle,matrixOracle,
        realReply_of_typed (inputOracle_odd a b _ _ k)] at hev
      have hid : read = ⟨read.thread,2*k+1⟩ := by cases read; simp_all
      rw [← hid] at hev
      change execution.eventAt read = _ at hev
      have hb : payloadByte (bLoc cfg k (col cfg.geometry.block read.thread))
          (Symbolic.encode .f32 (b k (col cfg.geometry.block read.thread))) loc = some value := by
        simpa only [Candidate.readByte,hev,Option.bind_some,Kind.readByte] using hr
      exact represented_payload (hi.2 _ _ hk ha.2) hb
    · simp [Candidate.readByte,he,Kind.readByte] at hr

theorem canonical_memory (cfg : Config) (a b : Matrix) {launch : Scalar.Launch}
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg a b launch.initial) :
    GenericMemoryConditions (canonical cfg a b launch.params hp) launch.initial
      (fun _ _ => .initial) (InitialCo (canonical cfg a b launch.params hp)) := by
  have hw := canonical_wellFormed cfg a b hg hp
  have hd := canonical_complete cfg a b launch.params hp
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
  · intro read loc value hr
    exact congrArg some (canonical_read_value cfg a b hg hp hi hr)
  · intro _ _ _ _ _ _ _ he
    cases he
  · intro read writer loc vr vw hr hwrite _
    have hu := input_unwritten hw hd hg hp (read_region hw hd hg hp hr) writer
    rw [hu] at hwrite
    cases hwrite

theorem nonvacuous (cfg : Config) (a b : Matrix) (domain : List Location)
    (hglobal : ∀ loc ∈ domain, loc.space = .global) :
    Scalar.Nonvacuous code (Pre cfg a b) (fun _ => domain) := by
  intro launch hp
  let execution := canonical cfg a b launch.params hp.2.1
  refine ⟨execution,(fun _ _ => .initial),InitialCo execution,
    selectedObservation execution launch.initial (writerSelector execution) domain,
    canonical_wellFormed cfg a b hp.1 hp.2.1,
    canonical_memory cfg a b hp.1 hp.2.1 hp.2.2,?_,rfl⟩
  apply unique_writers_observation (canonical_complete cfg a b launch.params hp.2.1) hglobal
  intro loc x y vx vy hx hy
  exact overlapping_writers_equal (canonical_wellFormed cfg a b hp.1 hp.2.1)
    (canonical_complete cfg a b launch.params hp.2.1) hp.1 hp.2.1 hx hy

end
end Ptx.ScalarMatmulEvent
