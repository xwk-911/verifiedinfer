import Ptx.Kernels.MoeExpertsCandidate
import Ptx.Scalar.Checked

/-! A separate complete consistent execution and observation witness for every
matrix precondition. This discharges model-relative nonvacuity, not physical
allocation/runtime correctness or full correspondence with the PTX standard. -/
namespace Ptx.MoeExpertsEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeExperts Ptx.MoeExpertsLoop
noncomputable section

theorem no_barrier_returns {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (event : EventId) (bid generation : Nat) : execution.eventAt event ≠ some (.barrierReturn bid generation) := by
  intro he
  obtain ⟨_,_,_,hs⟩ := event_shape hw hd hg hp he
  rcases hs with ⟨_,hk⟩ | ⟨_,⟨_,_,_,hk⟩ | ⟨_,_,_,hk⟩ | ⟨_,hk⟩⟩ <;> cases hk

theorem canonical_read_value (cfg : Config) (gates x : Moe.Matrix) (weights : Moe.Weights) {launch : Scalar.Launch}
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg gates x weights launch.initial)
    {read : EventId} {loc : Location} {value : Symbolic.Byte}
    (hr : (canonical cfg gates x weights launch.params hp).readByte read loc = some value) : launch.initial loc = value := by
  let execution := canonical cfg gates x weights launch.params hp
  have hw := canonical_wellFormed cfg gates x weights hg hp
  have hd := canonical_complete cfg gates x weights launch.params hp
  change execution.readByte read loc = some value at hr
  cases he : execution.eventAt read with
  | none => simp [Candidate.readByte,he] at hr
  | some kind =>
    obtain ⟨oracle,hv,ha,hcases⟩ := event_shape hw hd hg hp he
    have ht := canonical_member cfg gates x weights launch.params hp hv
    have hat : Active cfg (canonicalTrace cfg gates x weights launch.params hp read.thread).id := by simpa using ha
    have hevalid : expert (canonicalTrace cfg gates x weights launch.params hp read.thread).oracle < 2 := by
      simp only [canonical_trace_oracle,expertOracle_expert]
      exact Moe.selected_bound _ _
    rcases hcases with ⟨hs,_⟩ | ⟨_,⟨k,hk,hs,_⟩ | ⟨k,hk,hs,_⟩ | ⟨_,rfl⟩⟩
    · have hev := active_route_read hw hd hg hp ht hat
      simp only [canonical_trace_id,canonical_trace_oracle,routeKind,expertOracle_expert] at hev
      have hid : read = ⟨read.thread,0⟩ := by cases read; simp_all
      rw [← hid] at hev
      change execution.eventAt read = _ at hev
      have hb : payloadByte (rLoc cfg (row cfg.geometry.block read.thread))
          (u32Bytes (Moe.selected gates (row cfg.geometry.block read.thread))) loc = some value := by
        simpa only [Candidate.readByte,hev,Option.bind_some,Kind.readByte] using hr
      exact represented_u32_payload (hi.1 _ ha.1 (by have := ha.2; omega)) hb
    · have hev := active_read_x hw hd hg hp ht hat hevalid hk
      simp only [canonical_trace_id,canonical_trace_oracle,
        FmaLoop.realReply_of_typed (expertOracle_x cfg gates x weights _ k)] at hev
      have hid : read = ⟨read.thread,1+2*k⟩ := by cases read; simp_all
      rw [← hid] at hev
      change execution.eventAt read = _ at hev
      have hb : payloadByte (xLoc cfg (row cfg.geometry.block read.thread) k)
          (Symbolic.encode .f32 (x (row cfg.geometry.block read.thread) k)) loc = some value := by
        simpa only [Candidate.readByte,hev,Option.bind_some,Kind.readByte] using hr
      exact represented_payload (hi.2.1 _ _ ha.1 hk (by have := ha.2; omega)) hb
    · have hev := active_read_w hw hd hg hp ht hat hevalid hk
      simp only [canonical_trace_id,canonical_trace_oracle,expertOracle_expert,
        FmaLoop.realReply_of_typed (expertOracle_w cfg gates x weights _ k)] at hev
      simp only [← Nat.add_assoc] at hev
      have hid : read = ⟨read.thread,1+2*k+1⟩ := by cases read; simp_all; omega
      rw [← hid] at hev
      change execution.eventAt read = _ at hev
      have hb : payloadByte (wLoc cfg (Moe.selected gates (row cfg.geometry.block read.thread)) k (col cfg.geometry.block read.thread))
          (Symbolic.encode .f32 (weights (Moe.selected gates (row cfg.geometry.block read.thread)) k (col cfg.geometry.block read.thread))) loc = some value := by
        simpa only [Candidate.readByte,hev,Option.bind_some,Kind.readByte] using hr
      exact represented_payload (hi.2.2 _ _ _ (Moe.selected_bound _ _) hk ha.2 (by have := ha.1; omega)) hb
    · simp [Candidate.readByte,he,Kind.readByte] at hr

theorem canonical_memory (cfg : Config) (gates x : Moe.Matrix) (weights : Moe.Weights) {launch : Scalar.Launch}
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg gates x weights launch.initial) :
    GenericMemoryConditions (canonical cfg gates x weights launch.params hp) launch.initial
      (fun _ _ => .initial) (InitialCo (canonical cfg gates x weights launch.params hp)) := by
  have hw := canonical_wellFormed cfg gates x weights hg hp
  have hd := canonical_complete cfg gates x weights launch.params hp
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
    exact congrArg some (canonical_read_value cfg gates x weights hg hp hi hr)
  · intro _ _ _ _ _ _ _ he
    cases he
  · intro read writer loc vr vw hr hwrite _
    have hu := input_unwritten hw hd hg hp (read_region hw hd hg hp hr) writer
    rw [hu] at hwrite
    cases hwrite

theorem nonvacuous (cfg : Config) (gates x : Moe.Matrix) (weights : Moe.Weights) (domain : List Location)
    (hglobal : ∀ loc ∈ domain, loc.space = .global) :
    Scalar.Nonvacuous code (Pre cfg gates x weights) (fun _ => domain) := by
  intro launch hp
  let execution := canonical cfg gates x weights launch.params hp.2.1
  refine ⟨execution,(fun _ _ => .initial),InitialCo execution,
    selectedObservation execution launch.initial (writerSelector execution) domain,
    canonical_wellFormed cfg gates x weights hp.1 hp.2.1,
    canonical_memory cfg gates x weights hp.1 hp.2.1 hp.2.2,?_,rfl⟩
  apply unique_writers_observation (canonical_complete cfg gates x weights launch.params hp.2.1) hglobal
  intro loc writerA writerB vx vy hx hy
  exact overlapping_writers_equal (canonical_wellFormed cfg gates x weights hp.1 hp.2.1)
    (canonical_complete cfg gates x weights launch.params hp.2.1) hp.1 hp.2.1 hx hy

theorem checked_sites : Scalar.uniqueBarrierSites code = true := by decide

theorem checked_correct (cfg : Config) (gates x : Moe.Matrix) (weights : Moe.Weights) (domain : List Location)
    (hcover : CoversOutput cfg gates domain) :
    Scalar.CheckedTriple code (Pre cfg gates x weights) (fun _ => domain)
      (fun launch output => Moe.Experts gates x weights cfg.input.m cfg.input.n cfg.input.k cfg.input.h output ∧
        ∀ loc ∈ domain, ¬ SelectedByte cfg gates loc → output loc = launch.initial loc) :=
  Scalar.triple_checked (correct cfg gates x weights domain hcover)

theorem checked_nonvacuous (cfg : Config) (gates x : Moe.Matrix) (weights : Moe.Weights) (domain : List Location)
    (hglobal : ∀ loc ∈ domain, loc.space = .global) :
    Scalar.CheckedNonvacuous code (Pre cfg gates x weights) (fun _ => domain) :=
  Scalar.nonvacuous_checked_of_unique_sites checked_sites (nonvacuous cfg gates x weights domain hglobal)

end
end Ptx.MoeExpertsEvent
