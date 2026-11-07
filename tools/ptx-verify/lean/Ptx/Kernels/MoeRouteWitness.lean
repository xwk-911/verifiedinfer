import Ptx.Kernels.MoeRouteCandidate
import Ptx.Scalar.Checked

/-! Legal complete memory and observation witnesses, independently of the
universal output theorem. Source-aware admission uses the actual mixed source. -/
namespace Ptx.MoeRouteEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeRouteThread
noncomputable section

theorem no_barrier_returns {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (event : EventId) (bid generation : Nat) : execution.eventAt event ≠ some (.barrierReturn bid generation) := by
  intro he
  obtain ⟨_,_,_,hs⟩ := event_shape hw hd hg hp he
  rcases hs with ⟨_,hk⟩ | ⟨_,hk⟩ | ⟨_,hk⟩ <;> cases hk

theorem canonical_gate_event (cfg : Config) (gates : Moe.Matrix) {launch : Scalar.Launch}
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {id : ThreadId} (hv : id.Valid cfg.geometry) (ha : Active cfg id) {gate : Nat} (hgate : gate < 2) :
    (canonical cfg gates launch.params hp).eventAt ⟨id,gate⟩ =
      some (.read (gLoc cfg (index cfg id) gate) (Symbolic.encode .f32 (gates (index cfg id) gate))) := by
  have ht := canonical_member cfg gates launch.params hp hv
  have h := active_read (canonical_wellFormed cfg gates hg hp) (canonical_complete cfg gates launch.params hp)
    hg hp ht (by simpa using ha) hgate
  simpa only [canonical_trace_id,canonical_trace_oracle,gateOracle,replyReal] using h

theorem canonical_read_value (cfg : Config) (gates : Moe.Matrix) {launch : Scalar.Launch}
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg gates launch.initial)
    {read : EventId} {loc : Location} {value : Symbolic.Byte}
    (hr : (canonical cfg gates launch.params hp).readByte read loc = some value) : launch.initial loc = value := by
  let execution := canonical cfg gates launch.params hp
  have hw := canonical_wellFormed cfg gates hg hp
  have hd := canonical_complete cfg gates launch.params hp
  change execution.readByte read loc = some value at hr
  cases he : execution.eventAt read with
  | none => simp [Candidate.readByte,he] at hr
  | some kind =>
    obtain ⟨oracle,hv,ha,hcases⟩ := event_shape hw hd hg hp he
    have hgate : read.serial < 2 := by
      rcases hcases with ⟨hs,_⟩ | ⟨hs,_⟩ | ⟨_,rfl⟩
      · omega
      · omega
      · simp [Candidate.readByte,he,Kind.readByte] at hr
    have hev := canonical_gate_event cfg gates hg hp hv ha hgate
    have hid : read = ⟨read.thread,read.serial⟩ := rfl
    rw [← hid] at hev
    change execution.eventAt read = _ at hev
    have hb : payloadByte (gLoc cfg (index cfg read.thread) read.serial)
        (Symbolic.encode .f32 (gates (index cfg read.thread) read.serial)) loc = some value := by
      simpa only [Candidate.readByte,hev,Option.bind_some,Kind.readByte] using hr
    exact represented_payload (hi _ _ ha hgate) hb

theorem canonical_memory (cfg : Config) (gates : Moe.Matrix) {launch : Scalar.Launch}
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg gates launch.initial) :
    GenericMemoryConditions (canonical cfg gates launch.params hp) launch.initial
      (fun _ _ => .initial) (InitialCo (canonical cfg gates launch.params hp)) := by
  have hw := canonical_wellFormed cfg gates hg hp
  have hd := canonical_complete cfg gates launch.params hp
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
    exact congrArg some (canonical_read_value cfg gates hg hp hi hr)
  · intro _ _ _ _ _ _ _ he
    cases he
  · intro read writer loc vr vw hr hwrite _
    have hu := input_unwritten hw hd hg hp (read_region hw hd hg hp hr) writer
    rw [hu] at hwrite
    cases hwrite

theorem nonvacuous (cfg : Config) (gates : Moe.Matrix) (domain : List Location)
    (hglobal : ∀ loc ∈ domain, loc.space = .global) :
    Scalar.Nonvacuous code (Pre cfg gates) (fun _ => domain) := by
  intro launch hp
  let execution := canonical cfg gates launch.params hp.2.1
  refine ⟨execution,(fun _ _ => .initial),InitialCo execution,
    selectedObservation execution launch.initial (writerSelector execution) domain,
    canonical_wellFormed cfg gates hp.1 hp.2.1,
    canonical_memory cfg gates hp.1 hp.2.1 hp.2.2,?_,rfl⟩
  apply unique_writers_observation (canonical_complete cfg gates launch.params hp.2.1) hglobal
  intro loc x y vx vy hx hy
  exact overlapping_writers_equal (canonical_wellFormed cfg gates hp.1 hp.2.1)
    (canonical_complete cfg gates launch.params hp.2.1) hp.1 hp.2.1 hx hy

theorem checked_sites : Scalar.uniqueBarrierSites code = true := by decide
theorem checked_correct (cfg : Config) (gates : Moe.Matrix) (domain : List Location) (hcover : CoversOutput cfg domain) :
    Scalar.CheckedTriple code (Pre cfg gates) (fun _ => domain)
      (fun launch output => Moe.Routes gates cfg.input.m cfg.input.r output ∧
        ∀ loc ∈ domain, ¬ InWords cfg.input.r cfg.input.m loc → output loc = launch.initial loc) :=
  Scalar.triple_checked (correct cfg gates domain hcover)
theorem checked_nonvacuous (cfg : Config) (gates : Moe.Matrix) (domain : List Location)
    (hglobal : ∀ loc ∈ domain, loc.space = .global) :
    Scalar.CheckedNonvacuous code (Pre cfg gates) (fun _ => domain) :=
  Scalar.nonvacuous_checked_of_unique_sites checked_sites (nonvacuous cfg gates domain hglobal)

end
end Ptx.MoeRouteEvent
