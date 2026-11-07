import Ptx.Kernels.MoeRouteMemory

/-! Universal current-model routing output/frame contract. Actual gate replies
are derived from represented immutable initial memory. Nonvacuity is separate. -/
namespace Ptx.MoeRouteEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeRouteThread
noncomputable section

theorem active_read {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) {gate : Nat} (hgate : gate < 2) :
    execution.eventAt ⟨t.id,gate⟩ = some
      (.read (gLoc cfg (index cfg t.id) gate) (Symbolic.encode .f32 (replyReal t.oracle gate))) := by
  rw [eventAt_of_trace hw.2.1 ht rfl,(active_trace hw hd hg hp ht ha).2]
  rcases (show gate = 0 ∨ gate = 1 by omega) with rfl | rfl <;> rfl

theorem active_write {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) :
    execution.eventAt ⟨t.id,2⟩ = some (.write (rLoc cfg (index cfg t.id)) (u32Bytes (answer t.oracle))) := by
  rw [eventAt_of_trace hw.2.1 ht rfl,(active_trace hw hd hg hp ht ha).2]
  rfl

theorem gate_read_value {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    {rf : ReadsFrom} {co : Coherence} {gates : Moe.Matrix}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg gates launch.initial) (hc : GenericMemoryConditions execution launch.initial rf co)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) {gate : Nat} (hgate : gate < 2) :
    replyReal t.oracle gate = gates (index cfg t.id) gate := by
  apply immutable_real_load hc.agreement (active_read hw hd hg hp ht ha hgate)
  · exact race_free_eligible (no_races hw hd hg hp rf) _ _
  · exact input_unwritten hw hd hg hp (word_base_in_region (gate_index_bound cfg ha hgate))
  · exact hi _ _ ha hgate

theorem answer_correct {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    {rf : ReadsFrom} {co : Coherence} {gates : Moe.Matrix}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg gates launch.initial) (hc : GenericMemoryConditions execution launch.initial rf co)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) :
    answer t.oracle = Moe.selected gates (index cfg t.id) := by
  unfold answer
  rw [gate_read_value hw hd hg hp hi hc ht ha (show (1 : Nat) < 2 by decide),
    gate_read_value hw hd hg hp hi hc ht ha (show (0 : Nat) < 2 by decide)]
  rfl

def CoversOutput (cfg : Config) (domain : List Location) : Prop :=
  ∀ row, row < cfg.input.m → ∀ offset, offset < 4 → (rLoc cfg row).add offset ∈ domain

theorem active_output {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    {rf : ReadsFrom} {co : Coherence} {gates : Moe.Matrix} {o : Scalar.Observation}
    (hw : Scalar.WellFormed code launch execution) (hg : launch.geometry = cfg.geometry)
    (hp : Params cfg.input launch.params) (hi : Initialized cfg gates launch.initial)
    (hc : GenericMemoryConditions execution launch.initial rf co)
    (ho : ObserverConditions execution launch.initial rf co o)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id)
    (hdom : ∀ offset, offset < 4 → (rLoc cfg (index cfg t.id)).add offset ∈ o.domain) :
    RepresentsU32 o.output (rLoc cfg (index cfg t.id)) (Moe.selected gates (index cfg t.id)) := by
  have hstore := active_write hw ho.complete hg hp ht ha
  rw [answer_correct hw ho.complete hg hp hi hc ht ha] at hstore
  apply observe_u32_write hc ho hstore hdom
  · intro offset _
    exact race_free_observer_eligible (no_races hw ho.complete hg hp rf) _
  · intro offset hb writer value hwrite
    have hbyte : execution.writeByte ⟨t.id,2⟩ ((rLoc cfg (index cfg t.id)).add offset) =
        some (u32Byte (Moe.selected gates (index cfg t.id)) offset) := by
      simpa only [Candidate.writeByte,hstore,Option.bind_some,Kind.writeByte] using
        u32_payload_byte (rLoc cfg (index cfg t.id)) _ offset hb
    exact overlapping_writers_equal hw ho.complete hg hp hwrite hbyte

theorem routes_output {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    {rf : ReadsFrom} {co : Coherence} {gates : Moe.Matrix} {o : Scalar.Observation}
    (hw : Scalar.WellFormed code launch execution) (hg : launch.geometry = cfg.geometry)
    (hp : Params cfg.input launch.params) (hi : Initialized cfg gates launch.initial)
    (hc : GenericMemoryConditions execution launch.initial rf co)
    (ho : ObserverConditions execution launch.initial rf co o) (hdom : CoversOutput cfg o.domain) :
    Moe.Routes gates cfg.input.m cfg.input.r o.output := by
  intro row hr
  obtain ⟨id,hvalid,hindex⟩ := index_covered cfg hr
  have hlaunch : id.Valid launch.geometry := by simpa only [hg] using hvalid
  obtain ⟨t,ht,htid⟩ := hw.2.2.2 id hlaunch
  have hti : index cfg t.id = row := by rw [htid]; exact hindex
  have ha : Active cfg t.id := by change index cfg t.id < cfg.input.m; rw [hti]; exact hr
  have hresult := active_output hw hg hp hi hc ho ht ha (fun offset hb => by
    rw [hti]; exact hdom row hr offset hb)
  simpa only [hti,rLoc] using hresult

theorem frame {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    {rf : ReadsFrom} {co : Coherence} {o : Scalar.Observation}
    (hw : Scalar.WellFormed code launch execution) (hg : launch.geometry = cfg.geometry)
    (hp : Params cfg.input launch.params) (ho : ObserverConditions execution launch.initial rf co o)
    {loc : Location} (hm : loc ∈ o.domain) (hout : ¬ InWords cfg.input.r cfg.input.m loc) :
    o.output loc = launch.initial loc :=
  observer_unwritten ho hm (race_free_observer_eligible (no_races hw ho.complete hg hp rf) loc)
    (outside_unwritten hw ho.complete hg hp hout)

theorem correct (cfg : Config) (gates : Moe.Matrix) (domain : List Location) (hcover : CoversOutput cfg domain) :
    Scalar.Triple code (Pre cfg gates) (fun _ => domain)
      (fun launch output => Moe.Routes gates cfg.input.m cfg.input.r output ∧
        ∀ loc ∈ domain, ¬ InWords cfg.input.r cfg.input.m loc → output loc = launch.initial loc) := by
  intro launch execution rf co o hp hw hc ho hd
  constructor
  · apply routes_output hw hp.1 hp.2.1 hp.2.2 hc ho
    simpa only [hd] using hcover
  · intro loc hm hout
    exact frame hw hp.1 hp.2.1 ho (by simpa only [hd] using hm) hout

end
end Ptx.MoeRouteEvent
