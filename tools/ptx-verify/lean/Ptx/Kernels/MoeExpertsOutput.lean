import Ptx.Kernels.MoeExpertsInputs
import Ptx.Event.Publication

/-! Universal expert output, including byte preservation in unselected expert
planes. The route and the numerical result are derived from memory agreement.
Complete consistent executions are constructed separately. -/
namespace Ptx.MoeExpertsEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeExperts Ptx.MoeExpertsLoop
noncomputable section

def CoversOutput (cfg : Config) (gates : Moe.Matrix) (domain : List Location) : Prop :=
  ∀ r c, r < cfg.input.m → c < cfg.input.n → ∀ offset, offset < 4 →
    (hLoc cfg (Moe.selected gates r) r c).add offset ∈ domain

def SelectedByte (cfg : Config) (gates : Moe.Matrix) (loc : Location) : Prop :=
  ∃ r c offset, r < cfg.input.m ∧ c < cfg.input.n ∧ offset < 4 ∧
    loc = (hLoc cfg (Moe.selected gates r) r c).add offset

theorem unselected_byte (cfg : Config) (gates : Moe.Matrix) {e r c offset : Nat}
    (hr : r < cfg.input.m) (hc : c < cfg.input.n) (ho : offset < 4) (he : e ≠ Moe.selected gates r) :
    ¬ SelectedByte cfg gates ((hLoc cfg e r c).add offset) := by
  rintro ⟨s,d,other,hs,hd,hother,hloc⟩
  have haddr := congrArg Location.address hloc
  simp only [hLoc,Location.add] at haddr
  have hindex : (e*cfg.input.m+r)*cfg.input.n+c = (Moe.selected gates s*cfg.input.m+s)*cfg.input.n+d := by omega
  obtain ⟨hex,hrs,_⟩ := Moe.expert_index_injective hr hs hc hd hindex
  exact he (by simpa only [hrs] using hex)

theorem active_output {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    {rf : ReadsFrom} {co : Coherence} {gates x : Moe.Matrix} {weights : Moe.Weights} {o : Scalar.Observation}
    (hw : Scalar.WellFormed code launch execution) (hg : launch.geometry = cfg.geometry)
    (hp : Params cfg.input launch.params) (hi : Initialized cfg gates x weights launch.initial)
    (hc : GenericMemoryConditions execution launch.initial rf co)
    (ho : ObserverConditions execution launch.initial rf co o)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id)
    (hdom : ∀ offset, offset < 4 →
      (hLoc cfg (Moe.selected gates (row cfg.geometry.block t.id)) (row cfg.geometry.block t.id) (col cfg.geometry.block t.id)).add offset ∈ o.domain) :
    RepresentsReal .f32 o.output
      (hLoc cfg (Moe.selected gates (row cfg.geometry.block t.id)) (row cfg.geometry.block t.id) (col cfg.geometry.block t.id))
      (Moe.output gates x weights (row cfg.geometry.block t.id) (col cfg.geometry.block t.id) cfg.input.k) := by
  have hstore := active_write hw ho.complete hg hp ht ha (expert_valid hw ho.complete hg hp hi hc ht ha)
  rw [expert_correct hw ho.complete hg hp hi hc ht ha,answer_correct hw ho.complete hg hp hi hc ht ha] at hstore
  apply observe_real_write hc ho hstore hdom
  · intro offset _
    exact race_free_observer_eligible (no_races hw ho.complete hg hp rf) _
  · intro offset hb writer value hwrite
    have hbyte : execution.writeByte ⟨t.id,1+2*cfg.input.k⟩
        ((hLoc cfg (Moe.selected gates (row cfg.geometry.block t.id)) (row cfg.geometry.block t.id) (col cfg.geometry.block t.id)).add offset) =
          some (.realPart .f32 (Moe.output gates x weights (row cfg.geometry.block t.id) (col cfg.geometry.block t.id) cfg.input.k) offset) := by
      simpa only [Candidate.writeByte,hstore,Option.bind_some,Kind.writeByte] using encoded_byte .f32 _ _ hb
    exact overlapping_writers_equal hw ho.complete hg hp hwrite hbyte

theorem experts_output {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    {rf : ReadsFrom} {co : Coherence} {gates x : Moe.Matrix} {weights : Moe.Weights} {o : Scalar.Observation}
    (hw : Scalar.WellFormed code launch execution) (hg : launch.geometry = cfg.geometry)
    (hp : Params cfg.input launch.params) (hi : Initialized cfg gates x weights launch.initial)
    (hc : GenericMemoryConditions execution launch.initial rf co)
    (ho : ObserverConditions execution launch.initial rf co o) (hdom : CoversOutput cfg gates o.domain) :
    Moe.Experts gates x weights cfg.input.m cfg.input.n cfg.input.k cfg.input.h o.output := by
  intro r c hr hcol
  obtain ⟨id,hvalid,hrow,hcindex⟩ := ScalarMatmul.output_covered cfg.valid cfg.coversRows cfg.coversCols hr hcol
  have hlaunch : id.Valid launch.geometry := by simpa only [hg] using hvalid
  obtain ⟨t,ht,htid⟩ := hw.2.2.2 id hlaunch
  have htr : row cfg.geometry.block t.id = r := by rw [htid]; exact hrow
  have htc : col cfg.geometry.block t.id = c := by rw [htid]; exact hcindex
  have ha : Active cfg t.id := ⟨by rw [htr]; exact hr,by rw [htc]; exact hcol⟩
  have hresult := active_output hw hg hp hi hc ho ht ha (fun offset hb => by
    rw [htr,htc]; exact hdom r c hr hcol offset hb)
  simpa only [htr,htc,hLoc] using hresult

theorem write_selected {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    {rf : ReadsFrom} {co : Coherence} {gates x : Moe.Matrix} {weights : Moe.Weights}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg gates x weights launch.initial) (hc : GenericMemoryConditions execution launch.initial rf co)
    {writer : EventId} {loc : Location} {value : Symbolic.Byte} (hwrite : execution.writeByte writer loc = some value) :
    SelectedByte cfg gates loc := by
  obtain ⟨_,ha,hs,_⟩ := write_shape hw hd hg hp hwrite
  cases he : execution.eventAt writer with
  | none => simp [Candidate.writeByte,he] at hwrite
  | some kind =>
    obtain ⟨t,ht,htid,_⟩ := eventAt_trace he
    have hat : Active cfg t.id := by simpa only [htid] using ha
    have hstore := active_write hw hd hg hp ht hat (expert_valid hw hd hg hp hi hc ht hat)
    have hid : writer = ⟨t.id,1+2*cfg.input.k⟩ := by cases writer; simp_all
    rw [← hid,expert_correct hw hd hg hp hi hc ht hat] at hstore
    have hbyte : payloadByte
        (hLoc cfg (Moe.selected gates (row cfg.geometry.block t.id)) (row cfg.geometry.block t.id) (col cfg.geometry.block t.id))
        (Symbolic.encode .f32 (answer cfg t.oracle)) loc = some value := by
      simpa only [Candidate.writeByte,hstore,Option.bind_some,Kind.writeByte] using hwrite
    obtain ⟨offset,hb,hloc⟩ := payload_location hbyte
    exact ⟨_,_,offset,hat.1,hat.2,by simpa only [Symbolic.encode_length,Symbolic.Format.bytes] using hb,hloc⟩

theorem unselected_unwritten {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    {rf : ReadsFrom} {co : Coherence} {gates x : Moe.Matrix} {weights : Moe.Weights}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg gates x weights launch.initial) (hc : GenericMemoryConditions execution launch.initial rf co)
    {loc : Location} (hout : ¬ SelectedByte cfg gates loc) (writer : EventId) : execution.writeByte writer loc = none := by
  cases he : execution.writeByte writer loc with
  | none => rfl
  | some value => exact (hout (write_selected hw hd hg hp hi hc he)).elim

theorem frame {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    {rf : ReadsFrom} {co : Coherence} {gates x : Moe.Matrix} {weights : Moe.Weights} {o : Scalar.Observation}
    (hw : Scalar.WellFormed code launch execution) (hg : launch.geometry = cfg.geometry)
    (hp : Params cfg.input launch.params) (hi : Initialized cfg gates x weights launch.initial)
    (hc : GenericMemoryConditions execution launch.initial rf co)
    (ho : ObserverConditions execution launch.initial rf co o)
    {loc : Location} (hm : loc ∈ o.domain) (hout : ¬ SelectedByte cfg gates loc) :
    o.output loc = launch.initial loc :=
  observer_unwritten ho hm (race_free_observer_eligible (no_races hw ho.complete hg hp rf) loc)
    (unselected_unwritten hw ho.complete hg hp hi hc hout)

theorem correct (cfg : Config) (gates x : Moe.Matrix) (weights : Moe.Weights) (domain : List Location)
    (hcover : CoversOutput cfg gates domain) :
    Scalar.Triple code (Pre cfg gates x weights) (fun _ => domain)
      (fun launch output => Moe.Experts gates x weights cfg.input.m cfg.input.n cfg.input.k cfg.input.h output ∧
        ∀ loc ∈ domain, ¬ SelectedByte cfg gates loc → output loc = launch.initial loc) := by
  intro launch execution rf co o hp hw hc ho hd
  constructor
  · apply experts_output hw hp.1 hp.2.1 hp.2.2 hc ho
    simpa only [hd] using hcover
  · intro loc hm hout
    exact frame hw hp.1 hp.2.1 hp.2.2 hc ho (by simpa only [hd] using hm) hout

end
end Ptx.MoeExpertsEvent
