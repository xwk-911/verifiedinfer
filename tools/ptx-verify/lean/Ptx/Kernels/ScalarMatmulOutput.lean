import Ptx.Kernels.ScalarMatmulInputs

/-! Universal, model-relative matrix output and frame contract. This quantifies
over every complete provenance-checked candidate, reads-from/coherence witness
and synchronized observation. Existence of such an execution is a separate duty.
-/
namespace Ptx.ScalarMatmulEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.ScalarMatmul
noncomputable section

def CoversOutput (cfg : Config) (domain : List Location) : Prop :=
  ∀ r c, r < cfg.input.m → c < cfg.input.n → ∀ offset, offset < 4 → (cLoc cfg r c).add offset ∈ domain

theorem active_output {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    {rf : ReadsFrom} {co : Coherence} {a b : Matrix} {o : Scalar.Observation}
    (hw : Scalar.WellFormed code launch execution) (hg : launch.geometry = cfg.geometry)
    (hp : Params cfg.input launch.params) (hi : Initialized cfg a b launch.initial)
    (hc : GenericMemoryConditions execution launch.initial rf co)
    (ho : ObserverConditions execution launch.initial rf co o)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id)
    (hdom : ∀ offset, offset < 4 → (cLoc cfg (row cfg.geometry.block t.id) (col cfg.geometry.block t.id)).add offset ∈ o.domain) :
    RepresentsReal .f32 o.output (cLoc cfg (row cfg.geometry.block t.id) (col cfg.geometry.block t.id))
      (prefixProduct a b (row cfg.geometry.block t.id) (col cfg.geometry.block t.id) cfg.input.k) := by
  have hstore := active_write hw ho.complete hg hp ht ha
  rw [answer_correct hw ho.complete hg hp hi hc ht ha] at hstore
  apply observe_real_write hc ho hstore hdom
  · intro offset _
    exact race_free_observer_eligible (no_races hw ho.complete hg hp rf) _
  · intro offset hb writer value hwrite
    have hbyte : execution.writeByte ⟨t.id,2*cfg.input.k⟩
        ((cLoc cfg (row cfg.geometry.block t.id) (col cfg.geometry.block t.id)).add offset) =
          some (.realPart .f32 (prefixProduct a b (row cfg.geometry.block t.id) (col cfg.geometry.block t.id) cfg.input.k) offset) := by
      simpa only [Candidate.writeByte,hstore,Option.bind_some,Kind.writeByte] using
        encoded_byte .f32 _ (cLoc cfg (row cfg.geometry.block t.id) (col cfg.geometry.block t.id)) hb
    exact overlapping_writers_equal hw ho.complete hg hp hwrite hbyte

theorem matrix_output {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    {rf : ReadsFrom} {co : Coherence} {a b : Matrix} {o : Scalar.Observation}
    (hw : Scalar.WellFormed code launch execution) (hg : launch.geometry = cfg.geometry)
    (hp : Params cfg.input launch.params) (hi : Initialized cfg a b launch.initial)
    (hc : GenericMemoryConditions execution launch.initial rf co)
    (ho : ObserverConditions execution launch.initial rf co o) (hdom : CoversOutput cfg o.domain) :
    Post a b cfg.input.m cfg.input.n cfg.input.k cfg.input.c o.output := by
  intro r c hr hcol
  obtain ⟨id,hvalid,hrow,hcindex⟩ := output_covered cfg.valid cfg.coversRows cfg.coversCols hr hcol
  have hlaunch : id.Valid launch.geometry := by simpa only [hg] using hvalid
  obtain ⟨t,ht,htid⟩ := hw.2.2.2 id hlaunch
  have htr : row cfg.geometry.block t.id = r := by rw [htid]; exact hrow
  have htc : col cfg.geometry.block t.id = c := by rw [htid]; exact hcindex
  have ha : Active cfg t.id := ⟨by rw [htr]; exact hr,by rw [htc]; exact hcol⟩
  have hresult := active_output hw hg hp hi hc ho ht ha (fun offset hb => by
    rw [htr,htc]
    exact hdom r c hr hcol offset hb)
  simpa only [htr,htc,cLoc] using hresult

theorem frame {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    {rf : ReadsFrom} {co : Coherence} {o : Scalar.Observation}
    (hw : Scalar.WellFormed code launch execution) (hg : launch.geometry = cfg.geometry)
    (hp : Params cfg.input launch.params) (ho : ObserverConditions execution launch.initial rf co o)
    {loc : Location} (hm : loc ∈ o.domain) (hout : ¬ InWords cfg.input.c (cfg.input.m*cfg.input.n) loc) :
    o.output loc = launch.initial loc :=
  observer_unwritten ho hm (race_free_observer_eligible (no_races hw ho.complete hg hp rf) loc)
    (outside_unwritten hw ho.complete hg hp hout)

theorem correct (cfg : Config) (a b : Matrix) (domain : List Location) (hcover : CoversOutput cfg domain) :
    Scalar.Triple code (Pre cfg a b) (fun _ => domain)
      (fun launch output => Post a b cfg.input.m cfg.input.n cfg.input.k cfg.input.c output ∧
        ∀ loc ∈ domain, ¬ InWords cfg.input.c (cfg.input.m*cfg.input.n) loc → output loc = launch.initial loc) := by
  intro launch execution rf co o hp hw hc ho hd
  constructor
  · apply matrix_output hw hp.1 hp.2.1 hp.2.2 hc ho
    simpa only [hd] using hcover
  · intro loc hm hout
    exact frame hw hp.1 hp.2.1 ho (by simpa only [hd] using hm) hout

end
end Ptx.ScalarMatmulEvent
