import Ptx.Kernels.AmpereTiledWitnessAccesses
import Ptx.MemoryGraph.RankedWitness

/-! Independent rf/co admission for the input-determined tiled source family.
All agreement, ordering, race and from-read obligations are discharged on the
actual graph. Neither memory consistency nor desired output is a premise. -/
namespace Ptx.AmpereTiledWitnessMemory
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledGraph
open Ptx.AmpereTiledWitnessOracle Ptx.AmpereTiledWitnessAccesses Ptx.AmpereTiledProducer
noncomputable section

def rf : Ampere.ReadsFrom := fun node _ => match node with
  | .thread event =>
    if h : 7 ≤ event.serial%17 ∧ event.serial%17 < 13 then
      let reg : Fin 6 := ⟨event.serial%17-7,by omega⟩
      some (.copyWrite ⟨producer event.thread reg,3*(event.serial/17)+(part reg).val⟩)
    else none
  | _ => none
def co (cfg : Config) (launch : Scalar.Launch) (a b : Matrix) : Ampere.Coherence :=
  MemoryGraph.RankedCo (execution cfg launch a b).memoryGraph launch.initial AmpereTiledControl.rank

theorem rf_read (id : ThreadId) (phase : Nat) (reg : Fin 6) (loc : Location) :
    rf (.thread ⟨id,17*phase+7+reg.val⟩) loc = some (.copyWrite ⟨producer id reg,3*phase+(part reg).val⟩) := by
  have hi := reg.isLt
  have hd : (17*phase+7+reg.val)/17 = phase := by omega
  have hm : (17*phase+7+reg.val)%17 = 7+reg.val := by omega
  simp only [rf,hm,hd]
  rw [dite_eq_left (by omega)]
  simp

theorem base_lt {cfg launch candidate} (h : SourceInfo cfg launch candidate) {a b : Node}
    (hb : BaseOrder candidate a b) : AmpereTiledControl.rank a < AmpereTiledControl.rank b :=
  hb.rank_lt AmpereTiledControl.rank (AmpereTiledControl.base_rank h)

theorem write_rank_injective {cfg launch a b loc x y vx vy} (hp : Pre cfg a b launch) (ha : Active cfg)
    (hx : (execution cfg launch a b).writeByte x loc = some vx)
    (hy : (execution cfg launch a b).writeByte y loc = some vy)
    (he : AmpereTiledControl.rank x = AmpereTiledControl.rank y) : x = y := by
  rcases AmpereTiledRace.byte_conflicts_ordered (b := y) (source hp ha) hx (.inr (by simp [hy])) with hid | hf | hb
  · exact hid
  · have hh := base_lt (source hp ha) hf; omega
  · have hh := base_lt (source hp ha) hb; omega

theorem agreement {cfg launch a b node loc value} (hp : Pre cfg a b launch) (ha : Active cfg)
    (hr : (execution cfg launch a b).readByte node loc = some value) :
    MemoryGraph.sourceByte (execution cfg launch a b).memoryGraph launch.initial loc (rf node loc) = some value := by
  rcases AmpereTiledWitnessAccesses.read_cases hp ha hr with ⟨id,hv,phase,hphase,reg,hn,hpayload⟩ | ⟨operation,op,hn,hcopy,hpayload⟩
  · rw [hn,rf_read]
    exact shared_source_write hp ha hv hphase reg hpayload
  · rw [hn]
    change some (launch.initial loc) = some value
    exact congrArg some (copy_read_initial hp ha hcopy hpayload).symm

theorem read_from_lt {cfg launch a b read writer loc vr vw} (hp : Pre cfg a b launch) (ha : Active cfg)
    (hr : (execution cfg launch a b).readByte read loc = some vr)
    (_hw : (execution cfg launch a b).writeByte writer loc = some vw)
    (hs : rf read loc = some writer) : AmpereTiledControl.rank writer < AmpereTiledControl.rank read := by
  rcases AmpereTiledWitnessAccesses.read_cases hp ha hr with ⟨id,_,phase,_,reg,hn,_⟩ | ⟨operation,op,hn,_,_⟩
  · rw [hn,rf_read] at hs
    have hid := (Option.some.inj hs).symm
    rw [hid,hn,AmpereTiledControl.write_rank]
    simp only [AmpereTiledControl.rank]
    have hi := (part reg).isLt
    omega
  · rw [hn] at hs
    cases hs

theorem causal_lt {cfg launch a b x y} (hp : Pre cfg a b launch) (ha : Active cfg)
    (hc : MemoryGraph.Causality (execution cfg launch a b).memoryGraph rf x y) :
    AmpereTiledControl.rank x < AmpereTiledControl.rank y := by
  have ho : ∀ x y, MemoryGraph.ObservationOrder (execution cfg launch a b).memoryGraph rf x y →
      AmpereTiledControl.rank x < AmpereTiledControl.rank y := by
    intro x y hobs
    induction hobs with
    | direct h =>
      obtain ⟨_,loc,vr,hr,hs,hw⟩ := h
      obtain ⟨vw,hv⟩ := Option.isSome_iff_exists.mp hw
      exact read_from_lt hp ha hr hv hs
    | viaRMW _ _ _ ih₁ ih₂ => exact Nat.lt_trans ih₁ ih₂
  rcases hc with ⟨_,hb⟩ | ⟨middle,hobs,_,hb⟩
  · exact base_lt (source hp ha) hb
  · exact Nat.lt_trans (ho _ _ hobs) (base_lt (source hp ha) hb)

theorem from_read_lt {cfg launch a b read writer loc vr vw} (hp : Pre cfg a b launch) (ha : Active cfg)
    (_hne : read ≠ writer) (hr : (execution cfg launch a b).readByte read loc = some vr)
    (hw : (execution cfg launch a b).writeByte writer loc = some vw)
    (hc : co cfg launch a b loc (rf read loc) (some writer)) :
    AmpereTiledControl.rank read < AmpereTiledControl.rank writer := by
  rcases AmpereTiledWitnessAccesses.read_cases hp ha hr with ⟨id,hv,phase,hphase,reg,hn,hpayload⟩ | ⟨operation,op,hn,hcopy,hpayload⟩
  · subst read
    have hv' : (context launch id).id.Valid (geometry cfg) := by simpa only [context,hp.2.2.1] using hv
    have hproducer : (producer id reg).Valid launch.geometry := by simpa only [hp.2.2.1,context] using producer_valid hv' reg
    have hcurrent := shared_source_write hp ha hv hphase reg hpayload
    have hs : loc.space = .shared id.cta := (Ptx.Event.payloadByte_bounds hpayload).1.symm
    have hco : AmpereTiledControl.rank (.copyWrite ⟨producer id reg,3*phase+(part reg).val⟩) < AmpereTiledControl.rank writer := by
      rw [rf_read] at hc
      exact MemoryGraph.ranked_co_write_lt hc
    rcases AmpereTiledPhaseVisibility.writer_classification (rf := rf) (source hp ha) hproducer hv rfl hphase (part reg) reg hs hcurrent hr writer vw hw with hid | hbefore | hafter
    · rw [hid] at hco; omega
    · have hh := causal_lt hp ha hbefore; omega
    · exact causal_lt hp ha hafter
  · subst read
    have hs : loc.space = .global := (Ptx.Event.payloadByte_bounds hpayload).1.symm.trans (AmpereTiledMemory.copy_source_global (source hp ha) hcopy)
    have hn := AmpereTiledGlobalAccesses.global_read_unwritten (source hp ha) hs hr writer
    rw [hw] at hn
    cases hn

theorem memory {cfg launch a b} (hp : Pre cfg a b launch) (ha : Active cfg) :
    MemoryConstraints (execution cfg launch a b) launch.initial rf (co cfg launch a b) := by
  apply MemoryGraph.ranked_co_conditions AmpereTiledControl.rank
  · intro x y hpo
    change ProgramOrder (execution cfg launch a b) x y at hpo
    cases x <;> cases y <;> try exact False.elim hpo
    exact Nat.mul_lt_mul_of_pos_left hpo.2.2.2 (by decide)
  · intro x y hb
    exact base_lt (source hp ha) hb
  · exact AmpereTiledRace.race_free (source hp ha) rf
  · intro loc x y vx vy hx hy he
    exact write_rank_injective hp ha hx hy he
  · intro read loc value hr
    exact agreement hp ha hr
  · intro read writer loc vr vw hr hw hs
    exact read_from_lt hp ha hr hw hs
  · intro read writer loc vr vw hne hr hw hc
    exact from_read_lt hp ha hne hr hw hc

end
end Ptx.AmpereTiledWitnessMemory
