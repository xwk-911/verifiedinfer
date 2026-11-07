import Ptx.Kernels.AmpereTiledGlobalAccesses
import Ptx.Kernels.AmpereTiledPhaseVisibility

/-! Race freedom of every completed active source candidate, for arbitrary
read-from choices. This derives eligibility; no memory or warp admission is
needed for the ordering argument. -/
namespace Ptx.AmpereTiledRace
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledTrace Ptx.AmpereTiledGraph Ptx.AmpereTiledEvents
open Ptx.AmpereTiledSharedWriters Ptx.AmpereTiledPhaseOrder Ptx.AmpereTiledGlobalAccesses
noncomputable section

theorem write_space {cfg launch candidate node loc value} (h : SourceInfo cfg launch candidate)
    (hw : candidate.writeByte node loc = some value) : loc.space = .global ∨ ∃ cta, loc.space = .shared cta := by
  rcases AmpereTiledGraph.write_cases h hw with ⟨_,_,_,_,_,hp⟩ | ⟨t,ht,r,phase,_,part,_,hp⟩
  · exact .inl (Ptx.Event.payloadByte_bounds hp).1.symm
  · have hv : (context launch t.id).id.Valid (geometry cfg) := by
      simpa only [h.geometry,context] using (h.formed.2.2.1 t ht).1
    have hb := Ptx.Event.payloadByte_bounds hp
    rw [operation_destination (cfg := cfg) (context launch t.id) t.oracle r hv phase part] at hb
    exact .inr ⟨t.id.cta,hb.1.symm⟩

theorem shared_read_info {cfg launch candidate node loc value cta} (h : SourceInfo cfg launch candidate)
    (hs : loc.space = .shared cta) (hr : candidate.readByte node loc = some value) :
    ∃ t ∈ candidate.traces, ∃ phase, phase < cfg.k/16 ∧ ∃ reg : Fin 6,
      node = .thread ⟨t.id,17*phase+7+reg.val⟩ ∧ loc.space = .shared t.id.cta := by
  rcases AmpereTiledGraph.read_cases h hr with ⟨t,ht,_,phase,hphase,reg,hn,hp⟩ | ⟨t,ht,r,phase,hphase,part,_,hp⟩
  · exact ⟨t,ht,phase,hphase,reg,hn,(Ptx.Event.payloadByte_bounds hp).1.symm⟩
  · have hv : (context launch t.id).id.Valid (geometry cfg) := by
      simpa only [h.geometry,context] using (h.formed.2.2.1 t ht).1
    have hb := Ptx.Event.payloadByte_bounds hp
    rw [operation_source h.layout (context launch t.id) t.oracle r hv h.active phase hphase part] at hb
    have he : AddressSpace.global = .shared cta := hb.1.trans hs
    cases he

theorem shared_writes_ordered {cfg launch candidate a b loc va vb cta} (h : SourceInfo cfg launch candidate)
    (hs : loc.space = .shared cta) (hwa : candidate.writeByte a loc = some va)
    (hwb : candidate.writeByte b loc = some vb) : a = b ∨ BaseOrder candidate a b ∨ BaseOrder candidate b a := by
  obtain ⟨ta,hta,_,pa,hpa,ia,hna,hsa,_,_⟩ := shared_write_info h hs hwa
  obtain ⟨tb,htb,_,pb,hpb,ib,hnb,hsb,_,_⟩ := shared_write_info h hs hwb
  have hva := (h.formed.2.2.1 ta hta).1
  have hvb := (h.formed.2.2.1 tb htb).1
  have hcta : ta.id.cta = tb.id.cta := AddressSpace.shared.inj (hsa.symm.trans hsb)
  rcases Nat.lt_trichotomy pa pb with hlt | heq | hgt
  · exact .inr (.inl (hna ▸ hnb ▸ copy_before_later_copy h hva hvb hcta hlt hpb ia ib))
  · subst pb
    exact .inl (phase_unique h hs hwa hwb hna hnb)
  · exact .inr (.inr (hnb ▸ hna ▸ copy_before_later_copy h hvb hva hcta.symm hgt hpa ib ia))

theorem shared_write_read_ordered {cfg launch candidate writer read loc written observed cta}
    (h : SourceInfo cfg launch candidate) (hs : loc.space = .shared cta)
    (hw : candidate.writeByte writer loc = some written) (hr : candidate.readByte read loc = some observed) :
    BaseOrder candidate writer read ∨ BaseOrder candidate read writer := by
  obtain ⟨tw,htw,_,pw,hpw,part,hnw,hsw,_,_⟩ := shared_write_info h hs hw
  obtain ⟨tr,htr,pr,hpr,reg,hnr,hsr⟩ := shared_read_info h hs hr
  have hvw := (h.formed.2.2.1 tw htw).1
  have hvr := (h.formed.2.2.1 tr htr).1
  have hcta : tw.id.cta = tr.id.cta := AddressSpace.shared.inj (hsw.symm.trans hsr)
  rw [hnw,hnr]
  rcases Nat.lt_trichotomy pw pr with hlt | heq | hgt
  · exact .inl (.trans (copy_before_later_copy h hvw hvw rfl hlt hpr part part)
      (copy_before_read h hvw hvr hcta hpr part reg))
  · subst pr
    exact .inl (copy_before_read h hvw hvr hcta hpw part reg)
  · exact .inr (read_before_later_copy h hvr hvw hcta.symm hgt hpw reg part)

theorem byte_conflicts_ordered {cfg launch candidate a b loc value} (h : SourceInfo cfg launch candidate)
    (hw : candidate.writeByte a loc = some value) (hb : candidate.memoryGraph.Accesses b loc) :
    a = b ∨ BaseOrder candidate a b ∨ BaseOrder candidate b a := by
  rcases write_space h hw with hg | ⟨cta,hs⟩
  · rcases hb with hr | hwb
    · obtain ⟨observed,hr⟩ := Option.isSome_iff_exists.mp hr
      have hn := global_read_unwritten h hg hr a
      rw [hw] at hn
      cases hn
    · obtain ⟨written,hwb⟩ := Option.isSome_iff_exists.mp hwb
      exact .inl (global_writer_unique h hg hw hwb)
  · rcases hb with hr | hwb
    · obtain ⟨observed,hr⟩ := Option.isSome_iff_exists.mp hr
      exact .inr (shared_write_read_ordered h hs hw hr)
    · obtain ⟨written,hwb⟩ := Option.isSome_iff_exists.mp hwb
      exact shared_writes_ordered h hs hw hwb

theorem race_with_writer_impossible {cfg launch candidate a b} {rf : Ampere.ReadsFrom}
    (h : SourceInfo cfg launch candidate) (hw : candidate.memoryGraph.Writes a)
    (race : MemoryGraph.DataRace candidate.memoryGraph rf a b) : False := by
  obtain ⟨loc,ha,hb⟩ := race.overlap
  obtain ⟨writeLoc,written,hw⟩ := hw
  have hwa : ∃ value, candidate.writeByte a loc = some value := by
    rcases ha with hr | hw'
    · obtain ⟨observed,hr⟩ := Option.isSome_iff_exists.mp hr
      exact (MemoryGraph.read_write_exclusive (AmpereTiledGraph.no_rmw h a) hr hw).elim
    · exact Option.isSome_iff_exists.mp hw'
  obtain ⟨value,hwa⟩ := hwa
  rcases byte_conflicts_ordered h hwa hb with heq | hf | hback
  · subst b
    exact race.notStrong (MemoryGraph.write_self_strong hwa)
  · exact race.notForward (MemoryGraph.causal_of_base race.overlap hf)
  · exact race.notBackward (MemoryGraph.causal_of_base ⟨loc,hb,ha⟩ hback)

theorem race_free {cfg launch candidate} (h : SourceInfo cfg launch candidate) (rf : Ampere.ReadsFrom) (a b : Node) :
    ¬ MemoryGraph.DataRace candidate.memoryGraph rf a b := by
  intro race
  rcases race.conflict with hw | hw
  · exact race_with_writer_impossible h hw race
  · exact race_with_writer_impossible h hw (MemoryGraph.data_race_symm race)

theorem eligible {cfg launch candidate} (h : SourceInfo cfg launch candidate) (rf : Ampere.ReadsFrom) (node loc) :
    MemoryGraph.Eligible candidate.memoryGraph rf node loc :=
  MemoryGraph.race_free_eligible (race_free h rf) node loc

end
end Ptx.AmpereTiledRace
