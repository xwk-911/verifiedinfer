import Ptx.Event.Witnesses

/-! Logical, bytewise global-memory reads after synchronized kernel completion.
API order places every kernel access before these read-only observer events.
For the current weak generic subset, the added memory obligations are source
value agreement for untainted bytes and no coherence-stale source after ANY
kernel write. These are explicit model conditions, not a theorem that arbitrary
maps are observable or that a CUDA synchronization call is implemented correctly.
Allocation/domain coverage and full PTX correspondence remain separate duties.
-/
namespace Ptx.Event
open Ptx.ISA

variable {ByteValue Answers : Type}

structure Observation (ByteValue : Type := Byte) where
  domain : List Location
  output : ByteMap ByteValue
  source : Location → Source

def ObserverEligible (c : Candidate ByteValue Answers) (rf : ReadsFrom) (loc : Location) : Prop :=
  ¬ MixedSizeRace c rf ∧
  ¬ ∃ a b, (c.writeByte a loc).isSome = true ∧ (c.writeByte b loc).isSome = true ∧ DataRace c rf a b

structure ObserverConditions (c : Candidate ByteValue Answers) (initial : ByteMap ByteValue) (rf : ReadsFrom)
    (co : Coherence) (o : Observation ByteValue) : Prop where
  complete : c.Complete
  globalOnly : ∀ loc ∈ o.domain, loc.space = .global
  agreement : ∀ loc ∈ o.domain, ObserverEligible c rf loc →
    sourceByte c initial loc (o.source loc) = some (o.output loc)
  noStale : ∀ loc ∈ o.domain, ¬ MixedSizeRace c rf →
    ∀ writer value, c.writeByte writer loc = some value → ¬ co loc (o.source loc) (.write writer)

theorem race_free_observer_eligible {c : Candidate ByteValue Answers} {rf} (hn : ∀ a b, ¬ DataRace c rf a b) (loc) :
    ObserverEligible c rf loc := by
  constructor
  · rintro ⟨a,b,hr,_⟩; exact hn a b hr
  · rintro ⟨a,b,_,_,hr⟩; exact hn a b hr

theorem observer_unwritten {c : Candidate ByteValue Answers} {initial rf co o loc}
    (ho : ObserverConditions c initial rf co o) (hd : loc ∈ o.domain)
    (he : ObserverEligible c rf loc) (hn : ∀ writer, c.writeByte writer loc = none) :
    o.output loc = initial loc := by
  have hv := ho.agreement loc hd he
  cases hs : o.source loc with
  | initial => exact (Option.some.inj (by simpa [hs, sourceByte] using hv)).symm
  | write writer => simp [hs, sourceByte, hn] at hv

theorem observer_unique_writer {c : Candidate ByteValue Answers} {initial rf co o loc writer value}
    (hc : GenericMemoryConditions c initial rf co)
    (ho : ObserverConditions c initial rf co o) (hd : loc ∈ o.domain)
    (he : ObserverEligible c rf loc) (hw : c.writeByte writer loc = some value)
    (hu : ∀ other v, c.writeByte other loc = some v → other = writer) :
    o.output loc = value := by
  have hv := ho.agreement loc hd he
  cases hs : o.source loc with
  | initial =>
    exact False.elim (ho.noStale loc hd he.1 writer value hw
      (by simpa [hs] using (hc.coherence he.1).initialization loc writer value hw))
  | write other =>
    have hwrite : c.writeByte other loc = some (o.output loc) := by simpa [hs, sourceByte] using hv
    have hi := hu other (o.output loc) hwrite
    subst other
    exact Option.some.inj (hwrite.symm.trans hw)

theorem unique_byte_observer_eligible {c : Candidate ByteValue Answers} {rf loc}
    (hn : ¬ MixedSizeRace c rf)
    (hu : ∀ a b va vb, c.writeByte a loc = some va → c.writeByte b loc = some vb → a = b) :
    ObserverEligible c rf loc := by
  refine ⟨hn,?_⟩
  rintro ⟨a,b,ha,hb,hr⟩
  obtain ⟨va,hva⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨vb,hvb⟩ := Option.isSome_iff_exists.mp hb
  have he := hu a b va vb hva hvb
  subst b
  exact hr.notStrong (write_self_strong hva)

/-- Every alternative writer is either the selected writer or coherence-before
it. This supports repeated modifications, independently of a specific kernel. -/
theorem observer_latest_writer {c : Candidate ByteValue Answers} {initial rf co o loc writer value}
    (hc : GenericMemoryConditions c initial rf co)
    (ho : ObserverConditions c initial rf co o) (hd : loc ∈ o.domain)
    (he : ObserverEligible c rf loc) (hw : c.writeByte writer loc = some value)
    (hl : ∀ other v, c.writeByte other loc = some v → other = writer ∨ co loc (.write other) (.write writer)) :
    o.output loc = value := by
  have hv := ho.agreement loc hd he
  cases hs : o.source loc with
  | initial =>
    exact (ho.noStale loc hd he.1 writer value hw
      (by simpa only [hs] using (hc.coherence he.1).initialization loc writer value hw)).elim
  | write other =>
    have hwrite : c.writeByte other loc = some (o.output loc) := by simpa [hs,sourceByte] using hv
    rcases hl other (o.output loc) hwrite with hi | hbefore
    · subst other
      exact Option.some.inj (hwrite.symm.trans hw)
    · exact (ho.noStale loc hd he.1 writer value hw (by simpa only [hs] using hbefore)).elim

def singleWriterObservation (c : Candidate ByteValue Answers) (initial : ByteMap ByteValue) (writer : EventId)
    (domain : List Location) : Observation ByteValue := {
  domain := domain
  output := fun loc => (c.writeByte writer loc).getD (initial loc)
  source := fun loc => if (c.writeByte writer loc).isSome then .write writer else .initial
}

/-- An observation witness for the InitialCo construction; its values are
computed from the actual emitted write bytes and the fixed initial map. -/
theorem single_writer_observation {c : Candidate ByteValue Answers} {initial rf writer domain}
    (hd : c.Complete) (hg : ∀ loc ∈ domain, loc.space = .global)
    (hu : ∀ other loc value, c.writeByte other loc = some value → other = writer) :
    ObserverConditions c initial rf (InitialCo c) (singleWriterObservation c initial writer domain) := by
  refine ⟨hd, hg, ?_, ?_⟩
  · intro loc _ _
    cases hw : c.writeByte writer loc <;> simp [singleWriterObservation, sourceByte, hw]
  · intro loc _ _ other value hw hco
    have hi := hu other loc value hw
    subst other
    have hs : (singleWriterObservation c initial writer domain).source loc = .write writer := by
      simp [singleWriterObservation, hw]
    have hinit := hco.1
    rw [hs] at hinit
    cases hinit

def selectedObservation (c : Candidate ByteValue Answers) (initial : ByteMap ByteValue) (select : Location → Option EventId)
    (domain : List Location) : Observation ByteValue := {
  domain := domain
  output := fun loc => match select loc with
    | none => initial loc
    | some writer => (c.writeByte writer loc).getD (initial loc)
  source := fun loc => match select loc with
    | none => .initial
    | some writer => if (c.writeByte writer loc).isSome then .write writer else .initial
}

/-- Generalizes the single-writer construction to a different unique writer for
each byte. Coverage is proved from actual writes; a selector cannot hide a write
by choosing initialization or an unrelated event. -/
theorem selected_observation_on_domain {c : Candidate ByteValue Answers} {initial rf select domain}
    (hd : c.Complete) (hg : ∀ loc ∈ domain, loc.space = .global)
    (hcover : ∀ loc ∈ domain, ∀ writer value, c.writeByte writer loc = some value → select loc = some writer) :
    ObserverConditions c initial rf (InitialCo c) (selectedObservation c initial select domain) := by
  refine ⟨hd,hg,?_,?_⟩
  · intro loc _ _
    cases hs : select loc with
    | none => simp [selectedObservation,sourceByte,hs]
    | some writer => cases hw : c.writeByte writer loc <;> simp [selectedObservation,sourceByte,hs,hw]
  · intro loc hmem _ writer value hw hco
    have hs := hcover loc hmem writer value hw
    have hsource : (selectedObservation c initial select domain).source loc = .write writer := by
      simp [selectedObservation,hs,hw]
    have hi := hco.1
    rw [hsource] at hi
    cases hi

theorem selected_observation {c : Candidate ByteValue Answers} {initial rf select domain}
    (hd : c.Complete) (hg : ∀ loc ∈ domain, loc.space = .global)
    (hcover : ∀ loc writer value, c.writeByte writer loc = some value → select loc = some writer) :
    ObserverConditions c initial rf (InitialCo c) (selectedObservation c initial select domain) :=
  selected_observation_on_domain hd hg (fun loc _ => hcover loc)

/-- Choose an actual emitted writer whenever there is one. Uniqueness is a
separate obligation; this selector does not make an arbitrary graph consistent. -/
noncomputable def writerSelector (c : Candidate ByteValue Answers) (loc : Location) : Option EventId := by
  classical
  exact if h : ∃ writer value, c.writeByte writer loc = some value then
    some (Classical.choose h) else none

theorem writer_selector_covers {c : Candidate ByteValue Answers}
    (hu : ∀ loc a b va vb, c.writeByte a loc = some va → c.writeByte b loc = some vb → a = b)
    {loc writer value} (hw : c.writeByte writer loc = some value) : writerSelector c loc = some writer := by
  classical
  have hex : ∃ w v, c.writeByte w loc = some v := ⟨writer,value,hw⟩
  unfold writerSelector
  rw [dite_eq_left hex]
  obtain ⟨v,hv⟩ := Classical.choose_spec hex
  exact congrArg some (hu loc _ writer v value hv hw)

theorem unique_writers_observation {c : Candidate ByteValue Answers} {initial rf domain}
    (hd : c.Complete) (hg : ∀ loc ∈ domain, loc.space = .global)
    (hu : ∀ loc a b va vb, c.writeByte a loc = some va → c.writeByte b loc = some vb → a = b) :
    ObserverConditions c initial rf (InitialCo c) (selectedObservation c initial (writerSelector c) domain) :=
  selected_observation hd hg (fun _ _ _ hw => writer_selector_covers hu hw)

end Ptx.Event
