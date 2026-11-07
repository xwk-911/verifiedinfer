import Ptx.MemoryGraph.Rules

/-! Synchronized bytewise global observation over all graph nodes. Completion
is supplied by the concrete source adapter, not by an arbitrary output map. -/
namespace Ptx.MemoryGraph
open Ptx.ISA
open Ptx.Event (ByteMap)
variable {Node ByteValue Source : Type} [Sources Node Source]

structure Observation (ByteValue Source : Type) where
  domain : List Location
  output : ByteMap ByteValue
  source : Location → Source
def ObserverEligible (c : Graph Node ByteValue) (rf : ReadsFrom Node Source) (loc : Location) : Prop :=
  ¬ MixedSizeRace c rf ∧
  ¬ ∃ a b, (c.writeByte a loc).isSome = true ∧ (c.writeByte b loc).isSome = true ∧ DataRace c rf a b
structure ObserverConditions (c : Graph Node ByteValue) (initial : ByteMap ByteValue) (rf : ReadsFrom Node Source)
    (co : Coherence Source) (o : Observation ByteValue Source) : Prop where
  complete : c.complete
  globalOnly : ∀ loc ∈ o.domain, loc.space = .global
  agreement : ∀ loc ∈ o.domain, ObserverEligible c rf loc → sourceByte c initial loc (o.source loc) = some (o.output loc)
  noStale : ∀ loc ∈ o.domain, ¬ MixedSizeRace c rf →
    ∀ writer value, c.writeByte writer loc = some value → ¬ co loc (o.source loc) (writeSource writer)

theorem race_free_observer_eligible {c : Graph Node ByteValue} {rf : ReadsFrom Node Source}
    (hn : ∀ a b, ¬ DataRace c rf a b) (loc) : ObserverEligible c rf loc := by
  constructor
  · rintro ⟨a,b,hr,_⟩
    exact hn a b hr
  · rintro ⟨a,b,_,_,hr⟩
    exact hn a b hr
theorem observer_unwritten {c : Graph Node ByteValue} {initial co loc} {rf : ReadsFrom Node Source} {o : Observation ByteValue Source}
    (ho : ObserverConditions c initial rf co o) (hd : loc ∈ o.domain)
    (he : ObserverEligible c rf loc) (hn : ∀ writer, c.writeByte writer loc = none) : o.output loc = initial loc := by
  have hv := ho.agreement loc hd he
  rcases source_cases (o.source loc) with hs | ⟨writer,hs⟩
  · simpa only [hs,sourceByte_initial,Option.some.injEq] using hv.symm
  · simp only [hs,sourceByte_write,hn] at hv
    cases hv
theorem observer_unique_writer {c : Graph Node ByteValue} {initial co loc writer value} {rf : ReadsFrom Node Source} {o : Observation ByteValue Source}
    (hc : MemoryConditions c initial rf co) (ho : ObserverConditions c initial rf co o) (hd : loc ∈ o.domain)
    (he : ObserverEligible c rf loc) (hw : c.writeByte writer loc = some value)
    (hu : ∀ other v, c.writeByte other loc = some v → other = writer) : o.output loc = value := by
  have hv := ho.agreement loc hd he
  rcases source_cases (o.source loc) with hs | ⟨other,hs⟩
  · exact (ho.noStale loc hd he.1 writer value hw
      (by simpa only [hs] using (hc.coherence he.1).initialization loc writer value hw)).elim
  · have hwrite : c.writeByte other loc = some (o.output loc) := by simpa only [hs,sourceByte_write] using hv
    have hi := hu other (o.output loc) hwrite
    subst other
    exact Option.some.inj (hwrite.symm.trans hw)

end Ptx.MemoryGraph
