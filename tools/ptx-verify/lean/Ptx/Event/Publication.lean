import Ptx.Event.Observation

/-! Complete global publication from a finite observer. Its domain must cover
every actual global write. Outside that domain the initial bytes are retained;
the resulting map is proved observable on ANY finite global domain. No arbitrary
unobserved payload is imported into a successor launch. Shared memory is not
published by this construction. -/
namespace Ptx.Event
open Ptx.ISA
variable {ByteValue Answers : Type}

def CoversGlobalWrites (c : Candidate ByteValue Answers) (domain : List Location) : Prop :=
  ∀ writer loc value, loc.space = .global → c.writeByte writer loc = some value → loc ∈ domain

theorem payload_location {base loc : Location} {bytes : List ByteValue} {value : ByteValue}
    (h : payloadByte base bytes loc = some value) : ∃ offset, offset < bytes.length ∧ loc = base.add offset := by
  have hb := payloadByte_bounds h
  let offset := loc.address-base.address
  refine ⟨offset,by dsimp [offset]; omega,?_⟩
  rcases loc with ⟨space,address⟩
  rcases base with ⟨baseSpace,baseAddress⟩
  simp only at hb
  simp only [Location.add,Location.mk.injEq]
  exact ⟨hb.1.symm,by dsimp [offset]; omega⟩

def published (initial : ByteMap ByteValue) (o : Observation ByteValue) (loc : Location) : ByteValue :=
  if loc ∈ o.domain then o.output loc else initial loc

def publication (initial : ByteMap ByteValue) (o : Observation ByteValue) (domain : List Location) : Observation ByteValue := {
  domain := domain
  output := published initial o
  source := fun loc => if loc ∈ o.domain then o.source loc else .initial
}

theorem published_on {initial : ByteMap ByteValue} {o : Observation ByteValue} {loc : Location}
    (hm : loc ∈ o.domain) : published initial o loc = o.output loc := by simp [published,hm]

theorem published_outside {initial : ByteMap ByteValue} {o : Observation ByteValue} {loc : Location}
    (hm : loc ∉ o.domain) : published initial o loc = initial loc := by simp [published,hm]

theorem outside_domain_unwritten {c : Candidate ByteValue Answers} {domain : List Location}
    (hc : CoversGlobalWrites c domain) {loc : Location} (hg : loc.space = .global) (hm : loc ∉ domain)
    (writer : EventId) : c.writeByte writer loc = none := by
  cases he : c.writeByte writer loc with
  | none => rfl
  | some value => exact (hm (hc writer loc value hg he)).elim

theorem publication_observed {c : Candidate ByteValue Answers} {initial rf co o domain}
    (ho : ObserverConditions c initial rf co o) (hc : CoversGlobalWrites c o.domain)
    (hg : ∀ loc ∈ domain, loc.space = .global) :
    ObserverConditions c initial rf co (publication initial o domain) := by
  refine ⟨ho.complete,hg,?_,?_⟩
  · intro loc hm he
    by_cases hd : loc ∈ o.domain
    · simpa only [publication,published,ite_eq_left hd] using ho.agreement loc hd he
    · simp only [publication,published,ite_eq_right hd,sourceByte]
  · intro loc hm he writer value hw
    by_cases hd : loc ∈ o.domain
    · simpa only [publication,ite_eq_left hd] using ho.noStale loc hd he writer value hw
    · exact (hd (hc writer loc value (hg loc hm) hw)).elim

end Ptx.Event
