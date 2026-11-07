import Ptx.MemoryGraph.Witnesses
import Ptx.MemoryGraph.Observation

/-! Independent complete global observation witnesses selected from actual writes.
Selectors must cover every emitted write on the observed domain. -/
namespace Ptx.MemoryGraph
open Ptx.ISA
open Ptx.Event (ByteMap)
variable {Node ByteValue Source : Type} [Sources Node Source]

def selectedObservation (c : Graph Node ByteValue) (initial : ByteMap ByteValue) (select : Location → Option Node)
    (domain : List Location) : Observation ByteValue Source := {
  domain := domain
  output := fun loc => match select loc with
    | none => initial loc
    | some writer => (c.writeByte writer loc).getD (initial loc)
  source := fun loc => match select loc with
    | none => initialSource
    | some writer => if (c.writeByte writer loc).isSome then writeSource writer else initialSource
}

/-- Generalizes the single-writer construction to a different unique writer for
each byte. Coverage is proved from actual writes; a selector cannot hide a write
by choosing initialization or an unrelated event. -/
theorem selected_observation_on_domain {c : Graph Node ByteValue} {initial select domain} {rf : ReadsFrom Node Source}
    (hd : c.complete) (hg : ∀ loc ∈ domain, loc.space = .global)
    (hcover : ∀ loc ∈ domain, ∀ writer value, c.writeByte writer loc = some value → select loc = some writer) :
    ObserverConditions c initial rf (InitialCo c) (selectedObservation c initial select domain) := by
  refine ⟨hd,hg,?_,?_⟩
  · intro loc _ _
    cases hs : select loc with
    | none => simp [selectedObservation,sourceByte_initial,hs]
    | some writer => cases hw : c.writeByte writer loc <;> simp [selectedObservation,sourceByte_initial,sourceByte_write,hs,hw]
  · intro loc hmem _ writer value hw hco
    have hs := hcover loc hmem writer value hw
    have hsource : (selectedObservation (Source := Source) c initial select domain).source loc = writeSource writer := by
      simp [selectedObservation,hs,hw]
    have hi := hco.1
    rw [hsource] at hi
    exact initial_ne_write writer hi.symm

theorem selected_observation {c : Graph Node ByteValue} {initial select domain} {rf : ReadsFrom Node Source}
    (hd : c.complete) (hg : ∀ loc ∈ domain, loc.space = .global)
    (hcover : ∀ loc writer value, c.writeByte writer loc = some value → select loc = some writer) :
    ObserverConditions c initial rf (InitialCo c) (selectedObservation c initial select domain) :=
  selected_observation_on_domain hd hg (fun loc _ => hcover loc)

/-- Choose an actual emitted writer whenever there is one. Uniqueness is a
separate obligation; this selector does not make an arbitrary graph consistent. -/
noncomputable def writerSelector (c : Graph Node ByteValue) (loc : Location) : Option Node := by
  classical
  exact if h : ∃ writer value, c.writeByte writer loc = some value then
    some (Classical.choose h) else none

theorem writer_selector_covers {c : Graph Node ByteValue}
    (hu : ∀ loc a b va vb, c.writeByte a loc = some va → c.writeByte b loc = some vb → a = b)
    {loc writer value} (hw : c.writeByte writer loc = some value) : writerSelector c loc = some writer := by
  classical
  have hex : ∃ w v, c.writeByte w loc = some v := ⟨writer,value,hw⟩
  unfold writerSelector
  rw [dite_eq_left hex]
  obtain ⟨v,hv⟩ := Classical.choose_spec hex
  exact congrArg some (hu loc _ writer v value hv hw)

theorem unique_writers_observation {c : Graph Node ByteValue} {initial domain} {rf : ReadsFrom Node Source}
    (hd : c.complete) (hg : ∀ loc ∈ domain, loc.space = .global)
    (hu : ∀ loc a b va vb, c.writeByte a loc = some va → c.writeByte b loc = some vb → a = b) :
    ObserverConditions c initial rf (InitialCo c) (selectedObservation c initial (writerSelector c) domain) :=
  selected_observation hd hg (fun _ _ _ hw => writer_selector_covers hu hw)

end Ptx.MemoryGraph
