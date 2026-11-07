import Ptx.Kernels.ShuffleProbeSource
import Ptx.Event.AlignedWords

/-! Observable frame outside all actual wrapped source output spans. Aligned
word footprints rule out mixed-size overlap without assuming unique writers or
race freedom. This is not the distinct-writer output-array theorem. -/
namespace Ptx.Kernels.ShuffleProbe
open Ptx.ISA Ptx.Shuffle
noncomputable section

theorem w64_mod_four (value : Nat) : w64 value % 4 = value % 4 :=
  Nat.mod_mod_of_dvd _ (by decide)

theorem output_word_aligned (input : Inputs) (ctx : Scalar.Context) (offset : Nat)
    (ha : input.out % 4 = 0) (ho : offset % 4 = 0) : (outputLoc input ctx offset).address % 4 = 0 := by
  change w64 (address input ctx+offset) % 4 = 0
  simp [w64_mod_four,address,Nat.add_mod,Nat.mul_mod,ha,ho]

theorem memory_footprint_shape {mode input launch candidate actual} (hp : Params input launch.params)
    (hw : Shuffle.WellFormed (code mode) launch candidate) (hc : Shuffle.Complete candidate)
    (he : candidate.view.Present actual) :
    ∃ trace ∈ candidate.traces, ∃ slot, (slot = 0 ∨ slot = 4) ∧
      (candidate.view.eventAt actual).bind Ptx.Event.Kind.footprint = some (outputLoc input (context launch trace.id) slot,4) := by
  obtain ⟨kind,hkind⟩ := Option.isSome_iff_exists.mp he
  obtain ⟨trace,ht,_,⟨_,rfl⟩ | ⟨_,rfl⟩⟩ := actual_memory_event_shape hp hw hc hkind
  · exact ⟨trace,ht,0,Or.inl rfl,by simp [hkind,Ptx.Event.Kind.footprint]⟩
  · exact ⟨trace,ht,4,Or.inr rfl,by simp [hkind,Ptx.Event.Kind.footprint]⟩

theorem no_mixed_size_races {mode input launch candidate rf} (hp : Params input launch.params)
    (hw : Shuffle.WellFormed (code mode) launch candidate) (hc : Shuffle.Complete candidate)
    (ha : input.out % 4 = 0) : ¬Ptx.Event.MixedSizeRace candidate.view rf := by
  apply Ptx.Event.aligned_word_footprints_no_mixed_races
  intro actual he
  obtain ⟨trace,_,slot,hs,hfoot⟩ := memory_footprint_shape hp hw hc he
  exact ⟨_,hfoot,output_word_aligned input _ slot ha (by rcases hs with rfl | rfl <;> decide)⟩

/-- An input/geometry footprint independent of the candidate and its oracles.
The two starts are wrapped separately, just as the source address operands. -/
def OutputFootprint (input : Inputs) (launch : Scalar.Launch) (loc : Location) : Prop :=
  ∃ id, id.Valid launch.geometry ∧ ∃ slot, (slot = 0 ∨ slot = 4) ∧ loc.space = .global ∧
    (outputLoc input (context launch id) slot).address ≤ loc.address ∧
    loc.address < (outputLoc input (context launch id) slot).address+4

theorem actual_write_is_in_output_footprint {mode input launch candidate actual loc value}
    (hp : Params input launch.params) (hw : Shuffle.WellFormed (code mode) launch candidate)
    (hc : Shuffle.Complete candidate) (hwrite : candidate.view.writeByte actual loc = some value) :
    OutputFootprint input launch loc := by
  have haccess : candidate.view.Accesses actual loc := Or.inr (by rw [hwrite]; rfl)
  obtain ⟨trace,ht,slot,hs,hfoot⟩ := memory_footprint_shape hp hw hc (Ptx.Event.accesses_present haccess)
  have hb := Ptx.Event.access_footprint_bounds haccess hfoot
  exact ⟨trace.id,(hw.2.2.1 trace ht).1,slot,hs,hb.1.symm,hb.2⟩

theorem outside_output_has_no_writer {mode input launch candidate loc} (hp : Params input launch.params)
    (hw : Shuffle.WellFormed (code mode) launch candidate) (hc : Shuffle.Complete candidate)
    (ho : ¬OutputFootprint input launch loc) : ∀ actual, candidate.view.writeByte actual loc = none := by
  intro actual
  cases he : candidate.view.writeByte actual loc with
  | none => rfl
  | some value => exact False.elim (ho (actual_write_is_in_output_footprint hp hw hc he))

theorem observer_frame_outside_output {mode input launch candidate rf co observation loc}
    (hp : Params input launch.params) (hw : Shuffle.WellFormed (code mode) launch candidate)
    (hc : Shuffle.Complete candidate) (ha : input.out % 4 = 0)
    (ho : Ptx.Event.ObserverConditions candidate.view launch.initial rf co observation)
    (hl : loc ∈ observation.domain) (hout : ¬OutputFootprint input launch loc) :
    observation.output loc = launch.initial loc := by
  have hn := outside_output_has_no_writer hp hw hc hout
  have he : Ptx.Event.ObserverEligible candidate.view rf loc := by
    refine ⟨no_mixed_size_races hp hw hc ha,?_⟩
    rintro ⟨a,_,hw,_,_⟩
    simp [hn] at hw
  exact Ptx.Event.observer_unwritten ho hl he hn

theorem outside_output_frame_contract (mode : Mode) (input : Inputs) (domain : Scalar.Launch → List Location) :
    Shuffle.Triple (code mode) (fun launch => Params input launch.params ∧ input.out % 4 = 0) domain
      (fun launch output => ∀ loc ∈ domain launch, ¬OutputFootprint input launch loc → output loc = launch.initial loc) := by
  intro launch candidate rf co observation hp hw hc _ _ _ _ ho hd loc hl hout
  apply observer_frame_outside_output hp.1 hw hc hp.2 ho _ hout
  simpa only [hd] using hl

end
end Ptx.Kernels.ShuffleProbe
