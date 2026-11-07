import Ptx.Event.Observation

/-! Memory and observation witnesses for an event-empty view. This is useful
for register-only collective programs: their separate collective obligations
are not discharged by the absence of ordinary memory events. -/
namespace Ptx.Event
open Ptx.ISA
variable {ByteValue Answers : Type}

theorem empty_view_memory_conditions {candidate : Candidate ByteValue Answers} (initial : ByteMap ByteValue)
    (rf : ReadsFrom) (he : ∀ id, candidate.eventAt id = none) :
    GenericMemoryConditions candidate initial rf (InitialCo candidate) := by
  have hr : ∀ id loc, candidate.readByte id loc = none := by
    intro id loc; simp only [Candidate.readByte,he,Option.bind_none]
  have hw : ∀ id loc, candidate.writeByte id loc = none := by
    intro id loc; simp only [Candidate.writeByte,he,Option.bind_none]
  apply initial_co_conditions (fun _ => 0)
  · intro a b hp; simp [ProgramOrder,Candidate.Present,he] at hp
  · rintro a b ⟨_,bid,generation,hb,_⟩; simp [he] at hb
  · rintro a b ⟨ha,_⟩; simp [Candidate.Present,he] at ha
  · intro leave bid generation hb; simp [he] at hb
  · intro loc a b va vb ha; simp [hw] at ha
  · intro read loc value ha; simp [hr] at ha
  · intro read writer loc vr vw ha; simp [hr] at ha
  · intro read writer loc vr vw ha; simp [hr] at ha

theorem empty_view_no_races {candidate : Candidate ByteValue Answers}
    (he : ∀ id, candidate.eventAt id = none) : ∀ a b, ¬DataRace candidate rf a b := by
  intro a b hd
  obtain ⟨loc,ha,_⟩ := hd.overlap
  simp [Candidate.Accesses,Candidate.readByte,Candidate.writeByte,he] at ha

theorem empty_view_observer {candidate : Candidate ByteValue Answers} (initial : ByteMap ByteValue)
    (rf : ReadsFrom) (domain : List Location) (he : ∀ id, candidate.eventAt id = none)
    (hc : candidate.Complete) (hg : ∀ loc ∈ domain, loc.space = .global) :
    ObserverConditions candidate initial rf (InitialCo candidate) ⟨domain,initial,fun _ => .initial⟩ := by
  refine ⟨hc,hg,?_,?_⟩
  · intro loc _ _; rfl
  · intro loc _ _ writer value hw
    simp [Candidate.writeByte,he] at hw

theorem empty_view_observer_frame {candidate : Candidate ByteValue Answers} {initial rf co observation}
    (he : ∀ id, candidate.eventAt id = none) (ho : ObserverConditions candidate initial rf co observation)
    {loc} (hd : loc ∈ observation.domain) : observation.output loc = initial loc := by
  apply observer_unwritten ho hd (race_free_observer_eligible (empty_view_no_races he) loc)
  intro writer
  simp [Candidate.writeByte,he]

end Ptx.Event
