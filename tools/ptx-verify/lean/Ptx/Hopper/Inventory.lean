import Ptx.Hopper.Source

/-! A finite inventory of actual candidate resource operations, indexed by
source event identities. Invented/missing/repeated entries are checked separately
when a resource history is proposed. No integer or real load value is assumed. -/
namespace Ptx.Hopper
open Ptx.ISA
noncomputable section

structure ResourceEntry where
  id : Ptx.Event.EventId
  operation : BarrierOp
  deriving Repr, DecidableEq
structure ResourceRecord where
  id : Ptx.Event.EventId
  data : BarrierEvent
  deriving Repr, DecidableEq

def Candidate.eventIds (c : Candidate) : List Ptx.Event.EventId :=
  c.traces.flatMap (fun t => (List.range t.events.length).map (fun serial => ⟨t.id,serial⟩))
def Candidate.barrierRecords (c : Candidate) : List ResourceRecord :=
  c.eventIds.filterMap (fun id => (c.barrierAt id).map (fun data => ⟨id,data⟩))
def Candidate.resourceLocations (c : Candidate) : List Location :=
  (c.barrierRecords.map (fun r => r.data.location)).eraseDups
def Candidate.barrierInventory (c : Candidate) (loc : Location) : List ResourceEntry :=
  c.barrierRecords.filterMap (fun record => if loc = record.data.location then some ⟨record.id,record.data.operation⟩ else none)

theorem present_mem_eventIds {c : Candidate} {id} (he : c.Present id) : id ∈ c.eventIds := by
  obtain ⟨kind,hk⟩ := Option.isSome_iff_exists.mp he
  obtain ⟨t,ht,hid,hget⟩ := eventAt_trace hk
  apply List.mem_flatMap.mpr
  refine ⟨t,ht,List.mem_map.mpr ⟨id.serial,List.mem_range.mpr (List.getElem?_eq_some_iff.mp hget).1,?_⟩⟩
  cases id
  simp_all

theorem barrier_record_iff {c : Candidate} {id data} :
    ResourceRecord.mk id data ∈ c.barrierRecords ↔ c.barrierAt id = some data := by
  constructor
  · intro he
    obtain ⟨event,_,hget⟩ := List.mem_filterMap.mp he
    cases hbar : c.barrierAt event with
    | none => simp [hbar] at hget
    | some actual =>
      simp only [hbar,Option.map_some,Option.some.injEq,ResourceRecord.mk.injEq] at hget
      rcases hget with ⟨rfl,rfl⟩
      exact hbar
  · intro he
    exact List.mem_filterMap.mpr ⟨id,present_mem_eventIds (barrier_present he),by simp [he]⟩

theorem barrier_inventory_iff {c : Candidate} {loc id op} :
    ResourceEntry.mk id op ∈ c.barrierInventory loc ↔ c.barrierAt id = some ⟨loc,op⟩ := by
  constructor
  · intro he
    obtain ⟨record,hr,hget⟩ := List.mem_filterMap.mp he
    split at hget
    · rename_i hl
      simp only [Option.some.injEq,ResourceEntry.mk.injEq] at hget
      rcases record with ⟨rid,⟨rloc,rop⟩⟩
      cases hget.1
      cases hget.2
      cases hl
      exact barrier_record_iff.mp hr
    · cases hget
  · intro he
    exact List.mem_filterMap.mpr ⟨⟨id,⟨loc,op⟩⟩,barrier_record_iff.mpr he,by simp⟩

theorem barrier_location_mem {c : Candidate} {id loc op} (he : c.barrierAt id = some ⟨loc,op⟩) : loc ∈ c.resourceLocations := by
  apply List.mem_eraseDups.mpr
  exact List.mem_map.mpr ⟨⟨id,⟨loc,op⟩⟩,barrier_record_iff.mpr he,rfl⟩

theorem barrier_inventory_empty {c : Candidate} {loc} (hl : loc ∉ c.resourceLocations) : c.barrierInventory loc = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro entry he
  exact hl (barrier_location_mem (barrier_inventory_iff.mp he))

end
end Ptx.Hopper
