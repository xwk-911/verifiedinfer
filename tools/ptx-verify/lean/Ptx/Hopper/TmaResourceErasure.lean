import Ptx.Hopper.TmaControl

/-! Proven metadata erasure for resource/control checking. Memory payloads,
oracles and final states are discarded; event slots, barriers, CTA tags and
TMA descriptor/address metadata remain. This never asserts source production,
memory agreement or allowed execution for the erased candidate. -/
namespace Ptx.Hopper.Tma.ResourceErasure
open Ptx.ISA
noncomputable section

def event : Hopper.Event → Hopper.Event
  | .barrier data => .barrier data
  | .tmaIssue copy => .tmaIssue {copy with payload := []}
  | .proxyFenceAsyncShared cta => .proxyFenceAsyncShared cta
  | .ampere (.ordinary (.barrierArrival id generation)) => .ampere (.ordinary (.barrierArrival id generation))
  | .ampere (.ordinary (.barrierReturn id generation)) => .ampere (.ordinary (.barrierReturn id generation))
  | .wgmma tag => .wgmma tag
  | _ => .wgmma .fence
def trace (original : Hopper.ThreadTrace) : Hopper.ThreadTrace := {
  id := original.id
  oracle := {ampere := {scalar := fun _ => .integer 0,bytes := fun _ => []},wait := fun _ => false}
  count := 0
  final := {}
  events := original.events.map event
}
def candidate (original : Hopper.Candidate) : Hopper.Candidate := ⟨original.traces.map trace⟩

theorem traceAt_preserved (original : Hopper.Candidate) (id : ThreadId) :
    (candidate original).traceAt id = (original.traceAt id).map trace := by
  unfold Hopper.Candidate.traceAt candidate
  induction original.traces with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons,List.find?_cons,trace]; split <;> simp_all [trace]
theorem eventAt_preserved (original : Hopper.Candidate) (id : Ptx.Event.EventId) :
    (candidate original).eventAt id = (original.eventAt id).map event := by
  simp only [Hopper.Candidate.eventAt,traceAt_preserved]
  cases ht : original.traceAt id.thread <;> simp [ht,trace,List.getElem?_map]
theorem event_ids_preserved (original : Hopper.Candidate) :
    (candidate original).eventIds = original.eventIds := by
  simp only [Hopper.Candidate.eventIds,candidate,List.flatMap_map,Function.comp_def,trace,List.length_map]
theorem present_preserved (original : Hopper.Candidate) (id : Ptx.Event.EventId) :
    (candidate original).Present id ↔ original.Present id := by
  simp only [Hopper.Candidate.Present,eventAt_preserved,Option.isSome_map]
theorem barrierAt_preserved (original : Hopper.Candidate) (id : Ptx.Event.EventId) :
    (candidate original).barrierAt id = original.barrierAt id := by
  simp only [Hopper.Candidate.barrierAt,eventAt_preserved]
  cases he : original.eventAt id with
  | none => rfl
  | some e =>
    cases e <;> try rfl
    rename_i e
    cases e <;> try rfl
    rename_i e
    cases e <;> rfl
theorem ctaTag_preserved (original : Hopper.Candidate) (id : Ptx.Event.EventId) (arrival : Bool) :
    (candidate original).ctaTag arrival id = original.ctaTag arrival id := by
  simp only [Hopper.Candidate.ctaTag,eventAt_preserved]
  cases he : original.eventAt id with
  | none => rfl
  | some e =>
    cases e <;> try rfl
    rename_i e
    cases e <;> try rfl
    rename_i e
    cases e <;> rfl
theorem copyAt_preserved (original : Hopper.Candidate) (id : CopyId) :
    copyAt (candidate original) id = (copyAt original id).map (fun copy => {copy with payload := []}) := by
  simp only [copyAt,eventAt_preserved]
  cases he : original.eventAt id.issue with
  | none => rfl
  | some e =>
    cases e <;> try rfl
    rename_i e
    cases e <;> try rfl
    rename_i e
    cases e <;> rfl
theorem notification_preserved (resolve : SharedResolver) (original : Hopper.Candidate) (id : CopyId) :
    notification resolve (candidate original) id = notification resolve original id := by
  simp only [notification,copyAt_preserved,Option.map_map,Function.comp_def]
theorem barrier_records_preserved (original : Hopper.Candidate) :
    (candidate original).barrierRecords = original.barrierRecords := by
  simp only [Hopper.Candidate.barrierRecords,event_ids_preserved,barrierAt_preserved]
theorem copies_preserved (original : Hopper.Candidate) : copies (candidate original) = copies original := by
  unfold copies
  rw [event_ids_preserved]
  apply List.filterMap_congr
  intro id _
  rw [eventAt_preserved]
  cases he : original.eventAt id with
  | none => rfl
  | some e =>
    cases e <;> try rfl
    rename_i e
    cases e <;> try rfl
    rename_i e
    cases e <;> rfl
theorem origins_preserved (original : Hopper.Candidate) : origins (candidate original) = origins original := by
  simp only [origins,barrier_records_preserved,copies_preserved]
theorem resourceAt_preserved (resolve : SharedResolver) (original : Hopper.Candidate) (origin : Origin) :
    resourceAt resolve (candidate original) origin = resourceAt resolve original origin := by
  cases origin <;> simp only [resourceAt,barrierAt_preserved,notification_preserved]
theorem inventory_preserved (resolve : SharedResolver) (original : Hopper.Candidate) (loc : Location) :
    inventory resolve (candidate original) loc = inventory resolve original loc := by
  simp only [inventory,origins_preserved,resourceAt_preserved]
theorem history_valid_preserved {resolve original loc entries} :
    HistoryValid resolve (candidate original) loc entries ↔ HistoryValid resolve original loc entries := by
  constructor <;> intro h <;> exact ⟨h.unique,by simpa only [inventory_preserved] using h.exhaustive,h.ordered,h.protocol⟩

theorem read_location_preserved (original : Hopper.Candidate) (id : CopyId) (offset : Nat) :
    readLocation (candidate original) id offset = readLocation original id offset := by
  simp only [readLocation,copyAt_preserved]
  cases copyAt original id <;> rfl
theorem write_present_preserved (original : Hopper.Candidate) (id : CopyId) (offset : Nat) :
    WritePresent (candidate original) id offset ↔ WritePresent original id offset := by
  simp only [WritePresent,copyAt_preserved]
  cases copyAt original id <;> rfl
theorem program_order_preserved (original : Hopper.Candidate) (left right : Node) :
    ProgramOrder (candidate original) left right ↔ ProgramOrder original left right := by
  cases left <;> cases right <;> simp only [ProgramOrder,Hopper.ProgramOrder,present_preserved]
theorem cta_control_preserved (original : Hopper.Candidate) (left right : Node) :
    CTAControl (candidate original) left right ↔ CTAControl original left right := by
  cases left <;> cases right <;> simp only [CTAControl,Hopper.CTAControl,ctaTag_preserved]
theorem internal_edge_preserved (original : Hopper.Candidate) (left right : Node) :
    InternalEdge (candidate original) left right ↔ InternalEdge original left right := by
  constructor <;> intro h <;> cases h with
  | issue h => exact .issue (by simpa only [copyAt_preserved,Option.isSome_map] using h)
  | descriptorRead h => exact .descriptorRead (by simpa only [read_location_preserved] using h)
  | descriptorWrite h => exact .descriptorWrite (by simpa only [write_present_preserved] using h)
  | data h => exact .data (by simpa only [read_location_preserved] using h)
  | complete h => exact .complete (by simpa only [write_present_preserved] using h)
theorem control_edge_preserved (original : Hopper.Candidate) (histories) (left right : Node) :
    ControlEdge (candidate original) histories left right ↔ ControlEdge original histories left right := by
  simp only [ControlEdge,program_order_preserved,cta_control_preserved,internal_edge_preserved]
theorem control_acyclic_preserved (original : Hopper.Candidate) (histories) :
    ControlAcyclic (candidate original) histories ↔ ControlAcyclic original histories := by
  constructor <;> intro h node hp
  · exact h node (hp.mono (fun a b he => (control_edge_preserved original histories a b).mpr he))
  · exact h node (hp.mono (fun a b he => (control_edge_preserved original histories a b).mp he))

end
end Ptx.Hopper.Tma.ResourceErasure
