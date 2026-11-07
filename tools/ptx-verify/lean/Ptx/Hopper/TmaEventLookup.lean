import Ptx.Hopper.TmaControl

/-! Event-lookup transport for TMA control and resource components. History
transport additionally checks an event-ID permutation, preserving multiplicity;
equal lookups alone do not justify inventory exhaustiveness. -/
namespace Ptx.Hopper
open Ptx.ISA
noncomputable section

theorem program_order_lookup_eq {a b : Candidate} (he : a.eventAt = b.eventAt) : ProgramOrder a = ProgramOrder b := by
  funext left right
  simp only [ProgramOrder,Candidate.Present,he]

theorem cta_control_lookup_eq {a b : Candidate} (he : a.eventAt = b.eventAt) : CTAControl a = CTAControl b := by
  funext left right
  simp only [CTAControl,Candidate.ctaTag,he]

namespace Tma

theorem copy_lookup_eq {a b : Candidate} (he : a.eventAt = b.eventAt) : copyAt a = copyAt b := by
  funext id
  simp only [copyAt,he]

theorem read_location_lookup_eq {a b : Candidate} (he : a.eventAt = b.eventAt) : readLocation a = readLocation b := by
  funext id offset
  simp only [readLocation,copy_lookup_eq he]

theorem write_present_lookup_eq {a b : Candidate} (he : a.eventAt = b.eventAt) : WritePresent a = WritePresent b := by
  funext id offset
  simp only [WritePresent,copy_lookup_eq he]

theorem internal_edge_lookup_transport {a b : Candidate} (he : a.eventAt = b.eventAt) {left right}
    (hi : InternalEdge a left right) : InternalEdge b left right := by
  cases hi with
  | issue h => exact .issue (by rwa [← copy_lookup_eq he])
  | descriptorRead h => exact .descriptorRead (by rwa [← read_location_lookup_eq he])
  | descriptorWrite h => exact .descriptorWrite (by rwa [← write_present_lookup_eq he])
  | data h => exact .data (by rwa [← read_location_lookup_eq he])
  | complete h => exact .complete (by rwa [← write_present_lookup_eq he])

theorem program_order_lookup_eq {a b : Candidate} (he : a.eventAt = b.eventAt) : ProgramOrder a = ProgramOrder b := by
  funext left right
  cases left <;> cases right <;> simp only [ProgramOrder,Hopper.program_order_lookup_eq he]

theorem cta_control_lookup_eq {a b : Candidate} (he : a.eventAt = b.eventAt) : CTAControl a = CTAControl b := by
  funext left right
  cases left <;> cases right <;> simp only [CTAControl,Hopper.cta_control_lookup_eq he]

theorem control_edge_lookup_transport {a b : Candidate} (he : a.eventAt = b.eventAt) {histories left right}
    (hc : ControlEdge a histories left right) : ControlEdge b histories left right := by
  rcases hc with hp | hc | hi | hr
  · exact .inl (by rwa [← program_order_lookup_eq he])
  · exact .inr (.inl (by rwa [← cta_control_lookup_eq he]))
  · exact .inr (.inr (.inl (internal_edge_lookup_transport he hi)))
  · exact .inr (.inr (.inr hr))

theorem resource_at_lookup_eq {a b : Candidate} (he : a.eventAt = b.eventAt) (resolve : SharedResolver) :
    resourceAt resolve a = resourceAt resolve b := by
  funext origin
  cases origin <;> simp only [resourceAt,Candidate.barrierAt,notification,he,copy_lookup_eq he]

theorem inventory_lookup_perm {a b : Candidate} (he : a.eventAt = b.eventAt) (hi : a.eventIds.Perm b.eventIds)
    (resolve : SharedResolver) (loc : Location) : (inventory resolve a loc).Perm (inventory resolve b loc) := by
  have hbarrier : a.barrierRecords.Perm b.barrierRecords := by
    unfold Candidate.barrierRecords
    simp only [Candidate.barrierAt,he]
    exact hi.filterMap _
  have hcopy : (copies a).Perm (copies b) := by
    unfold copies
    rw [he]
    exact hi.filterMap _
  have horigin : (origins a).Perm (origins b) :=
    (hbarrier.map (fun r : Hopper.ResourceRecord => Origin.source r.id)).append (hcopy.map Origin.notification)
  unfold inventory
  rw [resource_at_lookup_eq he resolve]
  exact horigin.filterMap _

theorem history_lookup_transport {a b : Candidate} (he : a.eventAt = b.eventAt) (hi : a.eventIds.Perm b.eventIds)
    {resolve loc entries} (hh : HistoryValid resolve a loc entries) : HistoryValid resolve b loc entries :=
  ⟨hh.unique,hh.exhaustive.trans (inventory_lookup_perm he hi resolve loc),hh.ordered,hh.protocol⟩

end Tma
end
end Ptx.Hopper
