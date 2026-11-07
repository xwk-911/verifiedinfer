import Ptx.Hopper.UnifiedControl
import Ptx.Hopper.UnifiedBytes
import Ptx.Hopper.TmaEventLookup

/-! Event-lookup transport preserves actual native collective fields and
control/access predicates. Source production, participation, completion and
resource-inventory multiplicities remain explicit independent obligations. -/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

theorem view_lookup_eq {a b : Candidate} (he : a.eventAt = b.eventAt) : a.view.eventAt = b.view.eventAt := by
  funext id
  simp only [view_eventAt,he]

theorem representative_lookup_eq {a b : Candidate} (he : a.eventAt = b.eventAt) : a.representativeAt = b.representativeAt := by
  funext id
  simp only [Candidate.representativeAt,Candidate.wgmmaAt,he]

theorem native_signature_lookup_eq {a b : Candidate} (he : a.eventAt = b.eventAt) : a.nativeSignatureAt = b.nativeSignatureAt := by
  funext id
  simp only [Candidate.nativeSignatureAt,he]

def Collective.lookupTransport {a b : Candidate} {issue} (he : a.eventAt = b.eventAt) (collective : Collective a issue) : Collective b issue := {
  calls := collective.calls,marks := collective.marks,sources := collective.sources
  representative := collective.representative
  matched := fun lane => by rw [← he]; exact collective.matched lane
  sameCTA := collective.sameCTA,sameMark := collective.sameMark,cohort := collective.cohort
}

theorem completed_lookup_transport {a b : Candidate} (he : a.eventAt = b.eventAt) {issue wait}
    (hc : WgmmaCompletedAt a issue wait) : WgmmaCompletedAt b issue wait := by
  obtain ⟨collective,lane,mark,groups,keep,before,after,query,hw,rest⟩ := hc
  exact ⟨collective.lookupTransport he,lane,mark,groups,keep,before,after,query,by rwa [← he],rest⟩

theorem completed_lookup_iff {a b : Candidate} (he : a.eventAt = b.eventAt) (issue wait) :
    WgmmaCompletedAt a issue wait ↔ WgmmaCompletedAt b issue wait :=
  ⟨completed_lookup_transport he,completed_lookup_transport he.symm⟩

theorem native_arrival_lookup_eq {a b : Candidate} (he : a.eventAt = b.eventAt) : NativeArrival a = NativeArrival b := by
  funext left right
  cases left <;> cases right <;>
    simp only [NativeArrival,Hopper.program_order_lookup_eq (view_lookup_eq he),native_signature_lookup_eq he]

theorem native_sync_lookup_eq {a b : Candidate} (he : a.eventAt = b.eventAt) (block : Dim3) : NativeSync block a = NativeSync block b := by
  funext left right
  simp only [NativeSync,native_signature_lookup_eq he]

theorem native_rendezvous_lookup_eq {a b : Candidate} (he : a.eventAt = b.eventAt) (block : Dim3) : NativeRendezvous block a = NativeRendezvous block b := by
  funext left right
  cases left <;> cases right <;> simp only [NativeRendezvous,native_sync_lookup_eq he block]

theorem native_issue_lookup_eq {a b : Candidate} (he : a.eventAt = b.eventAt) : NativeIssue a = NativeIssue b := by
  funext left right
  cases left <;> cases right <;> simp only [NativeIssue,representative_lookup_eq he]

theorem native_finish_lookup_eq {a b : Candidate} (he : a.eventAt = b.eventAt) : NativeFinish a = NativeFinish b := by
  funext left right
  apply propext
  cases left <;> cases right <;> simp only [NativeFinish,completed_lookup_iff he]

theorem control_edge_lookup_transport {a b : Candidate} (he : a.eventAt = b.eventAt) {block histories left right}
    (hc : ControlEdge block a histories left right) : ControlEdge block b histories left right := by
  rcases hc with hb | ha | hr | hi | hf
  · cases left <;> cases right <;> try exact False.elim hb
    exact .inl (Tma.control_edge_lookup_transport (view_lookup_eq he) hb)
  · exact .inr (.inl (by rwa [← native_arrival_lookup_eq he]))
  · exact .inr (.inr (.inl (by rwa [← native_rendezvous_lookup_eq he block])))
  · exact .inr (.inr (.inr (.inl (by rwa [← native_issue_lookup_eq he]))))
  · exact .inr (.inr (.inr (.inr (by rwa [← native_finish_lookup_eq he]))))

theorem access_kind_lookup_eq {a b : Hopper.Candidate} (he : a.eventAt = b.eventAt)
    (resolve : Tma.SharedResolver) (descriptor : Access.DescriptorResolver) : Access.kind resolve descriptor a = Access.kind resolve descriptor b := by
  funext node
  cases node with
  | tma node =>
    cases node <;> simp only [Access.kind,he,Tma.copy_lookup_eq he,Tma.readLocation,Tma.writeLocation,Tma.transferByte]
  | copyRead _ | copyWrite _ => simp only [Access.kind,Access.copyAt,he]

theorem kind_lookup_eq {a b : Candidate} (he : a.eventAt = b.eventAt)
    (resolve : Tma.SharedResolver) (descriptor : Access.DescriptorResolver) : kind resolve descriptor a = kind resolve descriptor b := by
  funext node
  cases node <;> simp only [kind,access_kind_lookup_eq (view_lookup_eq he),representative_lookup_eq he]

theorem read_byte_lookup_eq {a b : Candidate} (he : a.eventAt = b.eventAt)
    (resolve : Tma.SharedResolver) (descriptor : Access.DescriptorResolver) : readByte resolve descriptor a = readByte resolve descriptor b := by
  funext node loc
  simp only [readByte,kind_lookup_eq he]

theorem write_byte_lookup_eq {a b : Candidate} (he : a.eventAt = b.eventAt)
    (resolve : Tma.SharedResolver) (descriptor : Access.DescriptorResolver) : writeByte resolve descriptor a = writeByte resolve descriptor b := by
  funext node loc
  simp only [writeByte,kind_lookup_eq he]

end
end Ptx.Hopper.Unified
