import Ptx.Tests.HopperCollectiveCycle

/-! The generated cycle is invisible to the old source/CTA/TMA control graph:
it has no copies/resources and admits an explicit old-control rank. The new
warp-rendezvous edges, rather than a pre-existing rejection, expose the cycle.
-/
namespace Ptx.HopperCollectiveCycleTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def sourceRank (id : Ptx.Event.EventId) : Nat :=
  if id.thread.tid.x = 0 then 10*id.serial else 10*(id.serial+1)
def oldControlRank : Tma.Node → Nat
  | .source id => sourceRank id
  | _ => 0
def copyBytes : Hopper.Event → Option Nat
  | .tmaIssue op => some op.descriptor.bytes
  | _ => none
theorem all_trace_copy_bytes_empty : ∀ lane : Wgmma.Lane, (trace lane).view.events.filterMap copyBytes = [] := by decide
theorem all_trace_event_lengths : ∀ lane : Wgmma.Lane, (trace lane).view.events.length = 3 := by decide
theorem all_cta_tag_ranks : ∀ lane : Wgmma.Lane, ∀ serial ∈ List.range 3, ∀ arrival : Bool,
    ∀ tag ∈ (candidate.view.ctaTag arrival (eid lane serial)).toList,
    sourceRank (eid lane serial) = if arrival then 10 else 20 := by decide
theorem copy_at_none (id : Tma.CopyId) : Tma.copyAt candidate.view id = none := by
  cases hc : Tma.copyAt candidate.view id with
  | none => rfl
  | some op =>
    obtain ⟨actual,ht,_,hget⟩ := Hopper.eventAt_trace (Tma.copyAt_iff.mp hc)
    obtain ⟨rich,hr,rfl⟩ := List.mem_map.mp ht
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp hr
    have hm := List.mem_filterMap.mpr ⟨Hopper.Event.tmaIssue op,List.mem_of_getElem? hget,show copyBytes (.tmaIssue op) = some op.descriptor.bytes from rfl⟩
    rw [all_trace_copy_bytes_empty] at hm
    cases hm
theorem present_has_lane {id} (hp : candidate.view.Present id) : ∃ lane, id.thread = (HopperStage.ctx lane).id ∧ id.serial < 3 := by
  obtain ⟨event,he⟩ := Option.isSome_iff_exists.mp hp
  obtain ⟨actual,ht,hid,hget⟩ := Hopper.eventAt_trace he
  obtain ⟨rich,hr,rfl⟩ := List.mem_map.mp ht
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp hr
  have hb := (List.getElem?_eq_some_iff.mp hget).1
  rw [all_trace_event_lengths] at hb
  exact ⟨lane,hid.symm,hb⟩
theorem old_program_order_rank {left right} (hp : Tma.ProgramOrder candidate.view left right) :
    oldControlRank left < oldControlRank right := by
  cases left <;> cases right <;> try exact False.elim hp
  rename_i left right
  obtain ⟨thread,serial⟩ := left
  obtain ⟨other,last⟩ := right
  have he : thread = other := hp.2.2.1
  subst other
  have hl : serial < last := hp.2.2.2
  change (if thread.tid.x = 0 then 10*serial else 10*(serial+1)) < (if thread.tid.x = 0 then 10*last else 10*(last+1))
  split_ifs <;> omega
theorem actual_cta_rank {id arrival tag} (he : candidate.view.ctaTag arrival id = some tag) :
    sourceRank id = if arrival then 10 else 20 := by
  obtain ⟨lane,hid,hb⟩ := present_has_lane (Hopper.cta_tag_present he)
  have hid' : id = eid lane id.serial := congrArg₂ Ptx.Event.EventId.mk hid rfl
  rw [hid'] at he ⊢
  exact all_cta_tag_ranks lane id.serial (List.mem_range.mpr hb) arrival tag (by simp only [he,Option.toList_some,List.mem_singleton])
theorem old_cta_order_rank {left right} (hc : Tma.CTAControl candidate.view left right) :
    oldControlRank left < oldControlRank right := by
  cases left <;> cases right <;> try exact False.elim hc
  rename_i left right
  cases ha : candidate.view.ctaTag true left with
  | none => simp [Tma.CTAControl,Hopper.CTAControl,ha] at hc
  | some a =>
    cases hb : candidate.view.ctaTag false right with
    | none => simp [Tma.CTAControl,Hopper.CTAControl,hb] at hc
    | some b =>
      change sourceRank left < sourceRank right
      rw [actual_cta_rank ha,actual_cta_rank hb]
      decide
theorem old_control_acyclic : Tma.ControlAcyclic candidate.view (fun _ => []) := by
  apply Tma.control_acyclic_of_rank oldControlRank
  · exact fun _ _ => old_program_order_rank
  · exact fun _ _ => old_cta_order_rank
  · intro left right he
    cases he with
    | issue hp => simp [copy_at_none] at hp
    | descriptorRead hp | data hp => simp [Tma.readLocation,copy_at_none] at hp
    | descriptorWrite hp | complete hp => simp [Tma.WritePresent,copy_at_none] at hp
  · rintro left right ⟨_,_,hmem,_⟩
    cases hmem

end
end Ptx.HopperCollectiveCycleTests
