import Ptx.Kernels.HopperDoubleBufferZeroSource

/-! Event-ID multiplicities for arbitrary completed zero-K traces. Thread
coverage and unique IDs give a permutation, not an assumed canonical trace
order. All list comparisons here concern only thread/event metadata. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def zeroThreadLane (thread : ThreadId) : Wgmma.Lane := ⟨resourceLane thread%128,Nat.mod_lt _ (by decide)⟩
def zeroThreadEventIds (thread : ThreadId) : List Ptx.Event.EventId :=
  (List.range (completeEvents 0 (zeroThreadLane thread)).length).map (fun serial => ⟨thread,serial⟩)

theorem zero_thread_lane_value (lane : Wgmma.Lane) : zeroThreadLane (ctx 0 lane).id = lane := by
  apply Fin.ext
  simp only [zeroThreadLane,resource_lane_value,Nat.mod_eq_of_lt lane.isLt]

theorem zero_thread_ids_perm {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) :
    (candidate.traces.map Unified.ThreadTrace.id).Perm (zeroCandidate.traces.map Unified.ThreadTrace.id) := by
  have hr : Unified.WellFormed code (completeLaunch 0 initial) zeroCandidate := data_source_well_formed (fun _ _ => 0) (fun _ _ => 0) 0 initial (by decide)
  apply (List.perm_ext_iff_of_nodup hw.2.1 hr.2.1).2
  intro id
  constructor
  · rintro hm
    obtain ⟨trace,ht,rfl⟩ := List.mem_map.mp hm
    obtain ⟨other,ho,hid⟩ := hr.2.2.2 trace.id (hw.2.2.1 trace ht).1
    exact List.mem_map.mpr ⟨other,ho,hid⟩
  · rintro hm
    obtain ⟨trace,ht,rfl⟩ := List.mem_map.mp hm
    obtain ⟨other,ho,hid⟩ := hw.2.2.2 trace.id (hr.2.2.1 trace ht).1
    exact List.mem_map.mpr ⟨other,ho,hid⟩

theorem completed_zero_event_ids_list {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    candidate.view.eventIds = (candidate.traces.map Unified.ThreadTrace.id).flatMap zeroThreadEventIds := by
  simp only [Hopper.Candidate.eventIds,Unified.Candidate.view,List.flatMap_map,Unified.ThreadTrace.view,List.length_map]
  apply List.flatMap_congr
  intro trace ht
  obtain ⟨lane,hid,_,_,he⟩ := completed_zero_trace hw hc ht
  rw [he,hid]
  simp only [zeroThreadEventIds,zero_thread_lane_value]

theorem completed_zero_event_ids_perm {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    candidate.view.eventIds.Perm zeroCandidate.view.eventIds := by
  have hr : Unified.WellFormed code (completeLaunch 0 initial) zeroCandidate := data_source_well_formed (fun _ _ => 0) (fun _ _ => 0) 0 initial (by decide)
  rw [completed_zero_event_ids_list hw hc,completed_zero_event_ids_list hr (data_candidate_local _ _ 0 (by decide))]
  exact (zero_thread_ids_perm hw).flatMap (fun _ _ => List.Perm.refl _)

end
end Ptx.Kernels.HopperDoubleBuffer
