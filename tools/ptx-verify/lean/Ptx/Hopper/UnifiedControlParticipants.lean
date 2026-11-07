import Ptx.Hopper.UnifiedControl

/-! Full aligned participation supplies actual source events, then warp-local
.sync matches exactly the 32 physical lanes. Aligned local scale-D predicates
remain local values. These rules neither synthesize proxy fences nor provide
byte-level ordering from native control paths. -/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

theorem native_signature_mem_trace {candidate : Candidate} {id signature}
    (he : candidate.nativeSignatureAt id = some signature) :
    ∃ trace ∈ candidate.traces, trace.id = id.thread ∧ signature ∈ trace.alignedSchedule := by
  obtain ⟨event,raw,hh,hs,ha⟩ := native_signature_actual he
  obtain ⟨trace,ht,hid,hget⟩ := eventAt_trace hh
  refine ⟨trace,ht,hid,List.mem_map.mpr ⟨raw,?_,ha⟩⟩
  exact List.mem_filterMap.mpr ⟨event,List.mem_of_getElem? hget,hs⟩
theorem trace_signature_has_event {candidate : Candidate} {trace signature}
    (hu : (candidate.traces.map ThreadTrace.id).Nodup) (ht : trace ∈ candidate.traces)
    (hs : signature ∈ trace.alignedSchedule) :
    ∃ id, id.thread = trace.id ∧ candidate.nativeSignatureAt id = some signature := by
  obtain ⟨raw,hr,ha⟩ := List.mem_map.mp hs
  obtain ⟨event,he,hraw⟩ := List.mem_filterMap.mp hr
  obtain ⟨serial,hget⟩ := List.getElem?_of_mem he
  refine ⟨⟨trace.id,serial⟩,rfl,?_⟩
  rw [Candidate.nativeSignatureAt,eventAt_of_member hu ht,hget]
  simp only [Option.bind_some,hraw,Option.map_some,ha]
theorem aligned_participant_event {candidate : Candidate} {block id signature}
    (hu : (candidate.traces.map ThreadTrace.id).Nodup) (hc : SchedulesAdmitted block candidate)
    (he : candidate.nativeSignatureAt id = some signature) (lane : Wgmma.Lane) :
    ∃ other, other.thread.cta = id.thread.cta ∧
      other.thread.tid.linear block = 128*(id.thread.tid.linear block/128)+lane.val ∧
      candidate.nativeSignatureAt other = some signature := by
  obtain ⟨trace,ht,hid,hs⟩ := native_signature_mem_trace he
  have hn : trace.nativeSchedule ≠ [] := by
    intro hn
    simp only [ThreadTrace.alignedSchedule,hn,List.map_nil,List.not_mem_nil] at hs
  obtain ⟨peer,hp,hcta,hlinear,hschedule⟩ := schedules_have_all_participants hc ht hn lane
  obtain ⟨other,hother,hactual⟩ := trace_signature_has_event hu hp (hschedule ▸ hs)
  refine ⟨other,?_,?_,hactual⟩
  · rw [hother,hcta,hid]
  · change other.thread.tid.linear block = _
    rw [hother]
    simpa only [ThreadTrace.linear,hid] using hlinear
theorem native_sync_has_all_warp_lanes {candidate : Candidate} {block id signature}
    (hu : (candidate.traces.map ThreadTrace.id).Nodup) (hc : SchedulesAdmitted block candidate)
    (he : candidate.nativeSignatureAt id = some signature) (lane : Fin 32) :
    ∃ other, other.thread.tid.linear block = 32*(id.thread.tid.linear block/32)+lane.val ∧ NativeSync block candidate other id := by
  let linear := id.thread.tid.linear block
  let groupLane : Wgmma.Lane := ⟨linear%128/32*32+lane.val,by have := lane.isLt; have := Nat.mod_lt linear (by decide : 0 < 128); omega⟩
  obtain ⟨other,hcta,hl,hs⟩ := aligned_participant_event hu hc he groupLane
  have hb := lane.isLt
  have hlinear : other.thread.tid.linear block = 32*(linear/32)+lane.val := by
    change other.thread.tid.linear block = 128*(linear/128)+(linear%128/32*32+lane.val) at hl
    omega
  refine ⟨other,hlinear,⟨⟨hcta,?_⟩,signature,hs,he⟩⟩
  change other.thread.tid.linear block/32 = linear/32
  omega
theorem synced_participants_source_pc {candidate code launch id signature}
    (hw : WellFormed code launch candidate) (hc : SchedulesAdmitted launch.geometry.block candidate)
    (he : candidate.nativeSignatureAt id = some signature) (lane : Fin 32) :
    ∃ other, NativeSync launch.geometry.block candidate other id ∧
      candidate.sourcePC code launch.params launch.geometry.block other = some signature.pc := by
  obtain ⟨other,_,hs⟩ := native_sync_has_all_warp_lanes hw.2.1 hc he lane
  obtain ⟨actual,ha,hb⟩ := hs.2
  have heq := Option.some.inj (hb.symm.trans he)
  subst actual
  exact ⟨other,hs,native_signature_actual_pc hw ha⟩

end
end Ptx.Hopper.Unified
