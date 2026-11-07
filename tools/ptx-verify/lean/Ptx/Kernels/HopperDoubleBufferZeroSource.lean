import Ptx.Kernels.HopperDoubleBufferKernelReconstruction
import Ptx.Kernels.HopperDoubleBufferDataSource
import Ptx.Kernels.HopperDoubleBufferResourceSerials

/-! Every source-well-formed completed zero-K candidate has the same actual
rich event lookup as the standard zero-K witness. Oracles and trace order may
differ; source validity/completion are checked, not inferred from event equality. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def zeroCandidate : Unified.Candidate := dataCompleteCandidate (fun _ _ => 0) (fun _ _ => 0) 0

theorem data_zero_events (a b lane) : dataCompleteEvents a b 0 lane = completeEvents 0 lane := rfl

theorem completed_zero_trace {initial candidate trace}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) (hm : trace ∈ candidate.traces) :
    ∃ lane : Wgmma.Lane, trace.id = (ctx 0 lane).id ∧ trace.count = completeSteps 0 lane ∧
      trace.final = completeState 0 lane ∧ trace.events = completeEvents 0 lane := by
  obtain ⟨lane,hid,hzero | hpositive⟩ := completed_candidate_trace_reconstruct (by decide) hw hc hm
  · exact ⟨lane,hid,hzero.2⟩
  · have h := hpositive.1
    omega

theorem zero_lane_identity {left right : Wgmma.Lane} (he : (ctx 0 left).id = (ctx 0 right).id) : left = right := by
  apply Fin.ext
  have hl := congrArg resourceLane he
  simpa only [resource_lane_value] using hl

theorem completed_zero_event_at_lane {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    (lane : Wgmma.Lane) (serial : Nat) : candidate.eventAt ⟨(ctx 0 lane).id,serial⟩ = (completeEvents 0 lane)[serial]? := by
  obtain ⟨trace,hm,hid⟩ := hw.2.2.2 (ctx 0 lane).id (HopperStage.ctx_valid lane)
  obtain ⟨actual,hactual,_,_,he⟩ := completed_zero_trace hw hc hm
  have hl : actual = lane := zero_lane_identity (hactual.symm.trans hid)
  subst actual
  rw [← hid,Unified.eventAt_of_member hw.2.1 hm,he]

theorem zero_candidate_event_at_lane (lane : Wgmma.Lane) (serial : Nat) :
    zeroCandidate.eventAt ⟨(ctx 0 lane).id,serial⟩ = (completeEvents 0 lane)[serial]? := by
  have hw := data_source_well_formed (fun _ _ => 0) (fun _ _ => 0) 0 (fun _ => .bits (byte 0)) (by decide)
  exact completed_zero_event_at_lane hw (data_candidate_local _ _ 0 (by decide)) lane serial

theorem completed_zero_event_to_reference {initial candidate id event}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    (he : candidate.eventAt id = some event) : zeroCandidate.eventAt id = some event := by
  obtain ⟨trace,hm,hid,hget⟩ := Unified.eventAt_trace he
  obtain ⟨lane,hthread,_,_,hevents⟩ := completed_zero_trace hw hc hm
  have ht : id.thread = (ctx 0 lane).id := hid.symm.trans hthread
  cases id with
  | mk thread serial =>
    dsimp only at ht
    subst thread
    rw [zero_candidate_event_at_lane]
    rwa [hevents] at hget

theorem reference_zero_event_to_completed {initial candidate id event}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    (he : zeroCandidate.eventAt id = some event) : candidate.eventAt id = some event := by
  obtain ⟨trace,hm,hid,hget⟩ := Unified.eventAt_trace he
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp hm
  have ht : id.thread = (ctx 0 lane).id := hid.symm
  cases id with
  | mk thread serial =>
    dsimp only at ht
    subst thread
    rw [completed_zero_event_at_lane hw hc]
    exact hget

theorem completed_zero_event_lookup {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    candidate.eventAt = zeroCandidate.eventAt := by
  funext id
  cases ha : candidate.eventAt id with
  | some event => exact (completed_zero_event_to_reference hw hc ha).symm
  | none =>
    cases hb : zeroCandidate.eventAt id with
    | none => rfl
    | some event => have hh := reference_zero_event_to_completed hw hc hb; rw [ha] at hh; cases hh

end
end Ptx.Kernels.HopperDoubleBuffer
