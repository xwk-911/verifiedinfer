import Ptx.Kernels.HopperDoubleBufferZeroInventory
import Ptx.Kernels.HopperDoubleBufferNativeControl
import Ptx.Kernels.HopperDoubleBufferRetryNativeSchedules
import Ptx.Kernels.HopperDoubleBufferRetryUnifiedControl
import Ptx.Hopper.UnifiedEventLookup
import Ptx.Hopper.UnifiedControlCheck

/-! Full construct control and resource/TMA components for every actual
source-well-formed completed zero-K candidate, with no canonical trace-order
or oracle premise. Source/event multiplicity is proved before history reuse. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def zeroHistories : Location → List Tma.Entry := dataHistories (fun _ _ => 0) (fun _ _ => 0) 0

theorem completed_zero_control_rank {initial candidate left right}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    (he : Unified.ControlEdge HopperStage.block candidate zeroHistories left right) :
    dataNativeControlRank 0 left < dataNativeControlRank 0 right :=
  data_native_control_edge_rank (a := fun _ _ => 0) (b := fun _ _ => 0) (tiles := 0) (by decide)
    (Unified.control_edge_lookup_transport (completed_zero_event_lookup hw hc) he)

theorem completed_zero_control_admitted {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    Unified.ControlAdmitted HopperStage.block candidate zeroHistories :=
  ⟨completed_candidate_native_schedules_admitted (by decide) hw hc,
    Unified.control_acyclic_of_rank (dataNativeControlRank 0) (fun _ _ => completed_zero_control_rank hw hc)⟩

theorem completed_zero_history_valid {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) (loc : Location) :
    Tma.HistoryValid Tma.localShared candidate.view loc (zeroHistories loc) :=
  Tma.history_lookup_transport (Unified.view_lookup_eq (completed_zero_event_lookup hw hc)).symm
    (completed_zero_event_ids_perm hw hc).symm (data_all_histories_valid (fun _ _ => 0) (fun _ _ => 0) 0 (by decide) loc)

theorem completed_zero_no_tma {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) (id : Tma.CopyId) :
    Tma.copyAt candidate.view id = none := by
  rw [Tma.copy_lookup_eq (Unified.view_lookup_eq (completed_zero_event_lookup hw hc))]
  cases he : Tma.copyAt zeroCandidate.view id with
  | none => rfl
  | some op =>
    obtain ⟨tile,ht,_⟩ := data_all_source_copies (fun _ _ => 0) (fun _ _ => 0) 0 (by decide) id op he
    omega

theorem completed_zero_native_signature_none {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) (id : Ptx.Event.EventId) :
    candidate.nativeSignatureAt id = none := by
  rw [Unified.native_signature_lookup_eq (completed_zero_event_lookup hw hc)]
  cases he : zeroCandidate.nativeSignatureAt id with
  | none => rfl
  | some signature =>
    obtain ⟨tile,lane,index,ht,_,_⟩ := data_native_signature_shape (a := fun _ _ => 0) (b := fun _ _ => 0) (tiles := 0) he
    omega

theorem completed_zero_representative_none {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) (id : Ptx.Event.EventId) :
    candidate.representativeAt id = none := by
  rw [Unified.representative_lookup_eq (completed_zero_event_lookup hw hc)]
  cases he : zeroCandidate.representativeAt id with
  | none => rfl
  | some pair =>
    obtain ⟨tile,lane,ht,_⟩ := data_native_mma_case (a := fun _ _ => 0) (b := fun _ _ => 0) (tiles := 0) (Unified.representative_at he).1
    omega

theorem completed_zero_descriptors {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    Tma.DescriptorAgreement candidate.view (dataMaps 0) := by
  intro id op he
  rw [completed_zero_no_tma hw hc] at he
  cases he

theorem completed_zero_tma_components {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    Unified.TmaComponents code (completeLaunch 0 initial) candidate Tma.localShared (dataMaps 0) zeroHistories := by
  refine ⟨hw,hc,completed_zero_descriptors hw hc,?_,completed_zero_history_valid hw hc,?_⟩
  · intro id op he
    rw [completed_zero_no_tma hw hc] at he
    cases he
  · exact Unified.native_control_keeps_base_acyclic (completed_zero_control_admitted hw hc)

theorem completed_candidate_control_exists {tiles initial candidate} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate) :
    ∃ histories, Unified.ControlAdmitted HopperStage.block candidate histories := by
  by_cases hz : tiles = 0
  · subst tiles
    exact ⟨zeroHistories,completed_zero_control_admitted hw hc⟩
  · obtain ⟨family,hcontrol⟩ := completed_positive_control_admitted (by omega) hb hw hc
    exact ⟨retryHistories family,hcontrol⟩

end
end Ptx.Kernels.HopperDoubleBuffer
