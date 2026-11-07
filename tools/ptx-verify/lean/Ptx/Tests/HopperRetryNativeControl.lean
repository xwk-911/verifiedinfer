import Ptx.Kernels.HopperDoubleBufferRetryNativeCases
import Ptx.Hopper.UnifiedControlParticipants
import Ptx.Hopper.UnifiedControlCheck
import Ptx.Tests.HopperRetryAdmission

/-! Actual native participants and source-PC linkage with heterogeneous failed
waits. These are positive participation components and negative rendezvous/
coverage tests, not combined-control or full-memory execution witnesses. The
existing fixture remains memory-negative and keeps arbitrary matrix replies. -/
namespace Ptx.HopperRetryNativeControlTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev family := HopperRetryAdmissionTests.family
abbrev candidate := HopperRetryAdmissionTests.candidate
abbrev source := HopperRetryAdmissionTests.source_well_formed

theorem all_actual_schedules (value : ℝ) : Unified.SchedulesAdmitted HopperStage.block (candidate value) :=
  retry_native_schedules_admitted (family value) (source value (fun _ => .bits (byte 0)))

theorem retry_independent_signature_sequence (value : ℝ) (lane : Wgmma.Lane) :
    ((family value).traces lane).nativeSchedule = dataNativeSchedule 3 := retry_family_native_schedule (family value) lane

theorem actual_native_indices (value : ℝ) :
    ((family value).nativeId 0 0 0).serial = 13 ∧ ((family value).nativeId 0 0 3).serial = 16 ∧
    ((family value).nativeId 2 2 0).serial = 29 ∧ ((family value).nativeId 2 2 3).serial = 32 := ⟨rfl,rfl,rfl,rfl⟩

theorem all_native_events_classified (value : ℝ) (id : Ptx.Event.EventId) (signature : Wgmma.SourceSignature)
    (he : (candidate value).nativeSignatureAt id = some signature) :
    ∃ tile lane index, tile < 3 ∧ id = (family value).nativeId tile lane index ∧ signature = dataNativeSignature tile index :=
  retry_native_signature_shape (family value) (source value (fun _ => .bits (byte 0))) he

theorem all_aligned_participants_actual (value : ℝ) (tile : Fin 3) (who : Wgmma.Lane) (index : Fin 4) (lane : Wgmma.Lane) :
    ∃ other, other.thread.cta = ((family value).nativeId tile who index).thread.cta ∧
      other.thread.tid.linear HopperStage.block = 128*(((family value).nativeId tile who index).thread.tid.linear HopperStage.block/128)+lane.val ∧
      (candidate value).nativeSignatureAt other = some (dataNativeSignature tile index) :=
  Unified.aligned_participant_event (source value (fun _ => .bits (byte 0))).2.1 (all_actual_schedules value)
    (retry_actual_native_signature (family value) (source value (fun _ => .bits (byte 0))) tile tile.isLt who index) lane

theorem all_warp_participant_source_pcs (value : ℝ) (tile : Fin 3) (who : Wgmma.Lane) (index : Fin 4) (lane : Fin 32) :
    ∃ other, Unified.NativeSync HopperStage.block (candidate value) other ((family value).nativeId tile who index) ∧
      (candidate value).sourcePC code (params 3) HopperStage.block other = some (76+index.val) := by
  obtain ⟨other,hs,hpc⟩ := Unified.synced_participants_source_pc (source value (fun _ => .bits (byte 0))) (all_actual_schedules value)
    (retry_actual_native_signature (family value) (source value (fun _ => .bits (byte 0))) tile tile.isLt who index) lane
  exact ⟨other,hs,hpc.trans (congrArg some (data_native_signature_pc tile index))⟩

theorem same_warp_matches_actual_instruction (value : ℝ) (tile : Fin 3) (index : Fin 4) :
    Unified.NativeSync HopperStage.block (candidate value) ((family value).nativeId tile 0 index) ((family value).nativeId tile 31 index) :=
  ⟨by change Unified.SamePhysicalWarp HopperStage.block (ctx 3 0).id (ctx 3 31).id; decide,dataNativeSignature tile index,
    retry_actual_native_signature (family value) (source value (fun _ => .bits (byte 0))) tile tile.isLt 0 index,
    retry_actual_native_signature (family value) (source value (fun _ => .bits (byte 0))) tile tile.isLt 31 index⟩

theorem other_warp_rejected (value : ℝ) (tile : Fin 3) (index : Fin 4) :
    ¬Unified.NativeSync HopperStage.block (candidate value) ((family value).nativeId tile 0 index) ((family value).nativeId tile 32 index) :=
  Unified.different_warps_no_native_sync (by change (0 : Nat)/32 ≠ 32/32; decide)

theorem other_instruction_rejected (value : ℝ) (tile : Fin 3) :
    ¬Unified.NativeSync HopperStage.block (candidate value) ((family value).nativeId tile 0 0) ((family value).nativeId tile 31 1) := by
  apply Unified.different_signatures_no_native_sync
    (retry_actual_native_signature (family value) (source value (fun _ => .bits (byte 0))) tile tile.isLt 0 0)
    (retry_actual_native_signature (family value) (source value (fun _ => .bits (byte 0))) tile tile.isLt 31 1)
  intro he
  have hh := congrArg Fin.val (data_native_signature_identity tile tile 0 1 he).2
  omega

theorem reused_stage_other_tile_rejected (value : ℝ) :
    ¬Unified.NativeSync HopperStage.block (candidate value) ((family value).nativeId 0 0 0) ((family value).nativeId 2 31 0) := by
  apply Unified.different_signatures_no_native_sync
    (retry_actual_native_signature (family value) (source value (fun _ => .bits (byte 0))) 0 (by decide) 0 0)
    (retry_actual_native_signature (family value) (source value (fun _ => .bits (byte 0))) 2 (by decide) 31 0)
  intro he
  have hh := (data_native_signature_identity 0 2 0 0 he).1
  omega

theorem earlier_wait_cannot_complete_later_group (value : ℝ) (lane : Wgmma.Lane) :
    ¬Unified.WgmmaCompletedAt (candidate value) ((family value).mmaId 2 0) ((family value).nativeWaitId 0 lane) := by
  rintro ⟨collective,actual,mark,groups,keep,before,after,query,hwait,_,_,_,_,hg,_,_,_⟩
  have hi : (candidate value).eventAt ((family value).mmaId 2 0) = some (.mma (collective.marks 0) (collective.calls 0)) := by
    simpa only [collective.representative] using collective.matched 0
  have hm := family_mma_at (family value) (source value (fun _ => .bits (byte 0))) 2 (by decide) 0
  have hcall := (Wgmma.Event.mma.inj (Option.some.inj (hi.symm.trans hm))).2
  have hgroup : (collective.calls 0).group = 2 := by
    rw [hcall]
    exact reply_call_group _ _ _ _ _
  have hw := family_native_wait_at (family value) (source value (fun _ => .bits (byte 0))) (by decide) 0 (by decide) lane
  have ha : after = 1 := (Wgmma.Event.wait.inj (Option.some.inj (hwait.symm.trans hw))).2.2.2.2.1
  rw [collective.cohort.group actual,hgroup,ha] at hg
  omega

def singleLane (value : ℝ) : Unified.Candidate := ⟨[(family value).traces 0]⟩
theorem missing_participants_rejected (value : ℝ) : ¬Unified.SchedulesAdmitted HopperStage.block (singleLane value) := by
  intro hc
  have hn : ((family value).traces 0).nativeSchedule ≠ [] := by
    rw [retry_family_native_schedule]
    intro he
    have hh := congrArg List.length he
    rw [data_native_schedule_length] at hh
    norm_num at hh
  obtain ⟨peer,hp,_,hl,_⟩ := Unified.schedules_have_all_participants hc (by exact List.mem_singleton_self _) hn 1
  have he : peer = (family value).traces 0 := List.mem_singleton.mp hp
  rw [he] at hl
  change ((family value).traces 0).id.tid.linear HopperStage.block =
    128*(((family value).traces 0).id.tid.linear HopperStage.block/128)+1 at hl
  rw [(family value).ids 0] at hl
  change (0 : Nat) = 1 at hl
  omega

end
end Ptx.HopperRetryNativeControlTests
