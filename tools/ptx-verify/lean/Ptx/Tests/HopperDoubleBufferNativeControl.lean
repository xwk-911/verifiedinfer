import Ptx.Kernels.HopperDoubleBufferNativeControl
import Ptx.Hopper.UnifiedControlCheck
import Ptx.Tests.HopperDoubleBufferData

/-! Actual repeated native schedules, warp-local rendezvous and increasing
control ranks. Corrupted schedules are metadata-only negative fixtures; no
source/memory admission is asserted for the corrupted candidates. -/
namespace Ptx.HopperDoubleBufferNativeControlTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

abbrev a := HopperDoubleBufferDataTests.a
abbrev b := HopperDoubleBufferDataTests.b
def signatureAt (tiles tile : Nat) (lane : Wgmma.Lane) (index : Fin 4) :=
  (dataCompleteCandidate a b tiles).nativeSignatureAt (dataNativeId a b tiles tile lane index)
def syncCheck (tiles leftTile : Nat) (left : Wgmma.Lane) (li : Fin 4)
    (rightTile : Nat) (right : Wgmma.Lane) (ri : Fin 4) : Bool :=
  Unified.checkNativeSync HopperStage.block (dataCompleteCandidate a b tiles)
    (dataNativeId a b tiles leftTile left li) (dataNativeId a b tiles rightTile right ri)
def syncMetadata (tiles leftTile : Nat) (left : Wgmma.Lane) (li : Fin 4)
    (rightTile : Nat) (right : Wgmma.Lane) (ri : Fin 4) : Bool :=
  decide (Unified.SamePhysicalWarp HopperStage.block (ctx tiles left).id (ctx tiles right).id) &&
    (dataNativeSignature leftTile li == dataNativeSignature rightTile ri)
theorem sync_metadata_correct (tiles leftTile : Nat) (left : Wgmma.Lane) (li : Fin 4)
    (rightTile : Nat) (right : Wgmma.Lane) (ri : Fin 4) (hl : leftTile < tiles) (hr : rightTile < tiles) :
    syncCheck tiles leftTile left li rightTile right ri = syncMetadata tiles leftTile left li rightTile right ri := by
  unfold syncCheck Unified.checkNativeSync
  rw [data_actual_native_signature a b tiles leftTile left hl li,data_actual_native_signature a b tiles rightTile right hr ri]
  rfl
def isLastWait (event : Wgmma.Event) : Bool := match event with | .wait mark _ _ _ _ _ => mark.sequence == 11 | _ => false
def missingWaitTrace (lane : Wgmma.Lane) : Unified.ThreadTrace :=
  if lane.val = 31 then {dataCompleteTrace a b 3 lane with events := (dataCompleteTrace a b 3 lane).events.filter (fun e => !isLastWait e)}
  else dataCompleteTrace a b 3 lane
def missingWait : Unified.Candidate := ⟨List.ofFn missingWaitTrace⟩
def missingLane : Unified.Candidate := ⟨(dataCompleteCandidate a b 3).traces.filter
  (fun trace => trace.id.tid.linear HopperStage.block != 127)⟩
def participantMetadata (leftTiles : Nat) (left : Wgmma.Lane) (rightTiles : Nat) (right lane : Wgmma.Lane) : Bool :=
  (ctx rightTiles right).id.cta == (ctx leftTiles left).id.cta &&
  Ampere.linearThread (ctx rightTiles right) == 128*(Ampere.linearThread (ctx leftTiles left)/128)+lane.val &&
  ((dataNativeSchedule rightTiles).map Wgmma.alignedSignature == (dataNativeSchedule leftTiles).map Wgmma.alignedSignature)
theorem participant_metadata_correct (leftTiles : Nat) (left : Wgmma.Lane) (rightTiles : Nat) (right lane : Wgmma.Lane) :
    Unified.participantMatches HopperStage.block (dataCompleteTrace a b leftTiles left) (dataCompleteTrace a b rightTiles right) lane =
      participantMetadata leftTiles left rightTiles right lane := by
  simp only [Unified.participantMatches,Unified.ThreadTrace.alignedSchedule,data_complete_native_schedule]
  rfl

theorem schedule_lengths :
    (dataCompleteTrace a b 0 0).nativeSchedule.length = 0 ∧
    (dataCompleteTrace a b 1 127).nativeSchedule.length = 4 ∧
    (dataCompleteTrace a b 3 0).nativeSchedule.length = 12 ∧
    (dataCompleteTrace a b 5 127).nativeSchedule.length = 20 := by
  simp only [data_complete_native_schedule,data_native_schedule_length]
  decide
theorem final_native_signature : signatureAt 3 2 127 3 = some (dataNativeSignature 2 3) :=
  data_actual_native_signature a b 3 2 127 (by decide) 3
theorem twice_reused_signature : signatureAt 5 4 0 1 = some (dataNativeSignature 4 1) :=
  data_actual_native_signature a b 5 4 0 (by decide) 1
theorem same_warp_fence_syncs : syncCheck 3 0 0 0 0 31 0 = true := by
  rw [sync_metadata_correct _ _ _ _ _ _ _ (by decide) (by decide)]; decide
theorem second_warp_mma_syncs : syncCheck 3 1 32 1 1 63 1 = true := by
  rw [sync_metadata_correct _ _ _ _ _ _ _ (by decide) (by decide)]; decide
theorem final_warp_wait_syncs : syncCheck 5 4 96 3 4 127 3 = true := by
  rw [sync_metadata_correct _ _ _ _ _ _ _ (by decide) (by decide)]; decide
theorem different_warps_do_not_sync : syncCheck 3 0 0 0 0 32 0 = false := by
  rw [sync_metadata_correct _ _ _ _ _ _ _ (by decide) (by decide)]; decide
theorem different_rounds_do_not_sync : syncCheck 3 0 0 1 2 31 1 = false := by
  rw [sync_metadata_correct _ _ _ _ _ _ _ (by decide) (by decide)]; decide
theorem different_instructions_do_not_sync : syncCheck 3 1 0 0 1 31 1 = false := by
  rw [sync_metadata_correct _ _ _ _ _ _ _ (by decide) (by decide)]; decide
theorem no_native_signature_on_zero_path : signatureAt 0 0 0 0 = none := by decide
theorem final_prefetch_gap_preserves_native_ticks :
    nativeTick 3 (dataNativeId a b 3 2 0 0) = 32 ∧ nativeTick 3 (dataNativeId a b 3 2 127 3) = 35 := by
  rw [data_native_id_tick a b 3 2 0 (by decide) 0,data_native_id_tick a b 3 2 127 (by decide) 3]; decide
theorem arrival_precedes_low_lane_return :
    dataNativeControlRank 3 (.arrival (dataNativeId a b 3 0 31 1)) = 26623 ∧
    dataNativeControlRank 3 (.base (.source (dataNativeId a b 3 0 0 1))) = 26624 := by
  change 2*(1024*nativeTick 3 (dataNativeId a b 3 0 31 1))-1 = 26623 ∧ 2*sourceControlRank 3 (dataNativeId a b 3 0 0 1) = 26624
  rw [data_native_id_tick a b 3 0 31 (by decide) 1,data_native_id_control_rank a b 3 0 0 (by decide) 1]; decide
theorem operand_between_issue_and_wait :
    dataNativeControlRank 3 (.operand (dataNativeId a b 3 0 0 1) (.a (0,0) 0)) = 26880 ∧
    dataNativeControlRank 3 (.base (.source (dataNativeId a b 3 0 0 3))) = 30720 := by
  change 2*(1024*nativeTick 3 (dataNativeId a b 3 0 0 1)+128) = 26880 ∧ 2*sourceControlRank 3 (dataNativeId a b 3 0 0 3) = 30720
  rw [data_native_id_tick a b 3 0 0 (by decide) 1,data_native_id_control_rank a b 3 0 0 (by decide) 3]; decide
theorem highest_lane_return_precedes_operand :
    dataNativeControlRank 5 (.base (.source (dataNativeId a b 5 4 127 1))) = 108798 ∧
    dataNativeControlRank 5 (.operand (dataNativeId a b 5 4 127 1) (.b (15,7) 1)) = 108800 := by
  change 2*sourceControlRank 5 (dataNativeId a b 5 4 127 1) = 108798 ∧ 2*(1024*nativeTick 5 (dataNativeId a b 5 4 127 1)+128) = 108800
  rw [data_native_id_control_rank a b 5 4 127 (by decide) 1,data_native_id_tick a b 5 4 127 (by decide) 1]; decide
theorem missing_wait_trace_linear (lane : Wgmma.Lane) : (missingWaitTrace lane).linear HopperStage.block = lane.val := by
  unfold missingWaitTrace
  split_ifs <;> change Ampere.linearThread (HopperStage.ctx lane) = lane.val <;> exact HopperStage.ctx_linear lane
theorem missing_native_wait_rejected : Unified.checkSchedules HopperStage.block missingWait = false := by
  cases h : Unified.checkSchedules HopperStage.block missingWait with
  | false => rfl
  | true =>
    exfalso
    have hzero : dataCompleteTrace a b 3 0 ∈ missingWait.traces := List.mem_ofFn.mpr ⟨0,rfl⟩
    obtain ⟨peer,hp,_,hlinear,hschedule⟩ := Unified.schedules_have_all_participants h hzero (by decide) 31
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp hp
    rw [missing_wait_trace_linear] at hlinear
    change lane.val = 128*(0/128)+31 at hlinear
    have hlane : lane = (31 : Wgmma.Lane) := Fin.ext (by omega)
    subst lane
    have hm := congrArg List.length hschedule
    have hshort : (missingWaitTrace 31).alignedSchedule.length = 11 := by decide
    have hfull : (dataCompleteTrace a b 3 0).alignedSchedule.length = 12 := by decide
    omega
theorem missing_participant_rejected : Unified.checkSchedules HopperStage.block missingLane = false := by
  cases h : Unified.checkSchedules HopperStage.block missingLane with
  | false => rfl
  | true =>
    exfalso
    have hzero : dataCompleteTrace a b 3 0 ∈ missingLane.traces :=
      List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨0,rfl⟩,by decide⟩
    obtain ⟨peer,hp,_,hlinear,_⟩ := Unified.schedules_have_all_participants h hzero (by decide) 127
    have hkeep := (List.mem_filter.mp hp).2
    change peer.linear HopperStage.block = 128*(0/128)+127 at hlinear
    have hlin : peer.id.tid.linear HopperStage.block = 127 := by exact hlinear
    have hn : ((127 : Nat) != 127) ≠ true := by decide
    exact hn (by simpa only [hlin] using hkeep)
theorem shorter_actual_schedule_mismatches :
    Unified.participantMatches HopperStage.block (dataCompleteTrace a b 3 0) (dataCompleteTrace a b 2 31) 31 = false := by
  simp only [Unified.participantMatches,Unified.ThreadTrace.alignedSchedule,data_complete_native_schedule]
  decide
theorem full_actual_schedule_matches :
    Unified.participantMatches HopperStage.block (dataCompleteTrace a b 5 0) (dataCompleteTrace a b 5 127) 127 = true := by
  simp only [Unified.participantMatches,Unified.ThreadTrace.alignedSchedule,data_complete_native_schedule]
  decide

theorem arbitrary_real_native_control (x : TileA) (y : TileB) (tiles : Nat) (hb : tiles ≤ 2^28) :
    Unified.ControlAdmitted HopperStage.block (dataCompleteCandidate x y tiles) (dataHistories x y tiles) :=
  data_native_control_admitted x y tiles hb
theorem empty_native_control : Unified.ControlAdmitted HopperStage.block (dataCompleteCandidate a b 0) (dataHistories a b 0) :=
  data_native_control_admitted a b 0 (by decide)
theorem repeated_native_control : Unified.ControlAdmitted HopperStage.block (dataCompleteCandidate a b 5) (dataHistories a b 5) :=
  data_native_control_admitted a b 5 (by decide)

theorem all_actual_warp_pcs (x : TileA) (y : TileB) (tiles tile : Nat) (hb : tiles ≤ 2^28) (ht : tile < tiles)
    (who : Wgmma.Lane) (index : Fin 4) (lane : Fin 32) :
    ∃ other, Unified.NativeSync HopperStage.block (dataCompleteCandidate x y tiles) other (dataNativeId x y tiles tile who index) ∧
      (dataCompleteCandidate x y tiles).sourcePC code (params tiles) HopperStage.block other = some (dataNativeSignature tile index).pc :=
  Unified.synced_participants_source_pc (data_source_well_formed x y tiles (fun _ => .bits (byte 0)) hb)
    (data_native_schedules_admitted x y tiles) (data_actual_native_signature x y tiles tile who ht index) lane

theorem native_finish_is_source_backed (x : TileA) (y : TileB) (tiles : Nat) (hb : tiles ≤ 2^28)
    (issue wait : Ptx.Event.EventId) (operand : Wgmma.OperandByte)
    (he : Unified.NativeFinish (dataCompleteCandidate x y tiles) (.operand issue operand) (.base (.source wait))) :
    dataNativeControlRank tiles (.operand issue operand) < dataNativeControlRank tiles (.base (.source wait)) :=
  data_native_finish_rank hb he

theorem actual_rendezvous_reversal_rejected :
    ¬Ptx.Event.Path (Unified.ControlEdge HopperStage.block (dataCompleteCandidate a b 3) (dataHistories a b 3))
      (.base (.source (dataNativeId a b 3 0 0 1))) (.arrival (dataNativeId a b 3 0 31 1)) := by
  intro hp
  have hh := hp.rank_lt (dataNativeControlRank 3) (fun _ _ => data_native_control_edge_rank (by decide))
  have hr := arrival_precedes_low_lane_return
  omega

end
end Ptx.HopperDoubleBufferNativeControlTests
