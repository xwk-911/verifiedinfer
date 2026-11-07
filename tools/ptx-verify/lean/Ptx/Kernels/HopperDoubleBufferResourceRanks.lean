import Ptx.Kernels.HopperDoubleBufferResourceSerials

/-! A recoverable resource-history position from actual origin metadata.
This is an identity/order proof device, not a GPU happens-before relation. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def sourcePosition (tiles : Nat) (slot : Stage) (lane serial : Nat) : Nat :=
  if serial ≤ 1 then 0 else
  if serial = invalSerial tiles slot then phaseStart (uses tiles slot) else
  if lane = 0 ∧ (serial = 5 ∨ serial%10 = 9) then
    phaseStart ((if serial = 5 then 0 else (serial+1)/10)/2)
  else phaseStart ((if lane = 0 then (serial-8)/10 else (serial-2)/7)/2)+3+lane

def notificationPosition (serial : Nat) : Nat :=
  phaseStart (serial/10/2)+(if serial = 7 ∨ serial%10 = 1 then 2 else 1)

def resourcePosition (tiles : Nat) (slot : Stage) : Tma.Origin → Nat
  | .source event => sourcePosition tiles slot (resourceLane event.thread) event.serial
  | .notification copy => notificationPosition copy.issue.serial

theorem init_position (tiles slot) : sourcePosition tiles slot 0 slot.val = 0 := by
  have := slot.isLt
  simp only [sourcePosition,ite_eq_left (by omega : slot.val ≤ 1)]

theorem inval_position (tiles slot) : sourcePosition tiles slot 0 (invalSerial tiles slot) = phaseStart (uses tiles slot) := by
  have h : ¬invalSerial tiles slot ≤ 1 := by dsimp [invalSerial]; omega
  simp [sourcePosition,h]

theorem expect_serial_tag (tile : Nat) : expectSerial tile = 5 ∨ expectSerial tile%10 = 9 := by
  by_cases hz : tile = 0 <;> simp [expectSerial,hz]
  omega

theorem expect_serial_decode (tile : Nat) :
    (if expectSerial tile = 5 then 0 else (expectSerial tile+1)/10) = tile := by
  by_cases hz : tile = 0
  · simp [expectSerial,hz]
  · have he : 10*tile-1 ≠ 5 := by omega
    simp only [expectSerial,ite_eq_right hz,ite_eq_right he]
    omega

theorem expect_position (tiles slot phase) (hp : phase < uses tiles slot) :
    sourcePosition tiles slot 0 (expectSerial (stageTile slot phase)) = phaseStart phase := by
  have ht := (stage_tile_in_range tiles slot phase).mpr hp
  have hs := slot.isLt
  have hb := expect_serial_bounds (stageTile slot phase)
  have hle : ¬expectSerial (stageTile slot phase) ≤ 1 := by omega
  have hne : expectSerial (stageTile slot phase) ≠ invalSerial tiles slot := by dsimp [invalSerial]; omega
  rw [sourcePosition,ite_eq_right hle,ite_eq_right hne,
    ite_eq_left (And.intro rfl (expect_serial_tag _)),expect_serial_decode]
  congr 1
  dsimp [stageTile]
  omega

theorem wait_position (tiles slot phase lane) (hp : phase < uses tiles slot) :
    sourcePosition tiles slot lane.val (waitSerial (stageTile slot phase) lane) = phaseStart phase+3+lane.val := by
  have ht := (stage_tile_in_range tiles slot phase).mpr hp
  have hs := slot.isLt
  have hl := lane.isLt
  simp only [sourcePosition,waitSerial,HopperStage.leader,decide_eq_true_eq,stageTile,invalSerial,phaseStart]
  split_ifs <;> omega

theorem copy_a_position (slot phase) : notificationPosition (copyASerial (stageTile slot phase)) = phaseStart phase+1 := by
  have hs := slot.isLt
  have hd : copyASerial (stageTile slot phase)/10 = stageTile slot phase := by
    by_cases hz : stageTile slot phase = 0 <;> simp [copyASerial,hz]
  have hn : ¬(copyASerial (stageTile slot phase) = 7 ∨ copyASerial (stageTile slot phase)%10 = 1) := by
    by_cases hz : stageTile slot phase = 0 <;> simp [copyASerial,hz]
    omega
  rw [notificationPosition,hd,ite_eq_right hn]
  have he : stageTile slot phase/2 = phase := by dsimp [stageTile]; omega
  rw [he]

theorem copy_b_position (slot phase) : notificationPosition (copyBSerial (stageTile slot phase)) = phaseStart phase+2 := by
  have hs := slot.isLt
  have hd : copyBSerial (stageTile slot phase)/10 = stageTile slot phase := by
    by_cases hz : stageTile slot phase = 0 <;> simp [copyBSerial,hz]
    all_goals omega
  have hn : copyBSerial (stageTile slot phase) = 7 ∨ copyBSerial (stageTile slot phase)%10 = 1 := by
    by_cases hz : stageTile slot phase = 0 <;> simp [copyBSerial,hz]
  rw [notificationPosition,hd,ite_eq_left hn]
  have he : stageTile slot phase/2 = phase := by dsimp [stageTile]; omega
  rw [he]

theorem data_init_position (tiles slot) : resourcePosition tiles slot (.source (dataInitId tiles slot)) = 0 := by
  change sourcePosition tiles slot (resourceLane (ctx tiles 0).id) slot.val = _
  rw [resource_lane_value]
  exact init_position tiles slot

theorem data_inval_position (a b tiles slot) :
    resourcePosition tiles slot (.source (dataInvalId a b tiles slot)) = phaseStart (uses tiles slot) := by
  change sourcePosition tiles slot (resourceLane (ctx tiles 0).id) (dataInvalId a b tiles slot).serial = _
  rw [resource_lane_value,data_inval_serial]
  exact inval_position tiles slot

theorem data_expect_position (a b tiles slot phase) (hp : phase < uses tiles slot) :
    resourcePosition tiles slot (.source (dataExpectId a b tiles (stageTile slot phase))) = phaseStart phase := by
  change sourcePosition tiles slot (resourceLane (ctx tiles 0).id) (dataExpectId a b tiles (stageTile slot phase)).serial = _
  rw [resource_lane_value,data_expect_serial a b tiles _ ((stage_tile_in_range tiles slot phase).mpr hp)]
  exact expect_position tiles slot phase hp

theorem data_wait_position (a b tiles slot phase lane) (hp : phase < uses tiles slot) :
    resourcePosition tiles slot (.source (dataWaitId a b tiles (stageTile slot phase) lane)) = phaseWaitIndex phase lane := by
  change sourcePosition tiles slot (resourceLane (ctx tiles lane).id) (dataWaitId a b tiles (stageTile slot phase) lane).serial = _
  rw [resource_lane_value,data_wait_serial a b tiles _ lane ((stage_tile_in_range tiles slot phase).mpr hp)]
  exact wait_position tiles slot phase lane hp

theorem data_copy_a_position (a b tiles slot phase) (hp : phase < uses tiles slot) :
    resourcePosition tiles slot (.notification (dataCopyAId a b tiles (stageTile slot phase))) = noticeAIndex phase := by
  change notificationPosition (dataCopyAId a b tiles (stageTile slot phase)).issue.serial = _
  rw [data_copy_a_serial a b tiles _ ((stage_tile_in_range tiles slot phase).mpr hp)]
  exact copy_a_position slot phase

theorem data_copy_b_position (a b tiles slot phase) (hp : phase < uses tiles slot) :
    resourcePosition tiles slot (.notification (dataCopyBId a b tiles (stageTile slot phase))) = noticeBIndex phase := by
  change notificationPosition (dataCopyBId a b tiles (stageTile slot phase)).issue.serial = _
  rw [data_copy_b_serial a b tiles _ ((stage_tile_in_range tiles slot phase).mpr hp)]
  exact copy_b_position slot phase

end
end Ptx.Kernels.HopperDoubleBuffer
