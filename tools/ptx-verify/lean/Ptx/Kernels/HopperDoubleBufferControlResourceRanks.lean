import Ptx.Kernels.HopperDoubleBufferControlClock

/-! Closed global-control ranks of the actual resource origins. These ranks
respect source identities and leave room for all implicit TMA access stages. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def originControlRank (tiles : Nat) (origin : Tma.Origin) : Nat := controlRank tiles origin.node

theorem producer_expect_tick (tiles tile) (ht : tile < tiles) : producerTick tiles (expectSerial tile) = expectSerial tile := by
  apply producer_tick_before
  have htpos : tiles ≠ 0 := by omega
  by_cases hz : tile = 0 <;> simp only [expectSerial,producerThreshold,htpos,hz,ite_true,ite_false] <;> omega

theorem producer_copy_a_tick (tiles tile) (ht : tile < tiles) : producerTick tiles (copyASerial tile) = copyASerial tile := by
  apply producer_tick_before
  have htpos : tiles ≠ 0 := by omega
  by_cases hz : tile = 0 <;> simp only [copyASerial,producerThreshold,htpos,hz,ite_true,ite_false] <;> omega

theorem producer_copy_b_tick (tiles tile) (ht : tile < tiles) : producerTick tiles (copyBSerial tile) = copyBSerial tile := by
  apply producer_tick_before
  have htpos : tiles ≠ 0 := by omega
  by_cases hz : tile = 0 <;> simp only [copyBSerial,producerThreshold,htpos,hz,ite_true,ite_false] <;> omega

theorem data_init_control_rank (tiles slot) :
    sourceControlRank tiles (dataInitId tiles slot) = 1024*slot.val := by
  change 1024*sourceTick tiles (resourceLane (ctx tiles 0).id) slot.val+resourceLane (ctx tiles 0).id = _
  rw [resource_lane_value]
  simp only [Fin.val_zero,sourceTick,ite_true,Nat.add_zero]
  rw [producer_initial_tick tiles slot.val (by have := slot.isLt; omega)]

theorem data_expect_control_rank (a b tiles tile) (ht : tile < tiles) :
    sourceControlRank tiles (dataExpectId a b tiles tile) = 1024*expectSerial tile := by
  change 1024*sourceTick tiles (resourceLane (ctx tiles 0).id) (dataExpectId a b tiles tile).serial+resourceLane (ctx tiles 0).id = _
  rw [resource_lane_value,data_expect_serial a b tiles tile ht]
  simp only [Fin.val_zero,sourceTick,ite_true,Nat.add_zero]
  rw [producer_expect_tick tiles tile ht]

theorem data_copy_a_control_rank (a b tiles tile) (ht : tile < tiles) :
    sourceControlRank tiles (dataCopyAId a b tiles tile).issue = 1024*copyASerial tile := by
  change 1024*sourceTick tiles (resourceLane (ctx tiles 0).id) (dataCopyAId a b tiles tile).issue.serial+resourceLane (ctx tiles 0).id = _
  rw [resource_lane_value,data_copy_a_serial a b tiles tile ht]
  simp only [Fin.val_zero,sourceTick,ite_true,Nat.add_zero]
  rw [producer_copy_a_tick tiles tile ht]

theorem data_copy_b_control_rank (a b tiles tile) (ht : tile < tiles) :
    sourceControlRank tiles (dataCopyBId a b tiles tile).issue = 1024*copyBSerial tile := by
  change 1024*sourceTick tiles (resourceLane (ctx tiles 0).id) (dataCopyBId a b tiles tile).issue.serial+resourceLane (ctx tiles 0).id = _
  rw [resource_lane_value,data_copy_b_serial a b tiles tile ht]
  simp only [Fin.val_zero,sourceTick,ite_true,Nat.add_zero]
  rw [producer_copy_b_tick tiles tile ht]

theorem data_wait_control_rank (a b tiles tile lane) (ht : tile < tiles) :
    sourceControlRank tiles (dataWaitId a b tiles tile lane) = 1024*(8+10*tile)+lane.val := by
  change 1024*sourceTick tiles (resourceLane (ctx tiles lane).id) (dataWaitId a b tiles tile lane).serial+resourceLane (ctx tiles lane).id = _
  rw [resource_lane_value,data_wait_serial a b tiles tile lane ht]
  by_cases hz : lane.val = 0 <;>
    simp only [sourceTick,waitSerial,HopperStage.leader,decide_eq_true_eq,hz,ite_true,ite_false,
      producer_wait_tick tiles tile ht,peer_wait_tick tiles tile ht]

theorem data_inval_control_rank (a b tiles slot) :
    sourceControlRank tiles (dataInvalId a b tiles slot) = 1024*(10*tiles+14+slot.val) := by
  change 1024*sourceTick tiles (resourceLane (ctx tiles 0).id) (dataInvalId a b tiles slot).serial+resourceLane (ctx tiles 0).id = _
  rw [resource_lane_value,data_inval_serial]
  simp only [sourceTick,Fin.val_zero,ite_true,Nat.add_zero,invalSerial]
  have he : 10*tiles+11+slot.val = 10*tiles+5+(6+slot.val) := by omega
  rw [he,producer_tail_tick]
  congr 1
  omega

def phaseRank (tile index : Nat) : Nat :=
  if index = 0 then 1024*expectSerial tile else
  if index = 1 then 1024*copyASerial tile+512 else
  if index = 2 then 1024*copyBSerial tile+512 else 1024*(8+10*tile)+(index-3)

theorem phase_rank_strict (tile left right : Nat) (hl : left < right) (hr : right < 131) :
    phaseRank tile left < phaseRank tile right := by
  by_cases hz : tile = 0 <;> simp only [phaseRank,expectSerial,copyASerial,copyBSerial,hz,ite_true,ite_false]
  all_goals split_ifs <;> omega

theorem phase_rank_bounds (tile index : Nat) (hi : index < 131) :
    1024*expectSerial tile ≤ phaseRank tile index ∧ phaseRank tile index ≤ 1024*(8+10*tile)+127 := by
  by_cases hz : tile = 0 <;> simp only [phaseRank,expectSerial,copyASerial,copyBSerial,hz,ite_true,ite_false]
  all_goals split_ifs <;> omega

theorem phase_control_gap (tile next : Nat) (hn : tile+2 ≤ next) :
    1024*(8+10*tile)+127 < 1024*expectSerial next := by
  have hz : next ≠ 0 := by omega
  simp only [expectSerial,hz,ite_false]
  omega

end
end Ptx.Kernels.HopperDoubleBuffer
