import Ptx.Kernels.HopperDoubleBufferResourceObservations

/-! Closed source-event serials, proved equal to interpreter-derived indices.
These formulas retain identity across resource reuse without inspecting real
payloads. They do not assert inventory completeness or memory admission. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def expectSerial (tile : Nat) : Nat := if tile = 0 then 5 else 10*tile-1
def copyASerial (tile : Nat) : Nat := if tile = 0 then 6 else 10*tile
def copyBSerial (tile : Nat) : Nat := if tile = 0 then 7 else 10*tile+1
def waitSerial (tile : Nat) (lane : Wgmma.Lane) : Nat := if HopperStage.leader lane then 8+10*tile else 2+7*tile
def invalSerial (tiles : Nat) (slot : Stage) : Nat := 10*tiles+11+slot.val

theorem data_expect_serial (a b tiles tile) (ht : tile < tiles) :
    (dataExpectId a b tiles tile).serial = expectSerial tile := by
  by_cases hz : tile = 0
  · simp [dataExpectId,expectSerial,hz]
  · simp only [dataExpectId,expectSerial,hz,ite_false]
    rw [data_tile_start_value a b tiles (tile-1) 0 (by omega)]
    change 8+10*(tile-1)+1 = 10*tile-1
    omega

theorem data_copy_a_serial (a b tiles tile) (ht : tile < tiles) :
    (dataCopyAId a b tiles tile).issue.serial = copyASerial tile := by
  by_cases hz : tile = 0
  · simp [dataCopyAId,copyASerial,hz]
  · simp only [dataCopyAId,copyASerial,hz,ite_false]
    rw [data_tile_start_value a b tiles (tile-1) 0 (by omega)]
    change 8+10*(tile-1)+2 = 10*tile
    omega

theorem data_copy_b_serial (a b tiles tile) (ht : tile < tiles) :
    (dataCopyBId a b tiles tile).issue.serial = copyBSerial tile := by
  by_cases hz : tile = 0
  · simp [dataCopyBId,copyBSerial,hz]
  · simp only [dataCopyBId,copyBSerial,hz,ite_false]
    rw [data_tile_start_value a b tiles (tile-1) 0 (by omega)]
    change 8+10*(tile-1)+3 = 10*tile+1
    omega

theorem data_wait_serial (a b tiles tile lane) (ht : tile < tiles) :
    (dataWaitId a b tiles tile lane).serial = waitSerial tile lane :=
  data_tile_start_value a b tiles tile lane ht

theorem data_loop_full_length (a b tiles lane) :
    (dataLoopEvents a b tiles lane tiles).length =
      if HopperStage.leader lane then (if tiles = 0 then 0 else 10*tiles-3) else 7*tiles := by
  cases tiles with
  | zero => cases HopperStage.leader lane <;> rfl
  | succ n =>
    have he : dataLoopEvents a b (n+1) lane (n+1) =
        dataLoopEvents a b (n+1) lane n++dataIterationEvents a b (n+1) n lane := by
      simp only [dataLoopEvents,loopEvents,dataIterationEvents,dataCheckpoint,Nat.zero_add,zeroRetries]
    rw [he,List.length_append,data_loop_prefix_length a b (n+1) lane n (by omega),data_iteration_length]
    cases hl : HopperStage.leader lane <;> simp [dataPreludeLength,needsPrefetch,hl] <;> omega

theorem data_producer_pre_output_length (a b tiles) : (dataPreOutputEvents a b tiles 0).length = 10*tiles+5 := by
  by_cases hz : tiles = 0
  · subst tiles
    rfl
  · simp only [dataPreOutputEvents,hz,ite_false,dataKernelLoopEvents,List.length_append,data_loop_full_length]
    change 8+(10*tiles-3) = 10*tiles+5
    omega

theorem data_inval_serial (a b tiles slot) : (dataInvalId a b tiles slot).serial = invalSerial tiles slot := by
  simp only [dataInvalId,invalSerial,data_producer_pre_output_length]

def resourceLane (id : ThreadId) : Nat := id.tid.x+4*(id.tid.y+8*id.tid.z)
theorem resource_lane_value (tiles lane) : resourceLane (ctx tiles lane).id = lane.val := by
  change Ampere.linearThread (HopperStage.ctx lane) = lane.val
  exact HopperStage.ctx_linear lane

theorem resource_ctx_injective (tiles) : Function.Injective (fun lane : Wgmma.Lane => (ctx tiles lane).id) := by
  intro left right he
  apply Fin.ext
  have hh := congrArg resourceLane he
  simpa only [resource_lane_value] using hh

theorem leader_iff_zero (lane : Wgmma.Lane) : HopperStage.leader lane = true ↔ lane = 0 := by
  change decide (lane.val = 0) = true ↔ lane = 0
  simp only [decide_eq_true_eq,Fin.ext_iff,Fin.val_zero]

theorem expect_serial_bounds (tile : Nat) : 2 < expectSerial tile ∧ expectSerial tile < 8+10*tile := by
  by_cases hz : tile = 0 <;> simp [expectSerial,hz]
  omega

theorem expect_serial_strict_mono : StrictMono expectSerial := by
  intro left right h
  by_cases hl : left = 0 <;> by_cases hr : right = 0 <;> simp [expectSerial,hl,hr] <;> omega

end
end Ptx.Kernels.HopperDoubleBuffer
