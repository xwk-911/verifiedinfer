import Ptx.Kernels.HopperDoubleBufferDataSource

/-! Actual constructed call fields, arithmetic and represented operand values.
Call membership is tied to the complete source trace. Logical shared-tile
storage below is not a proved admitted shared heap or repeated RF/co history.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def dataIterationCall (a : TileA) (b : TileB) (tiles tile : Nat) (lane : Wgmma.Lane) : Wgmma.Call :=
  computeCall (ctx tiles lane) (dataOracle a b tiles lane)
    (preparedState (dataCheckpoint a b tiles lane tile).1 tile tiles 0 (HopperStage.leader lane))
    (aDescriptor (stage tile)) (bDescriptor (stage tile)) (dataCheckpoint a b tiles lane tile).2

def dataIterationMark (a : TileA) (b : TileB) (tiles tile : Nat) (lane : Wgmma.Lane) : Wgmma.Mark :=
  Wgmma.mark (ctx tiles lane) (computeFence (preparedState (dataCheckpoint a b tiles lane tile).1 tile tiles 0 (HopperStage.leader lane)))

theorem data_call_input (a b tiles tile lane) (ht : tile < tiles) (slot : Wgmma.Slot) :
    (dataIterationCall a b tiles tile lane).input slot = result a b tile (Wgmma.cCoord (lane,slot)) := by
  exact congrFun (data_checkpoint_values a b tiles lane tile (by omega)) slot

theorem data_call_output (a b tiles tile lane) (ht : tile < tiles) (slot : Wgmma.Slot) :
    (dataIterationCall a b tiles tile lane).output slot = result a b (tile+1) (Wgmma.cCoord (lane,slot)) := by
  change (dataOracle a b tiles lane).matrix
    (preparedState (dataCheckpoint a b tiles lane tile).1 tile tiles 0 (HopperStage.leader lane)).base.scalar.core.queries slot = _
  rw [data_prepared_native_query a b tiles lane tile ht]
  exact data_oracle_native_matrix a b tiles lane tile ht slot

theorem data_call_operands (a b tiles tile lane) (ht : tile < tiles) (offset : Nat) :
    (dataIterationCall a b tiles tile lane).operandBytes offset = Wgmma.payload (a tile) (b tile) offset := by
  change (dataOracle a b tiles lane).operands
    (preparedState (dataCheckpoint a b tiles lane tile).1 tile tiles 0 (HopperStage.leader lane)).base.scalar.core.queries offset = _
  rw [data_prepared_native_query a b tiles lane tile ht]
  exact data_oracle_native_operands a b tiles lane tile ht offset

theorem wrapped_a_descriptor (slot : Stage) : wrap 64 (aDescriptor slot) = aDescriptor slot := by fin_cases slot <;> decide
theorem wrapped_b_descriptor (slot : Stage) : wrap 64 (bDescriptor slot) = bDescriptor slot := by fin_cases slot <;> decide

theorem data_call_a (a b tiles tile lane) : (dataIterationCall a b tiles tile lane).a = aDescriptor (stage tile) := wrapped_a_descriptor _
theorem data_call_b (a b tiles tile lane) : (dataIterationCall a b tiles tile lane).b = bDescriptor (stage tile) := wrapped_b_descriptor _

theorem data_call_lane (a b tiles tile lane) : (dataIterationCall a b tiles tile lane).lane = lane := by
  apply Fin.ext
  change Ampere.linearThread (ctx tiles lane)%128 = lane.val
  change Ampere.linearThread (HopperStage.ctx lane)%128 = lane.val
  rw [HopperStage.ctx_linear,Nat.mod_eq_of_lt lane.isLt]

theorem data_call_group (a b tiles tile lane) : (dataIterationCall a b tiles tile lane).group = tile := by
  change (preparedState (dataCheckpoint a b tiles lane tile).1 tile tiles 0 (HopperStage.leader lane)).ledger.groups = tile
  simp [dataCheckpoint,initialLoopState]

theorem data_call_ordinal (a b tiles tile lane) : (dataIterationCall a b tiles tile lane).ordinal = tile := by
  have he : (preparedState (dataCheckpoint a b tiles lane tile).1 tile tiles 0 (HopperStage.leader lane)).ledger.calls =
      (dataCheckpoint a b tiles lane tile).1.ledger.calls :=
    congrArg (fun x => x.2.2.1) (preparedState_bookkeeping _ tile tiles 0 (HopperStage.leader lane))
  change (preparedState (dataCheckpoint a b tiles lane tile).1 tile tiles 0 (HopperStage.leader lane)).ledger.calls.length = tile
  rw [he]
  simp [dataCheckpoint,loopCheckpoint_call_count,initialLoopState]

theorem data_calls_cohort (a b tiles tile) : Wgmma.Cohort (dataIterationCall a b tiles tile) := {
  lane := data_call_lane a b tiles tile
  a := fun _ => (data_call_a _ _ _ _ _).trans (data_call_a _ _ _ _ _).symm
  b := fun _ => (data_call_b _ _ _ _ _).trans (data_call_b _ _ _ _ _).symm
  d := fun _ => rfl
  ordinal := fun _ => (data_call_ordinal _ _ _ _ _).trans (data_call_ordinal _ _ _ _ _).symm
  group := fun _ => (data_call_group _ _ _ _ _).trans (data_call_group _ _ _ _ _).symm
}

theorem data_calls_arithmetic (a b tiles tile) (ht : tile < tiles) :
    Wgmma.Arithmetic (a tile) (b tile) (fun p => (dataIterationCall a b tiles tile p.1).input p.2)
      (fun p => (dataIterationCall a b tiles tile p.1).output p.2) := by
  intro p
  have hin : (fun p => (dataIterationCall a b tiles tile p.1).input p.2) = Wgmma.gatherC (result a b tile) := by
    funext q
    exact data_call_input a b tiles tile q.1 ht q.2
  change (dataIterationCall a b tiles tile p.1).output p.2 = Wgmma.results (a tile) (b tile) (fun q => (dataIterationCall a b tiles tile q.1).input q.2) p
  rw [data_call_output a b tiles tile p.1 ht p.2,hin]
  exact (tile_reply_value a b tile p).symm

theorem data_call_input_values (a b tiles tile lane) (ht : tile < tiles) :
    Wgmma.InputValues (dataIterationCall a b tiles tile lane) (a tile) (b tile) := by
  constructor
  · intro p byte
    rw [data_call_operands a b tiles tile lane ht]
    exact Wgmma.payload_a _ _ _ _
  · intro p byte
    rw [data_call_operands a b tiles tile lane ht]
    exact Wgmma.payload_b _ _ _ _

theorem data_iteration_has_call (a b tiles tile lane) :
    .mma (dataIterationMark a b tiles tile lane) (dataIterationCall a b tiles tile lane) ∈
      iterationEvents (ctx tiles lane) (dataOracle a b tiles lane) (dataCheckpoint a b tiles lane tile).1 tile tiles 0
        (HopperStage.leader lane) 4096 4224 (dataCheckpoint a b tiles lane tile).2 := by
  simp [iterationEvents,computeEvents,dataIterationMark,dataIterationCall]

theorem data_loop_event_retained (a b tiles lane) (event : Wgmma.Event) (m n : Nat) (hle : m ≤ n)
    (hm : event ∈ dataLoopEvents a b tiles lane m) : event ∈ dataLoopEvents a b tiles lane n := by
  induction n with
  | zero =>
    have he : m = 0 := by omega
    simpa only [he] using hm
  | succ n ih =>
    by_cases he : m = n+1
    · simpa [he] using hm
    · have hold := ih (by omega)
      unfold dataLoopEvents at hold ⊢
      rw [loopEvents]
      exact List.mem_append_left _ hold

theorem data_complete_has_call (a b tiles tile lane) (ht : tile < tiles) :
    .mma (dataIterationMark a b tiles tile lane) (dataIterationCall a b tiles tile lane) ∈ dataCompleteEvents a b tiles lane := by
  have hstep : .mma (dataIterationMark a b tiles tile lane) (dataIterationCall a b tiles tile lane) ∈ dataLoopEvents a b tiles lane (tile+1) := by
    simp only [dataLoopEvents,loopEvents,Nat.zero_add]
    exact List.mem_append_right _ (data_iteration_has_call a b tiles tile lane)
  have hfull := data_loop_event_retained a b tiles lane _ (tile+1) tiles (by omega) hstep
  have hpos : tiles ≠ 0 := by omega
  simp only [dataCompleteEvents,dataPreOutputEvents,hpos,ite_false,dataKernelLoopEvents,List.mem_append]
  exact Or.inl (Or.inr hfull)

end
end Ptx.Kernels.HopperDoubleBuffer
