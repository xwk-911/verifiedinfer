import Ptx.Kernels.HopperDoubleBufferDataEntry
import Ptx.Kernels.HopperDoubleBufferKernelLoop

/-! Arbitrary-real source loop witness. Accumulator values at every checkpoint
are derived from source execution/read availability and the constructed WGMMA
arithmetic replies. This is not a universal admitted-kernel correctness theorem.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def dataCheckpoint (a : TileA) (b : TileB) (tiles : Nat) (lane : Wgmma.Lane) (n : Nat) : LoopCheckpoint :=
  loopCheckpoint (ctx tiles lane) (dataOracle a b tiles lane) 0 tiles (HopperStage.leader lane) zeroRetries
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) n

def dataLoopEvents (a : TileA) (b : TileB) (tiles : Nat) (lane : Wgmma.Lane) (n : Nat) : List Wgmma.Event :=
  loopEvents (ctx tiles lane) (dataOracle a b tiles lane) 0 tiles (HopperStage.leader lane) zeroRetries
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) 4096 4224 n

theorem data_checkpoint_query (a b tiles lane n) :
    (dataCheckpoint a b tiles lane n).1.base.scalar.core.queries =
      loopQuery 0 tiles (HopperStage.leader lane) zeroRetries (initialQuery (HopperStage.leader lane)) n := by
  simp only [dataCheckpoint,loopCheckpoint_queries]
  rfl

theorem data_prepared_native_query (a b tiles lane n) (ht : n < tiles) :
    (preparedState (dataCheckpoint a b tiles lane n).1 n tiles 0 (HopperStage.leader lane)).base.scalar.core.queries =
      nativeQuery tiles n (HopperStage.leader lane) := by
  rw [preparedState_queries,data_checkpoint_query]
  simp only [Nat.add_zero]
  exact native_query_at_tile tiles n (HopperStage.leader lane) ht

theorem data_checkpoint_values (a b tiles lane n) (hb : n ≤ tiles) :
    (dataCheckpoint a b tiles lane n).2 = fun slot => result a b n (Wgmma.cCoord (lane,slot)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have heq : (dataCheckpoint a b tiles lane (n+1)).2 = (dataOracle a b tiles lane).matrix
        (preparedState (dataCheckpoint a b tiles lane n).1 n tiles 0 (HopperStage.leader lane)).base.scalar.core.queries := by
      simp only [dataCheckpoint,loopCheckpoint,Nat.zero_add,zeroRetries]
    rw [heq,data_prepared_native_query a b tiles lane n (by omega)]
    funext slot
    exact data_oracle_native_matrix a b tiles lane n (by omega) slot

theorem data_loop_ready (a b tiles lane n) (ht : 0 < tiles) (hb : tiles ≤ 2^28) (hn : n ≤ tiles) :
    CheckpointReady (dataCheckpoint a b tiles lane n) n tiles (HopperStage.leader lane) 4096 4224 := by
  simpa only [dataCheckpoint,Nat.zero_add] using loopCheckpoint_ready (ctx tiles lane) (dataOracle a b tiles lane) 0 tiles (HopperStage.leader lane) zeroRetries
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) 4096 4224 rfl rfl rfl (Nat.le_refl 0)
    (initial_loop_registers tiles lane _ hb) (initial_loop_accumulators tiles lane _) ht n (by omega)

theorem data_loop_accumulators (a b tiles lane n) (ht : 0 < tiles) (hb : tiles ≤ 2^28) (hn : n ≤ tiles) :
    Accumulators (dataCheckpoint a b tiles lane n).1 (fun slot => result a b n (Wgmma.cCoord (lane,slot))) := by
  have ha := (data_loop_ready a b tiles lane n ht hb hn).2.2.2.2.2
  rw [data_checkpoint_values a b tiles lane n hn] at ha
  exact ha

theorem data_loop_run (a b tiles lane n) (ht : 0 < tiles) (hb : tiles ≤ 2^28) (hn : n ≤ tiles) :
    Wgmma.run (ctx tiles lane) (dataOracle a b tiles lane) code (loopFuel 0 tiles (HopperStage.leader lane) zeroRetries n)
      (initialLoopState tiles lane (HopperStage.leader lane)) = .ok ((dataCheckpoint a b tiles lane n).1,dataLoopEvents a b tiles lane n) := by
  apply loop_execute (ctx tiles lane) (dataOracle a b tiles lane) 0 tiles (HopperStage.leader lane) zeroRetries
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) 4096 4224 rfl rfl rfl (Nat.le_refl 0)
    (initial_loop_registers tiles lane _ hb) (initial_loop_accumulators tiles lane _) ht hb n (by omega)
  intro i _
  exact data_oracle_loop_replies a b tiles lane _ _

def dataKernelLoopEvents (a : TileA) (b : TileB) (tiles : Nat) (lane : Wgmma.Lane) : List Wgmma.Event :=
  (initializationEvents (HopperStage.leader lane)++dataInitialCopies a b tiles (HopperStage.leader lane))++dataLoopEvents a b tiles lane tiles

theorem data_kernel_loop_run (a b tiles lane) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Wgmma.run (ctx tiles lane) (dataOracle a b tiles lane) code (kernelLoopSteps tiles lane) {} =
      .ok ((dataCheckpoint a b tiles lane tiles).1,dataKernelLoopEvents a b tiles lane) := by
  rw [kernelLoopSteps,Wgmma.run_add,data_kernel_reaches_loop a b tiles lane ht hb]
  simp only [Except.bind,data_loop_run a b tiles lane tiles ht hb (Nat.le_refl _),dataKernelLoopEvents]

theorem data_loop_output_specification (a b tiles lane) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    ∀ slot, declarationLookup (computeSlotName slot) (dataCheckpoint a b tiles lane tiles).1.base.scalar.floats =
      some (.f32,specification a b tiles (Wgmma.cCoord (lane,slot))) := by
  intro slot
  have hv := (data_loop_accumulators a b tiles lane tiles ht hb (Nat.le_refl _) slot).1
  simpa only [result_matches_specification] using hv

end
end Ptx.Kernels.HopperDoubleBuffer
