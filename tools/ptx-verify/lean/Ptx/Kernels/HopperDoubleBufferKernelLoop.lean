import Ptx.Kernels.HopperDoubleBufferInitialization
import Ptx.Kernels.HopperDoubleBufferLoopSchedule

/-! Reconstructed initial-kernel execution to output entry for every lane and
bounded tile count. The chosen represented zero-input oracle is explicit.
This does not finish output/return or admit resource/collective/memory graphs.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

theorem initial_loop_registers (tiles : Nat) (lane : Wgmma.Lane) (leader : Bool) (hb : tiles ≤ 2^28) :
    LoopRegisters (initialLoopState tiles lane leader) 0 tiles leader 4096 4224 := by
  have hw : wrap 32 tiles = tiles := Nat.mod_eq_of_lt (by omega)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro binding hm
    simp only [selectionBindings,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases leader <;> simp [initialLoopState,initialLoopRegs,entryRegs,lookup,phaseZero,phaseOne,wrap]
  all_goals cases leader <;> simp [initialLoopState,initialLoopRegs,entryRegs,lookup,hw,show wrap 64 4096 = 4096 from by decide,show wrap 64 4224 = 4224 from by decide]

theorem initial_loop_accumulators (tiles : Nat) (lane : Wgmma.Lane) (leader : Bool) :
    Accumulators (initialLoopState tiles lane leader) (fun _ => 0) := by
  intro i
  fin_cases i <;> cases leader <;>
    simp [initialLoopState,initialLoopRegs,entryRegs,computeSlotName,HopperStage.zeroFloats,HopperStage.zeroLiteral,
      Scalar.F32Literal.zero_value,declarationLookup,lookup]

def kernelLoopSteps (tiles : Nat) (lane : Wgmma.Lane) : Nat :=
  initialSteps (HopperStage.leader lane)+loopFuel 0 tiles (HopperStage.leader lane) zeroRetries tiles

def kernelLoopState (tiles : Nat) (lane : Wgmma.Lane) : Wgmma.State :=
  (loopCheckpoint (ctx tiles lane) (oracle tiles) 0 tiles (HopperStage.leader lane) zeroRetries
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) tiles).1

def kernelLoopEvents (tiles : Nat) (lane : Wgmma.Lane) : List Wgmma.Event :=
  (initializationEvents (HopperStage.leader lane)++initialCopies tiles (HopperStage.leader lane))++
  loopEvents (ctx tiles lane) (oracle tiles) 0 tiles (HopperStage.leader lane) zeroRetries
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) 4096 4224 tiles

theorem kernel_loop_source (tiles : Nat) (lane : Wgmma.Lane) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Wgmma.run (ctx tiles lane) (oracle tiles) code (kernelLoopSteps tiles lane) {} =
      .ok (kernelLoopState tiles lane,kernelLoopEvents tiles lane) := by
  have hl := zero_retry_loop_source (ctx tiles lane) 0 tiles (HopperStage.leader lane)
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) 4096 4224
    rfl rfl rfl (Nat.le_refl 0) (initial_loop_registers tiles lane _ hb) (initial_loop_accumulators tiles lane _) ht hb
  simp only [Nat.sub_zero] at hl
  rw [kernelLoopSteps,Wgmma.run_add,kernel_reaches_loop tiles lane ht hb]
  simp only [Except.bind,hl,kernelLoopState,kernelLoopEvents]

theorem kernel_loop_output (tiles : Nat) (lane : Wgmma.Lane) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    (kernelLoopState tiles lane).base.scalar.core.thread.pc = 85 ∧ Wgmma.pending (kernelLoopState tiles lane).ledger = [] := by
  exact zero_retry_loop_output (ctx tiles lane) 0 tiles (HopperStage.leader lane)
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) 4096 4224
    rfl rfl rfl (Nat.le_refl 0) (initial_loop_registers tiles lane _ hb) (initial_loop_accumulators tiles lane _) ht

theorem kernel_loop_groups (tiles : Nat) (lane : Wgmma.Lane) :
    (kernelLoopState tiles lane).ledger.groups = tiles := by
  simp [kernelLoopState,initialLoopState]

theorem zero_oracle_checkpoint_values (context : Scalar.Context) (first tiles : Nat) (leader : Bool)
    (s : Wgmma.State) (n : Nat) :
    (loopCheckpoint context (oracle tiles) first tiles leader zeroRetries s (fun _ => 0) n).2 = (fun _ => 0) := by
  cases n <;> rfl

theorem kernel_loop_zero_accumulators (tiles : Nat) (lane : Wgmma.Lane) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Accumulators (kernelLoopState tiles lane) (fun _ => 0) := by
  have hr := loopCheckpoint_ready (ctx tiles lane) (oracle tiles) 0 tiles (HopperStage.leader lane) zeroRetries
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) 4096 4224
    rfl rfl rfl (Nat.le_refl 0) (initial_loop_registers tiles lane _ hb) (initial_loop_accumulators tiles lane _) ht tiles (by omega)
  have ha := hr.2.2.2.2.2
  rw [zero_oracle_checkpoint_values] at ha
  exact ha

def zeroTileSteps (lane : Wgmma.Lane) : Nat := 28+initializationSteps (HopperStage.leader lane)+2

theorem kernel_zero_tiles_source (lane : Wgmma.Lane) :
    Wgmma.run (ctx 0 lane) (oracle 0) code (zeroTileSteps lane) {} =
      .ok (guardedInitialState 0 lane (HopperStage.leader lane) true,initializationEvents (HopperStage.leader lane)) := by
  rw [zeroTileSteps,Wgmma.run_add,Wgmma.run_add,entry_producer_flag]
  simp only [Except.bind,initialize_barriers,initial_guard_execute 0 lane _ (by decide),decide_true,List.nil_append,List.append_nil]

theorem kernel_loop_status (tiles : Nat) (lane : Wgmma.Lane) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    (kernelLoopState tiles lane).base.scalar.core.thread.status = .running := by
  exact (loopCheckpoint_ready (ctx tiles lane) (oracle tiles) 0 tiles (HopperStage.leader lane) zeroRetries
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) 4096 4224
    rfl rfl rfl (Nat.le_refl 0) (initial_loop_registers tiles lane _ hb) (initial_loop_accumulators tiles lane _) ht tiles (by omega)).1

theorem kernel_loop_completed (tiles : Nat) (lane : Wgmma.Lane) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    (kernelLoopState tiles lane).ledger.completed = tiles := by
  simpa only [kernelLoopState,show (initialLoopState tiles lane (HopperStage.leader lane)).ledger.groups = 0 from rfl,Nat.zero_add] using
    (loopCheckpoint_completed (ctx tiles lane) (oracle tiles) 0 tiles (HopperStage.leader lane) zeroRetries
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) 4096 4224
    rfl rfl rfl (Nat.le_refl 0) (initial_loop_registers tiles lane _ hb) (initial_loop_accumulators tiles lane _) ht tiles ht (by omega))

theorem kernel_loop_call_count (tiles : Nat) (lane : Wgmma.Lane) :
    (kernelLoopState tiles lane).ledger.calls.length = tiles := by
  simp [kernelLoopState,loopCheckpoint_call_count,initialLoopState]

theorem kernel_loop_control_frame (tiles : Nat) (lane : Wgmma.Lane) (ht : 0 < tiles) (hb : tiles ≤ 2^28) (name : String)
    (hx : name ∉ ["%phase0","%phase1","%even","%waitbar","%ad","%bd","%parity","%ready",
      "%next","%more","%nextbar","%copya","%copyb","%ay","%slot","%tile","%d0","%d1","%d2","%d3"]) :
    lookup name (kernelLoopState tiles lane).base.scalar.core.thread.regs =
      lookup name (initialLoopState tiles lane (HopperStage.leader lane)).base.scalar.core.thread.regs := by
  exact loopCheckpoint_control_frame (ctx tiles lane) (oracle tiles) 0 tiles (HopperStage.leader lane) zeroRetries
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) 4096 4224
    rfl rfl rfl (Nat.le_refl 0) (initial_loop_registers tiles lane _ hb) (initial_loop_accumulators tiles lane _) ht tiles (by omega) name hx

end
end Ptx.Kernels.HopperDoubleBuffer
