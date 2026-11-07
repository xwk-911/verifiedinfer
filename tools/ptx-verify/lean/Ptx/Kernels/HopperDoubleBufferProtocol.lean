import Ptx.Hopper.Mbarrier
import Ptx.Kernels.HopperDoubleBufferSpec

/-! Resource-local repeated transfer phases for either shared stage. This
proves arbitrary-length protocol runs; matching these abstract operations to
all actual source/notification IDs and proving control/memory remain separate.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def readyState (phase : Nat) : Mbarrier.PhaseState := ⟨phase,1,1,0,true⟩
def transferredState (phase : Nat) : Mbarrier.PhaseState := ⟨phase+1,1,1,0,false⟩
def phaseOperations (phase : Nat) : List BarrierOp :=
  [.arriveExpectTx 2304,.completeTx 2048,.completeTx 256]++List.replicate 128 (.tryWaitParity (phase%2) true)
def phases : Nat → List BarrierOp
  | 0 => []
  | n+1 => phases n++phaseOperations n
def stageProtocol (uses : Nat) : List BarrierOp := [.init 1]++phases uses++[.inval]

theorem transfers_finish_phase (phase : Nat) :
    Mbarrier.run (some (readyState phase)) [.arriveExpectTx 2304,.completeTx 2048,.completeTx 256] = some (some (transferredState phase)) := by
  simp [Mbarrier.run,Mbarrier.step,Mbarrier.accept,Mbarrier.WellFormed,Mbarrier.finish,Mbarrier.limit,readyState,transferredState]
theorem successful_phase_wait (phase : Nat) :
    Mbarrier.step (some (transferredState phase)) (.tryWaitParity (phase%2) true) = some (some (readyState (phase+1))) := by
  have hp : phase%2 ≠ (phase+1)%2 := by omega
  simp [Mbarrier.step,transferredState,readyState,hp]
theorem repeated_ready_waits (phase count : Nat) :
    Mbarrier.run (some (readyState (phase+1))) (List.replicate count (.tryWaitParity (phase%2) true)) = some (some (readyState (phase+1))) := by
  have hp : phase%2 ≠ (phase+1)%2 := by omega
  have hs : Mbarrier.step (some (readyState (phase+1))) (.tryWaitParity (phase%2) true) = some (some (readyState (phase+1))) := by
    simp [Mbarrier.step,readyState,hp]
  induction count with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ,Mbarrier.run,hs,Option.bind_some,ih]
theorem one_phase_protocol (phase : Nat) :
    Mbarrier.run (some (readyState phase)) (phaseOperations phase) = some (some (readyState (phase+1))) := by
  rw [phaseOperations,Mbarrier.run_append,transfers_finish_phase,Option.bind_some]
  rw [List.replicate_succ,Mbarrier.run,successful_phase_wait,Option.bind_some]
  exact repeated_ready_waits phase 127
theorem all_phases_protocol (uses : Nat) :
    Mbarrier.run (some (readyState 0)) (phases uses) = some (some (readyState uses)) := by
  induction uses with
  | zero => rfl
  | succ n ih => rw [phases,Mbarrier.run_append,ih,Option.bind_some,one_phase_protocol]
theorem full_stage_protocol (uses : Nat) : Mbarrier.run none (stageProtocol uses) = some none := by
  rw [stageProtocol,Mbarrier.run_append,Mbarrier.run_append]
  have hi : Mbarrier.run none [.init 1] = some (some (readyState 0)) := by decide
  rw [hi,Option.bind_some,all_phases_protocol,Option.bind_some]
  rfl
theorem unobserved_phase_cannot_restart (phase : Nat) :
    Mbarrier.step (some (transferredState phase)) (.arriveExpectTx 2304) = none := by
  simp [Mbarrier.step,transferredState]
theorem current_parity_cannot_confirm (phase : Nat) :
    Mbarrier.step (some (transferredState phase)) (.tryWaitParity ((phase+1)%2) true) = none := by
  simp [Mbarrier.step,transferredState]
theorem first_transfer_alone_cannot_confirm (phase : Nat) :
    Mbarrier.run (some (readyState phase)) [.arriveExpectTx 2304,.completeTx 2048,.tryWaitParity (phase%2) true] = none := by
  by_cases hphase : phase = 0
  · subst phase; decide
  · simp [Mbarrier.run,Mbarrier.step,Mbarrier.accept,Mbarrier.WellFormed,Mbarrier.finish,Mbarrier.limit,readyState]

end
end Ptx.Kernels.HopperDoubleBuffer
