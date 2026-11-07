import Ptx.Hopper.Mbarrier
import Ptx.Generated.HopperMbarrier
import Ptx.Generated.HopperMbarrierNoComplete

/-! Actual two-phase source traces and a locally completing lying oracle that
fails the independent resource protocol. These are not GEMM, TMA data-memory
admission or GPU execution proofs. -/
namespace Ptx.HopperMbarrierTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Mbarrier
noncomputable section
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

def ctx : Scalar.Context := {id := ⟨.zero,.zero⟩,block := .one}
def oracle (answers : Nat → Bool) : Oracle :=
  {ampere := {scalar := fun _ => .integer 0,bytes := fun _ => []},wait := answers}
def loc : Location := ⟨.shared .zero,0⟩
def ev (op : BarrierOp) : Hopper.Event := .barrier ⟨loc,op⟩
def goodOps : List BarrierOp := [.init 1,.arriveExpectTx 16,.completeTx 16,.tryWaitParity 0 true,
  .arriveExpectTx 32,.completeTx 32,.tryWaitParity 1 true,.inval]
def goodEvents : List Hopper.Event := goodOps.map ev
def done (queries : Nat) : State :=
  {scalar := {core := {thread := {pc := 11,regs := [("%ready",1),("%bar",0)],status := .done},queries := queries}}}
def goodLocated : List (SourceRun.Located Hopper.Event) :=
  List.zipWith (fun pc kind => ⟨kind,pc⟩) [1,2,3,4,6,7,8,10] goodEvents

theorem typed_good (i) (hi : i ∈ Generated.hopper_mbarrier.program) :
    InstructionTyped Generated.hopper_mbarrier.registerDeclarations [] 12 i :=
  Generated.hopper_mbarrier.checked.instruction_typed hi

theorem good_source : Hopper.run ctx (oracle (fun _ => true)) Generated.hopper_mbarrier.program 12 {} =
    .ok (done 2,goodEvents) := by rfl
theorem good_actual_source_pcs : runLocated ctx (oracle (fun _ => true)) Generated.hopper_mbarrier.program 12 {} =
    .ok (done 2,goodLocated) := by rfl
theorem good_projected_operations : operationsAt loc goodEvents = goodOps := by rfl
theorem different_cta_is_another_object : operationsAt ⟨.shared ⟨1,0,0⟩,0⟩ goodEvents = [] := by rfl
theorem different_address_is_another_object : operationsAt ⟨.shared .zero,8⟩ goodEvents = [] := by rfl
theorem good_protocol_run : Mbarrier.run none goodOps = some none := by decide
theorem good_source_protocol : AdmittedAt loc goodEvents := ⟨none,good_protocol_run⟩

def retryOps : List BarrierOp := [.init 1,.arriveExpectTx 16,.completeTx 16,.tryWaitParity 0 false,.tryWaitParity 0 true,
  .arriveExpectTx 32,.completeTx 32,.tryWaitParity 1 true,.inval]
def retryEvents := retryOps.map ev

theorem retry_source : Hopper.run ctx (oracle (fun q => q != 0)) Generated.hopper_mbarrier.program 14 {} =
    .ok (done 3,retryEvents) := by rfl
theorem retry_protocol_run : Mbarrier.run none retryOps = some none := by decide
theorem retry_source_protocol : AdmittedAt loc retryEvents := ⟨none,retry_protocol_run⟩

def badOps : List BarrierOp := [.init 1,.arriveExpectTx 16,.tryWaitParity 0 true]
def badEvents := badOps.map ev
def badDone : State := {scalar := {core := {thread := {pc := 3,regs := [("%ready",1)],status := .done},queries := 1}}}

theorem incomplete_but_source_returns : Hopper.run ctx (oracle (fun _ => true)) Generated.hopper_mbarrier_no_complete.program 4 {} =
    .ok (badDone,badEvents) := by rfl
theorem incomplete_protocol_rejected : Mbarrier.run none badOps = none := by decide
theorem incomplete_source_not_admitted : ¬ AdmittedAt loc badEvents := by
  rintro ⟨last,h⟩
  change Mbarrier.run none badOps = some last at h
  rw [incomplete_protocol_rejected] at h
  cases h

theorem signed_early_completion : Mbarrier.run none [.init 1,.completeTx 16] =
    some (some ⟨0,1,1,-16,true⟩) := by decide
theorem completion_before_expect_is_legal : Mbarrier.run none [.init 1,.completeTx 16,.arriveExpectTx 16,.tryWaitParity 0 true] =
    some (some ⟨1,1,1,0,true⟩) := by decide

theorem arrival_only_not_complete : Mbarrier.run none [.init 1,.arriveExpectTx 16] =
    some (some ⟨0,1,0,16,true⟩) := by decide
theorem transactions_only_not_complete : Mbarrier.run none [.init 2,.arriveExpectTx 16,.completeTx 16] =
    some (some ⟨0,2,1,0,true⟩) := by decide
theorem missing_arrival_wait_rejected : Mbarrier.run none [.init 2,.arriveExpectTx 16,.completeTx 16,.tryWaitParity 0 true] = none := by decide

theorem next_phase_requires_successful_wait : Mbarrier.run none [.init 1,.arriveExpectTx 0,.arriveExpectTx 0] = none := by decide
theorem false_wait_does_not_enable_reuse : Mbarrier.run none [.init 1,.arriveExpectTx 0,.tryWaitParity 0 false,.arriveExpectTx 0] = none := by decide
theorem wrong_parity_rejected : Mbarrier.run none [.init 1,.arriveExpectTx 0,.tryWaitParity 1 true] = none := by decide
theorem stale_parity_after_reuse_rejected : Mbarrier.run none [.init 1,.arriveExpectTx 0,.tryWaitParity 0 true,
    .arriveExpectTx 0,.tryWaitParity 0 true] = none := by decide

theorem double_init_rejected : Mbarrier.run none [.init 1,.init 1] = none := by decide
theorem uninitialized_arrive_rejected : Mbarrier.run none [.arriveExpectTx 0] = none := by decide
theorem zero_init_rejected : Mbarrier.run none [.init 0] = none := by decide
theorem count_overflow_rejected : Mbarrier.run none [.init (2^20)] = none := by decide
theorem bounded_large_expect_delta : Mbarrier.run none [.init 2,.completeTx limit,.arriveExpectTx (2*limit)] =
    some (some ⟨0,2,1,(limit : Int),true⟩) := by decide
theorem bounded_large_complete_delta : Mbarrier.step (some ⟨0,2,1,(limit : Int),true⟩) (.completeTx (2*limit)) =
    some (some ⟨0,2,1,-(limit : Int),true⟩) := by decide

theorem negative_tx_overflow_rejected : Mbarrier.run none [.init 1,.completeTx limit,.completeTx 1] = none := by decide

theorem positive_tx_overflow_rejected : Mbarrier.run none [.init 2,.arriveExpectTx limit,.arriveExpectTx 1] = none := by decide
theorem invalidation_allows_reinitialization : Mbarrier.run none [.init 1,.arriveExpectTx 0,.tryWaitParity 0 true,.inval,.init 2] =
    some (some ⟨0,2,2,0,true⟩) := by decide

theorem second_phase_wf : ObjectWellFormed (some (PhaseState.mk 2 1 1 0 true)) := by
  exact Mbarrier.run_wf (s := none) trivial (show Mbarrier.run none (goodOps.take 7) = some (some ⟨2,1,1,0,true⟩) by decide)

end
end Ptx.HopperMbarrierTests
