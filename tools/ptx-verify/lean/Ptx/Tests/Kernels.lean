import Ptx.Generated.Copy
import Ptx.Generated.SharedSwap
import Ptx.Generated.Loop
import Ptx.Generated.MissingSync
import Ptx.Generated.OutOfBounds
import Ptx.Contracts
import Ptx.Async.Model

/-! Kernel-checked finite execution examples. These are deliberately labelled as
finite instances: they are not all-input, all-interleaving kernel contracts. -/
namespace Ptx.Examples
def copyInitial : Machine := {
  threads := [{}, {}]
  globalMem := [some 17, some 29, none, none]
  sharedMem := []
  params := [("src",0),("dst",8),("n",2)]
}
def copySchedule : List Action := List.replicate 12 (.thread 0) ++ List.replicate 12 (.thread 1)
def copyResult := run Generated.copy.program copySchedule copyInitial
theorem copy_values : (copyResult.toOption.map Machine.globalMem) =
    some [some 17, some 29, some 17, some 29] := by decide
theorem copy_terminates : (copyResult.toOption.map (fun m => m.threads.all (fun t => t.status == .done))) = some true := by decide
theorem copy_has_execution : ∃ m, copyResult = .ok m ∧ Steps Generated.copy.program copyInitial m := by
  have h : copyResult = .ok (copyResult.toOption.getD copyInitial) := by decide
  exact ⟨_, h, run_sound h⟩

def sharedInitial : Machine := { copyInitial with
  sharedMem := List.replicate (Generated.shared_swap.sharedBytes / 4) none
}
def sharedSchedule : List Action :=
  List.replicate 11 (.thread 0) ++ List.replicate 11 (.thread 1) ++ [.release] ++
  List.replicate 6 (.thread 0) ++ List.replicate 6 (.thread 1)
def sharedResult := run Generated.shared_swap.program sharedSchedule sharedInitial
theorem shared_values : (sharedResult.toOption.map Machine.globalMem) =
    some [some 17, some 29, some 29, some 17] := by decide
theorem shared_terminates : (sharedResult.toOption.map (fun m => m.threads.all (fun t => t.status == .done))) = some true := by decide

def missingSyncSchedule : List Action :=
  List.replicate 10 (.thread 0) ++ List.replicate 10 (.thread 1) ++ List.replicate 4 (.thread 0)
theorem rejects_missing_barrier :
    run Generated.missing_sync.program missingSyncSchedule sharedInitial =
      .error (.race .shared 4 1 0) := by decide
theorem rejects_out_of_bounds :
    run Generated.out_of_bounds.program (List.replicate 11 (.thread 0)) copyInitial =
      .error (.bounds .global 4104) := by decide
theorem rejects_premature_barrier_release : release sharedInitial = .error .barrierMismatch := by decide

def loopInitial : Machine := { threads := [{}], globalMem := [], sharedMem := [] }
def loopResult := run Generated.loop.program (List.replicate 14 (.thread 0)) loopInitial
theorem loop_value : ((loopResult.toOption.bind (fun m => m.threads[0]?)).bind (fun t => lookup "%r" t.regs)) = some 4 := by decide
theorem loop_terminates : (loopResult.toOption.map (fun m => m.threads.all (fun t => t.status == .done))) = some true := by decide

open Async in
def asyncInitial : Async.State := { streams := [{},{}], buffers := [{value:=42},{}] }
open Async in
def prefetch : Except Async.Error Async.State := do
  let s ← submitCopy asyncInitial 0 0 1
  let s ← record s 0 7
  let s ← waitStream s 1 7
  let s ← submitUse s 1 1
  let s ← record s 1 8
  let s ← deviceStep s 0
  let s ← deviceStep s 1 -- actual wait, after producer completion
  let s ← deviceStep s 1 -- actual consumer
  let s ← await s 7
  await s 8
theorem prefetch_value : ((prefetch.toOption.bind (fun s => s.buffers[1]?)).map Async.Buffer.value) = some 42 := by decide
theorem prefetch_returns_resources : (prefetch.toOption.map (fun s => s.buffers.all (fun b => b.loans.isEmpty))) = some true := by decide

open Async in
def deferredReclaim : Except Async.Error Async.State := do
  let s ← submitUse asyncInitial 0 0
  let s ← record s 0 9
  let s ← deviceStep s 0
  let s ← await s 9
  reclaim s 0
theorem deferred_reclaim_succeeds : ((deferredReclaim.toOption.bind (fun s => s.buffers[0]?)).map Async.Buffer.alive) = some false := by decide

open Async in
def earlyReclaim : Except Async.Error Async.State := do
  let s ← submitUse asyncInitial 0 0
  reclaim s 0
theorem rejects_early_reclaim : earlyReclaim = .error .outstandingLoan := by decide
open Async in
def prematureEvent : Except Async.Error Async.State := do
  let s ← submitCopy asyncInitial 0 0 1
  let s ← record s 0 7
  await s 7
theorem recording_is_not_completion : prematureEvent = .error .notComplete := by decide
open Async in
def missingStreamWait : Except Async.Error Async.State := do
  let s ← submitCopy asyncInitial 0 0 1
  submitUse s 1 1
theorem rejects_missing_stream_wait : missingStreamWait = .error .outstandingLoan := by decide
open Async in
def waitDoesNotComplete : Except Async.Error Async.State := do
  let s ← submitCopy asyncInitial 0 0 1
  let s ← record s 0 7
  let s ← waitStream s 1 7
  deviceStep s 1
theorem queued_wait_blocks : waitDoesNotComplete = .error .notComplete := by decide

end Ptx.Examples
