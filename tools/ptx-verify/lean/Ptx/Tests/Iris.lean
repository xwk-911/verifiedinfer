import Ptx.Iris.Ptx
import Ptx.Iris.Async
import Ptx.Async.Refinement
import Ptx.Tests.Copy
import Ptx.Tests.SharedSwap
import Ptx.Tests.Kernels

/-! Closed Iris regressions and a nonvacuous PTX/async completion bridge.
The concrete kernel schedules here complement the separate universal contracts.
-/
namespace Ptx.IrisInstances
open Iris.ProgramLogic

theorem copy_closed :
    adequate .NotStuck
      (IrisPtx.script CopyContract.code CopyInstances.maskedSchedule) CopyInstances.maskedInitial
      (fun v _ => ∃ m', v = .ok m' ∧ CopyContract.Post CopyInstances.maskedConfig m') := by
  let final := CopyInstances.maskedResult.toOption.getD CopyInstances.maskedInitial
  have hs : CopyInstances.maskedResult = .ok final := by decide
  have hd : final.threads.all (fun t => t.status == .done) = true := by decide
  have ha := IrisPtx.copy_adequate (CopyContract.initial_pre _ _) hs hd
  exact ⟨fun t s v h => ⟨final,ha.adequate_result t s v h⟩,ha.adequate_not_stuck⟩

theorem shared_closed :
    adequate .NotStuck (IrisPtx.script SharedContract.code SharedInstances.roundRobin) SharedInstances.start
      (fun v _ => ∃ m', v = .ok m' ∧ SharedContract.Post SharedInstances.pair m') := by
  let final := SharedInstances.result.toOption.getD SharedInstances.start
  have hs : SharedInstances.result = .ok final := by decide
  have hd : final.threads.all (fun t => t.status == .done) = true := by decide
  have ha := IrisPtx.shared_adequate (SharedContract.initial_pre _) hs hd
  exact ⟨fun t s v h => ⟨final,ha.adequate_result t s v h⟩,ha.adequate_not_stuck⟩

theorem bounds_cannot_certify :
    ¬ adequate .NotStuck
      (IrisPtx.script Generated.out_of_bounds.program (List.replicate 11 (.thread 0))) Examples.copyInitial
      (fun v _ => ∃ m', v = .ok m') :=
  IrisPtx.reject_not_ok_adequate Examples.rejects_out_of_bounds

theorem missing_barrier_cannot_certify :
    ¬ adequate .NotStuck
      (IrisPtx.script Generated.missing_sync.program Examples.missingSyncSchedule) Examples.sharedInitial
      (fun v _ => ∃ m', v = .ok m') :=
  IrisPtx.reject_not_ok_adequate Examples.rejects_missing_barrier

theorem early_reclaim_cannot_certify (value : Nat) :
    ¬ adequate .NotStuck
      (IrisAsync.Expr.script [.use 0 0,.reclaim 0]) (Async.initial 1 [value])
      (fun v _ => ∃ s', v = .ok s') :=
  IrisAsync.reject_not_ok_adequate (by rfl)

/-- Arbitrary valid u32 data, actual 12-instruction generated copy, and exact
abstract data correspondence. This witness is not restricted to a sample value. -/
theorem scalar_copy_bridge (value : Nat) (hw : value < 2^32) :
    ∃ m m' next,
      Steps CopyContract.code m m' ∧
      m'.threads.all (fun t => t.status == .done) = true ∧
      Async.execute (Async.initial 2 [value,0]) (.copy 0 1) = .ok next ∧
      m'.globalMem = AsyncPtxRefinement.cells next := by
  let s := Async.initial 2 [value,0]
  let a : Async.Buffer := {value := value}
  let b : Async.Buffer := {value := 0}
  have ha : Async.getBuffer s 0 = .ok a := rfl
  have hb : Async.getBuffer s 1 = .ok b := rfl
  let c := AsyncPtxRefinement.copyConfig s 0 1 a b ha hb (by decide) hw (by decide) (by decide)
  let m := CopyContract.initial c []
  let actions : List Action := List.replicate 12 (.thread 0)
  let m' := (run CopyContract.code actions m).toOption.getD m
  have hs : run CopyContract.code actions m = .ok m' := by with_unfolding_all rfl
  have hd : m'.threads.all (fun t => t.status == .done) = true := by with_unfolding_all rfl
  obtain ⟨next,hn,heq⟩ := AsyncPtxRefinement.copy_refines ha hb (by decide) hw
    (by decide) (by decide) (CopyContract.initial_pre c []) (run_sound hs) hd
  exact ⟨m,m',next,run_sound hs,hd,hn,heq⟩

end Ptx.IrisInstances
