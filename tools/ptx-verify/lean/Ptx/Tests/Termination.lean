import Ptx.Kernels.CopyEventRefinement
import Ptx.Tests.CopyEvent

/-! Completion is stronger than safety/progress. A self-loop can always execute
another step, but cannot satisfy the strict-rank premise or become finished.
-/
namespace Ptx.TerminationTests
open Ptx.Termination

def loopCode : List Instr := [.jump 0]
def loopMachine : Machine := {threads := [{}],globalMem := [],sharedMem := []}

theorem self_loop_progress : threadStep loopCode 0 loopMachine = .ok loopMachine := by decide

theorem self_loop_step {action next} (hs : step loopCode action loopMachine = .ok next) :
    next = loopMachine := by
  cases action with
  | release => simp [step,release,loopMachine,bind,Except.bind] at hs
  | thread tid =>
    cases tid with
    | zero => simpa only [step,self_loop_progress,Except.ok.injEq] using hs.symm
    | succ tid => simp [step,threadStep,loopMachine,bind,Except.bind] at hs

theorem self_loop_never_complete {next} (hs : Steps loopCode loopMachine next) :
    next.threads.all (fun t => t.status == .done) = false := by
  have he : ∀ m m', Steps loopCode m m' → m = loopMachine → m' = loopMachine := by
    intro m m' hsteps
    induction hsteps with
    | refl => exact fun h => h
    | next action hstep _ ih =>
      intro hm
      rw [hm] at hstep
      exact ih (self_loop_step hstep)
  rw [he _ _ hs rfl]
  rfl

theorem self_loop_rank_rejected (rank : Machine → Nat) :
    ¬ rank loopMachine < rank loopMachine := Nat.lt_irrefl _

/-- Operational completion supports the original empty CPU configuration without
pretending its zero thread count is a legal GPU launch. -/
theorem zero_thread_skip :
    let c := CopyEventTests.zeroConfig
    let m := CopyContract.initial c [some 91]
    let initial := Event.Cells.encode c.before (fun _ => ISA.byte 165)
    run CopyEvent.code [] m = .ok m ∧
      m.threads.all (fun t => t.status == .done) = true ∧
      Event.Cells.encode m.globalMem initial = initial ∧ ∀ l, ¬ CopyEvent.Pre c l := by
  dsimp only
  have h := CopyEvent.zero_count_skip CopyEventTests.zeroConfig rfl (CopyContract.initial_pre _ [some 91])
    (Event.Cells.encode_represents _ (fun _ => ISA.byte 165))
  exact ⟨h.2.1,h.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩

theorem masked_all_outputs_included {execution sources order o}
    (hw : execution.WellFormed CopyEvent.code (CopyEventTests.launch CopyInstances.maskedConfig (fun _ => ISA.byte 165)))
    (hc : Event.GenericMemoryConditions execution
      (CopyEventTests.launch CopyInstances.maskedConfig (fun _ => ISA.byte 165)).initial sources order)
    (ho : Event.ObserverConditions execution
      (CopyEventTests.launch CopyInstances.maskedConfig (fun _ => ISA.byte 165)).initial sources order o)
    (hd : o.domain = CopyEvent.domain CopyInstances.maskedConfig) :
    ∃ actions m', run CopyEvent.code actions CopyInstances.maskedInitial = .ok m' ∧
      m'.threads.all (fun t => t.status == .done) = true ∧ CopyContract.Post CopyInstances.maskedConfig m' ∧
      ∀ loc ∈ CopyEvent.domain CopyInstances.maskedConfig,
        o.output loc = Event.Cells.encode m'.globalMem
          (CopyEventTests.launch CopyInstances.maskedConfig (fun _ => ISA.byte 165)).initial loc :=
  CopyEvent.output_inclusion CopyInstances.maskedConfig
    (CopyEventTests.launch_pre _ _ (by decide)) hw hc ho hd (CopyContract.initial_pre _ _)

end Ptx.TerminationTests
