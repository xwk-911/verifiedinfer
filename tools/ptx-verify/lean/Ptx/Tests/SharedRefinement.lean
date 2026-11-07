import Ptx.Kernels.SharedEventRefinement
import Ptx.Tests.SharedEvent

/-! Regression boundaries for completion and full allocated-byte inclusion.
Arbitrary-candidate theorems are distinct from the finite executable rank checks.
-/
namespace Ptx.SharedRefinementTests
open Ptx.ISA Ptx.Event

def arrived : Machine :=
  (run SharedContract.code (List.replicate 11 [.thread 0,.thread 1]).flatten SharedInstances.start).toOption.getD
    SharedInstances.start
def resumed := SharedContract.released arrived

theorem real_collective_release : release arrived = .ok resumed := by decide

theorem collective_work_decreases : SharedCompletion.work arrived = 13 ∧ SharedCompletion.work resumed = 12 := by decide

theorem thread_work_unchanged_on_release :
    Termination.potential (Termination.threadWork 17) arrived.threads = 12 ∧
    Termination.potential (Termination.threadWork 17) resumed.threads = 12 := by decide

/-- Original Pre permits arbitrary initialized shared cells, stale register data
overwritten by the program, irrelevant parameters and shadowed parameter tails. -/
def customStart : Machine := {
  threads := [{regs := [("%r3",999)]},{regs := [("%rd4",99999)]}]
  globalMem := SharedInstances.pair.before
  sharedMem := [some 17,some 23]
  params := [("unused",99),("src",0),("dst",8),("src",100)]
}

theorem custom_pre : SharedContract.Pre SharedInstances.pair customStart := by
  refine {count := rfl,memory := rfl,sharedSize := rfl,params := ⟨rfl,rfl⟩,phase := rfl,history := rfl,threads := ?_}
  intro t ht
  simp only [customStart,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl <;> exact ⟨rfl,rfl⟩

theorem custom_start_completes :
    ∃ actions m, run SharedContract.code actions customStart = .ok m ∧
      m.threads.all (fun t => t.status == .done) = true ∧ SharedContract.Post SharedInstances.pair m := by
  obtain ⟨m,hs,hd,hpost⟩ := SharedCompletion.complete_from_pre custom_pre
  obtain ⟨actions,hrun⟩ := Termination.steps_run hs
  exact ⟨actions,m,hrun,hd,hpost⟩

theorem all_candidate_outputs_included (c : SharedContract.Config) (fallback : ByteMap)
    {execution sources order o}
    (hw : execution.WellFormed SharedEvent.code (SharedEventTests.launch c fallback))
    (hc : GenericMemoryConditions execution (SharedEventTests.launch c fallback).initial sources order)
    (ho : ObserverConditions execution (SharedEventTests.launch c fallback).initial sources order o)
    (hd : o.domain = SharedEvent.domain c) :
    ∃ actions m, run SharedEvent.code actions (SharedContract.initial c) = .ok m ∧
      m.threads.all (fun t => t.status == .done) = true ∧ SharedContract.Post c m ∧
      ∀ loc ∈ SharedEvent.domain c,
        o.output loc = Cells.encode m.globalMem (SharedEventTests.launch c fallback).initial loc :=
  SharedEvent.output_inclusion c (SharedEventTests.launch_pre c fallback) hw hc ho hd (SharedContract.initial_pre c)

theorem custom_start_all_outputs_included {execution sources order o}
    (hw : execution.WellFormed SharedEvent.code (SharedEventTests.launch SharedInstances.pair (fun _ => byte 165)))
    (hc : GenericMemoryConditions execution (SharedEventTests.launch SharedInstances.pair (fun _ => byte 165)).initial sources order)
    (ho : ObserverConditions execution (SharedEventTests.launch SharedInstances.pair (fun _ => byte 165)).initial sources order o)
    (hd : o.domain = SharedEvent.domain SharedInstances.pair) :
    ∃ actions m, run SharedEvent.code actions customStart = .ok m ∧
      m.threads.all (fun t => t.status == .done) = true ∧ SharedContract.Post SharedInstances.pair m ∧
      ∀ loc ∈ SharedEvent.domain SharedInstances.pair,
        o.output loc = Cells.encode m.globalMem (SharedEventTests.launch SharedInstances.pair (fun _ => byte 165)).initial loc :=
  SharedEvent.output_inclusion SharedInstances.pair (SharedEventTests.launch_pre _ _) hw hc ho hd custom_pre

/-- The SAME actual old schedule agrees with every permitted event output,
not only the canonical witness chosen to establish non-vacuity. -/
theorem round_robin_all_outputs_agree {execution sources order o}
    (hw : execution.WellFormed SharedEvent.code (SharedEventTests.launch SharedInstances.pair (fun _ => byte 165)))
    (hc : GenericMemoryConditions execution (SharedEventTests.launch SharedInstances.pair (fun _ => byte 165)).initial sources order)
    (ho : ObserverConditions execution (SharedEventTests.launch SharedInstances.pair (fun _ => byte 165)).initial sources order o)
    (hd : o.domain = SharedEvent.domain SharedInstances.pair) :
    ∃ m, SharedInstances.result = .ok m ∧
      ∀ loc ∈ SharedEvent.domain SharedInstances.pair,
        o.output loc = Cells.encode m.globalMem (SharedEventTests.launch SharedInstances.pair (fun _ => byte 165)).initial loc := by
  let m := SharedInstances.result.toOption.getD SharedInstances.start
  have hr : SharedInstances.result = .ok m := by decide
  have hdone : m.threads.all (fun t => t.status == .done) = true := by decide
  exact ⟨m,hr,SharedEvent.completed_output_agreement SharedInstances.pair (SharedEventTests.launch_pre _ _)
    hw hc ho hd (SharedContract.initial_pre _) (run_sound hr) hdone⟩

/-- Initialized-cell representation by itself cannot constrain unknown bytes.
The region's byte-frame obligation is necessary for exact output inclusion. -/
theorem unknown_representation_not_byte_equality :
    Cells.Represents [none] (fun _ => byte 0) ∧ Cells.Represents [none] (fun _ => byte 165) ∧
      (fun _ : Location => byte 0) ≠ (fun _ : Location => byte 165) := by
  have hr : ∀ bytes, Cells.Represents [none] bytes := by
    intro bytes cell value h
    cases cell <;> simp at h
  refine ⟨hr _,hr _,?_⟩
  intro he
  have h := congrFun he (Cells.location 0 0)
  exact (show byte 0 ≠ byte 165 by decide) h

end Ptx.SharedRefinementTests
