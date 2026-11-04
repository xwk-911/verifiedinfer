import Ptx.Kernels.SharedSwap

/-! Finite regression evidence, kept separate from the universal shared contract. -/
namespace Ptx.SharedInstances
open SharedContract
open CopyContract (word)

def pair := pairConfig 4294967295 4294967307
def start := initial pair
def roundRobin : List Action :=
  (List.replicate 11 [.thread 0,.thread 1]).flatten ++ [.release] ++
  (List.replicate 6 [.thread 1,.thread 0]).flatten
def sequential : List Action :=
  List.replicate 11 (.thread 1) ++ List.replicate 11 (.thread 0) ++ [.release] ++
  List.replicate 6 (.thread 0) ++ List.replicate 6 (.thread 1)
def result := run code roundRobin start
def sequentialResult := run code sequential start

theorem words_exact : (result.toOption.map Machine.globalMem) =
    some [some 4294967295,some 11,some 11,some 4294967295] := by decide
theorem staged_exact : (result.toOption.map Machine.sharedMem) =
    some [some 4294967295,some 11] := by decide
theorem schedule_same_words : result.toOption.map Machine.globalMem =
    sequentialResult.toOption.map Machine.globalMem := by decide
theorem generic_post : ∃ m, result = .ok m ∧ Post pair m := by
  let m := result.toOption.getD start
  have hs : result = .ok m := by decide
  have hd : m.threads.all (fun t => t.status == .done) = true := by decide
  exact ⟨m,hs,correct pair _ _ (initial_pre _) (run_sound hs) hd⟩

def partialArrival := run code (List.replicate 11 (.thread 0)) start
theorem reject_partial_release : partialArrival.bind release = .error .barrierMismatch := by decide
theorem waiting_thread_is_blocked :
    run code (List.replicate 12 (.thread 0)) start = .error .blocked := by decide

def reverseConfig (x y : Nat) : Config := {
  toConfig := {
    src := 3, dst := 0, n := 2, count := 2
    input i := if i = 0 then x else y
    before := [none,none,some 777,some (word x),some (word y),some 888]
    coverage := by decide
    count32 := by decide
    src64 := by decide
    dst64 := by decide
    srcBound := by simp
    dstBound := by simp
    disjoint := Or.inr (by decide)
    initialized := by
      intro i hi
      have h : i = 0 ∨ i = 1 := by omega
      rcases h with rfl | rfl <;> simp
  }
  n_two := rfl
  count_two := rfl
}

def reverse := reverseConfig 0 4294967295
def reverseResult := run code sequential (initial reverse)
theorem reverse_words_frame : reverseResult.toOption.map Machine.globalMem =
    some [some 4294967295,some 0,some 777,some 0,some 4294967295,some 888] := by decide
theorem reverse_generic_post : ∃ m, reverseResult = .ok m ∧ Post reverse m := by
  let m := reverseResult.toOption.getD (initial reverse)
  have hs : reverseResult = .ok m := by decide
  have hd : m.threads.all (fun t => t.status == .done) = true := by decide
  exact ⟨m,hs,correct reverse _ _ (initial_pre _) (run_sound hs) hd⟩

end Ptx.SharedInstances
