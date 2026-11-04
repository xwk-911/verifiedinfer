import Ptx.Kernels.Copy

/-! Finite regression instances complement, and do not replace, the universal
copy contract. They exercise empty buffers, masked threads, exact u32 words,
nonserial scheduling, reversed array layout and unrelated frame cells. -/
namespace Ptx.CopyInstances
open CopyContract

def emptyConfig := contiguous [] 3 (by decide) (by decide)
def emptyInitial := initial emptyConfig [some 88]
def emptySchedule : List Action := (List.replicate 7 [.thread 2,.thread 0,.thread 1]).flatten
def emptyResult := run code emptySchedule emptyInitial

theorem empty_no_access : (emptyResult.toOption.map Machine.globalMem) = some [] := by decide
theorem empty_terminates :
    (emptyResult.toOption.map (fun m => m.threads.all (fun t => t.status == .done))) = some true := by decide
theorem empty_shared_frame : (emptyResult.toOption.map Machine.sharedMem) = some [some 88] := by decide

def maskedConfig := contiguous [0,4294967295,4294967303] 5 (by decide) (by decide)
def maskedInitial := initial maskedConfig []
def maskedSchedule : List Action :=
  (List.replicate 6 [.thread 0,.thread 1,.thread 2,.thread 3,.thread 4]).flatten ++
  [.thread 3,.thread 4] ++ (List.replicate 6 [.thread 2,.thread 0,.thread 1]).flatten
def maskedResult := run code maskedSchedule maskedInitial

theorem masked_words : (maskedResult.toOption.map Machine.globalMem) =
    some [some 0,some 4294967295,some 7,some 0,some 4294967295,some 7] := by decide
theorem masked_terminates :
    (maskedResult.toOption.map (fun m => m.threads.all (fun t => t.status == .done))) = some true := by decide
theorem masked_generic_post : ∃ m, maskedResult = .ok m ∧ Post maskedConfig m := by
  let m := maskedResult.toOption.getD maskedInitial
  have hs : maskedResult = .ok m := by decide
  have hd : m.threads.all (fun t => t.status == .done) = true := by decide
  exact ⟨m,hs,correct maskedConfig _ _ (initial_pre _ _) (run_sound hs) hd⟩

def reverseConfig : Config where
  src := 3
  dst := 0
  n := 2
  count := 4
  input i := if i = 0 then 10 else 20
  before := [none,none,some 777,some 10,some 20,some 888]
  coverage := by decide
  count32 := by decide
  src64 := by decide
  dst64 := by decide
  srcBound := by decide
  dstBound := by decide
  disjoint := Or.inr (by decide)
  initialized := by
    intro i hi
    have h : i = 0 ∨ i = 1 := by omega
    rcases h with rfl | rfl <;> decide

def reverseInitial := initial reverseConfig [some 91,some 92]
def reverseSchedule : List Action :=
  (List.replicate 6 [.thread 3,.thread 2,.thread 1,.thread 0]).flatten ++
  [.thread 2,.thread 3] ++ (List.replicate 6 [.thread 1,.thread 0]).flatten
def reverseResult := run code reverseSchedule reverseInitial

theorem reverse_words_and_frame : (reverseResult.toOption.map Machine.globalMem) =
    some [some 10,some 20,some 777,some 10,some 20,some 888] := by decide
theorem reverse_generic_post : ∃ m, reverseResult = .ok m ∧ Post reverseConfig m := by
  let m := reverseResult.toOption.getD reverseInitial
  have hs : reverseResult = .ok m := by decide
  have hd : m.threads.all (fun t => t.status == .done) = true := by decide
  exact ⟨m,hs,correct reverseConfig _ _ (initial_pre _ _) (run_sound hs) hd⟩

end Ptx.CopyInstances
