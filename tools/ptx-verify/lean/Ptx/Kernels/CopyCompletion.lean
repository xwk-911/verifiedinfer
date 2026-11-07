import Ptx.Kernels.Copy
import Ptx.Rules.Termination

/-! Completion witnesses for arbitrary original Copy configurations and reachable
invariant states. No positive launch-count premise is needed in the operational
model: the zero-thread CPU/no-launch state is already complete.
-/
namespace Ptx.CopyCompletion
open CopyContract Termination

def work (m : Machine) := potential (threadWork 12) m.threads

theorem instruction_forward {pc : Nat} {i : Instr} (hb : pc ≤ 11)
    (hc : code[pc]? = some i) : ForwardAt pc i := by
  have hcases : pc = 0 ∨ pc = 1 ∨ pc = 2 ∨ pc = 3 ∨ pc = 4 ∨ pc = 5 ∨
      pc = 6 ∨ pc = 7 ∨ pc = 8 ∨ pc = 9 ∨ pc = 10 ∨ pc = 11 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [code,Generated.copy.program] at hc <;> subst i <;> simp [ForwardAt]

theorem threadStep_decreases {c m tid m'} (hi : Inv c m)
    (hs : threadStep code tid m = .ok m') : work m' < work m := by
  cases ht : m.threads[tid]? with
  | none => simp [threadStep,ht,bind,Except.bind] at hs
  | some t =>
    have hit := hi.threads tid t ht
    rcases hit.1 with hr | hd
    · obtain ⟨i,t',hc,hthreads,hkind⟩ := threadStep_shape ht hr hs
      have hdrop : threadWork 12 t' < threadWork 12 t := by
        rcases hkind with ⟨_,hlocal⟩ | ⟨hpc,hstatus⟩
        · exact local_work_decreases hr (by have := hit.2.1; omega)
            (instruction_forward hit.2.1 hc) hlocal
        · simp only [threadWork,hstatus,hr,hpc,reduceCtorEq,↓reduceIte]
          have := hit.2.1
          omega
      simpa only [work,hthreads] using potential_set_lt ht hdrop
    · simp [threadStep,ht,hd,bind,Except.bind] at hs

theorem decreasing_progress (m : Machine) {c} (hi : Inv c m)
    (hn : m.threads.all (fun t => t.status == .done) ≠ true) :
    ∃ action next, step code action m = .ok next ∧ work next < work m := by
  have hf : m.threads.all (fun t => t.status == .done) = false := Bool.eq_false_iff.mpr hn
  obtain ⟨t,ht,hnd⟩ := List.all_eq_false.mp hf
  have hnd : t.status ≠ .done := by simpa using hnd
  obtain ⟨tid,hget⟩ := List.mem_iff_getElem?.mp ht
  have hr : t.status = .running := (hi.threads tid t hget).1.resolve_right hnd
  obtain ⟨next,hnext,_⟩ := thread_rule hi hget hr
  exact ⟨.thread tid,next,hnext,threadStep_decreases hi hnext⟩

theorem complete_from_invariant {c m} (hi : Inv c m) :
    ∃ m', Steps code m m' ∧ m'.threads.all (fun t => t.status == .done) = true :=
  completed_execution work (invariant c) (fun m hi hn => decreasing_progress m hi hn) hi

theorem complete_from_pre {c m} (hp : CopyContract.Pre c m) :
    ∃ m', Steps code m m' ∧ m'.threads.all (fun t => t.status == .done) = true ∧ Post c m' := by
  obtain ⟨m',hs,hd⟩ := complete_from_invariant (pre_invariant hp)
  exact ⟨m',hs,hd,correct c m m' hp hs hd⟩

end Ptx.CopyCompletion
