import Ptx.Kernels.SharedSwap
import Ptx.Rules.Termination

/-! Completion of the ORIGINAL SharedSwap interpreter program for every original
configuration and invariant state. The potential pays once for the real collective
release; no synchronization is inserted and no fairness assumption is required.
-/
namespace Ptx.SharedCompletion
open SharedContract Termination

def work (m : Machine) := potential (threadWork 17) m.threads + (1-m.epoch)

theorem instruction_forward {pc : Nat} {i : Instr} (hc : code[pc]? = some i) : ForwardAt pc i := by
  have hm : i ∈ code := List.mem_of_getElem? hc
  simp only [code,Generated.shared_swap.program,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    trivial

theorem threadStep_decreases {c m tid m'} (hi : Inv c m)
    (hs : threadStep code tid m = .ok m') : work m' < work m := by
  cases ht : m.threads[tid]? with
  | none => simp [threadStep,ht,bind,Except.bind] at hs
  | some t =>
    have hit := hi.threads tid t ht
    cases hr : t.status with
    | done => simp [threadStep,ht,hr,bind,Except.bind] at hs
    | waiting bid => simp [threadStep,ht,hr,bind,Except.bind] at hs
    | running =>
      have hepoch : m'.epoch = m.epoch := by
        obtain ⟨mid,hmid,_,he,_⟩ := thread_rule hi ht hr
        rw [hs] at hmid
        cases hmid
        exact he
      obtain ⟨i,t',hc,hthreads,hkind⟩ := threadStep_shape ht hr hs
      have hdrop : threadWork 17 t' < threadWork 17 t := by
        rcases hkind with ⟨_,hlocal⟩ | ⟨hpc,hstatus⟩
        · exact local_work_decreases hr (by have := hit.1.1; omega) (instruction_forward hc) hlocal
        · simp only [threadWork,hstatus,hr,hpc,reduceCtorEq,↓reduceIte]
          have := hit.1.1
          omega
      have hpot : potential (threadWork 17) m'.threads < potential (threadWork 17) m.threads := by
        rw [hthreads]
        exact potential_set_lt ht hdrop
      simpa only [work,hepoch] using Nat.add_lt_add_right hpot (1-m.epoch)

theorem release_decreases {c m m'} (hi : Inv c m) (hs : release m = .ok m') : work m' < work m := by
  obtain ⟨he,hall,rfl⟩ := release_shape hi hs
  have hwait : ∀ t ∈ m.threads, t.status = .waiting 0 := by
    intro t ht
    have h := List.all_eq_true.mp hall t ht
    simpa using h
  have hpot : potential (threadWork 17) (released m).threads = potential (threadWork 17) m.threads := by
    apply potential_map_eq
    intro t ht
    simp [threadWork,hwait t ht]
  change potential (threadWork 17) (released m).threads + (1-(m.epoch+1)) <
    potential (threadWork 17) m.threads + (1-m.epoch)
  rw [hpot,he]
  omega

theorem step_decreases {c m m' action} (hi : Inv c m) (hs : step code action m = .ok m') : work m' < work m := by
  cases action with
  | thread tid => exact threadStep_decreases hi hs
  | release => exact release_decreases hi hs

theorem complete_from_invariant {c m} (hi : Inv c m) :
    ∃ m', Steps code m m' ∧ m'.threads.all (fun t => t.status == .done) = true := by
  apply completed_execution work (invariant c) _ hi
  intro current hcurrent hn
  obtain ⟨action,next,hs⟩ := invariant_progress hcurrent hn
  exact ⟨action,next,hs,step_decreases hcurrent hs⟩

theorem complete_from_pre {c m} (hp : Pre c m) :
    ∃ m', Steps code m m' ∧ m'.threads.all (fun t => t.status == .done) = true ∧ Post c m' := by
  obtain ⟨m',hs,hd⟩ := complete_from_invariant (pre_invariant hp)
  exact ⟨m',hs,hd,correct c m m' hp hs hd⟩

end Ptx.SharedCompletion
