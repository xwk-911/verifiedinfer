import Ptx.Kernels.MoeExpertsRoute

/-! The actual expert-plane selection, including both source branches. Plane
arithmetic stays modular until later layout/footprint bounds eliminate wrap. -/
namespace Ptx.MoeExperts
open Ptx.ISA Ptx.Scalar Ptx.MoeExpertsLoop
noncomputable section

def wBase (i : Inputs) (expert : Nat) : Nat := i.w+expert*(4*(i.k*i.n))
def hBase (i : Inputs) (expert : Nat) : Nat := i.h+expert*(4*(i.m*i.n))
structure Selected (i : Inputs) (ctx : Scalar.Context) (expert : Nat) (s : Scalar.State) : Prop where
  running : s.core.thread.status = .running
  pcValue : s.core.thread.pc = 34
  queries : s.core.queries = 1
  x : lookup "%x" s.core.thread.regs = some i.x
  w : lookup "%w" s.core.thread.regs = some (wrap 64 (wBase i expert))
  h : lookup "%h" s.core.thread.regs = some (wrap 64 (hBase i expert))
  m : lookup "%m" s.core.thread.regs = some i.m
  n : lookup "%n" s.core.thread.regs = some i.n
  k : lookup "%kmax" s.core.thread.regs = some i.k
  rowValue : lookup "%row" s.core.thread.regs = some (row ctx.block ctx.id)
  colValue : lookup "%col" s.core.thread.regs = some (col ctx.block ctx.id)
  expertValue : lookup "%e" s.core.thread.regs = some expert
  banks : BanksDisjoint s

theorem zero_selected {i ctx s} (hi : Loaded i ctx 0 34 s) : Selected i ctx 0 s := by
  refine ⟨hi.running,hi.pcValue,hi.queries,hi.x,?_,?_,hi.m,hi.n,hi.k,hi.rowValue,hi.colValue,hi.expertValue,hi.banks⟩
  · simpa [wBase,show wrap 64 i.w = i.w from Nat.mod_eq_of_lt i.w64] using hi.w
  · simpa [hBase,show wrap 64 i.h = i.h from Nat.mod_eq_of_lt i.h64] using hi.h

theorem plane_run (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {s : Scalar.State} (hi : Loaded i ctx 1 28 s) :
    ∃ next, Scalar.run ctx oracle code 6 s = .ok (next,[]) ∧ Selected i ctx 1 next := by
  let s1 := intAssign s "%plane" (wrap 64 (i.k*i.n))
  let s2 := intAssign s1 "%plane" (wrap 64 (4*(i.k*i.n)))
  let s3 := intAssign s2 "%w" (wrap 64 (wBase i 1))
  let s4 := intAssign s3 "%plane" (wrap 64 (i.m*i.n))
  let s5 := intAssign s4 "%plane" (wrap 64 (4*(i.m*i.n)))
  let s6 := intAssign s5 "%h" (wrap 64 (hBase i 1))
  have hm : wrap 32 i.m = i.m := Nat.mod_eq_of_lt i.m32
  have hn : wrap 32 i.n = i.n := Nat.mod_eq_of_lt i.n32
  have hk : wrap 32 i.k = i.k := Nat.mod_eq_of_lt i.k32
  have hw : wrap 64 i.w = i.w := Nat.mod_eq_of_lt i.w64
  have hh : wrap 64 i.h = i.h := Nat.mod_eq_of_lt i.h64
  have h0 : Scalar.step ctx oracle code s = .ok (s1,[]) := by
    apply integer_local_step (instruction := .bin .mul 32 64 "%plane" (.reg "%kmax") (.reg "%n"))
      (by simpa [intAssign,finishInteger,assign,advance] using hi.running)
      (by simp [intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.moe_experts.program])
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,hi.m,hi.n,hi.k,hi.w,hi.h,hm,hn,hk,hw,hh,wBase,hBase,
      wrap_mul,wrap_add_right,Nat.mul_comm,bind,Except.bind,pure,Except.pure]
  have h1 : Scalar.step ctx oracle code s1 = .ok (s2,[]) := by
    apply integer_local_step (instruction := .bin .mul 64 64 "%plane" (.reg "%plane") (.imm 4))
      (by simpa [s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simp [s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.moe_experts.program])
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s1,hi.m,hi.n,hi.k,hi.w,hi.h,hm,hn,hk,hw,hh,wBase,hBase,
      wrap_mul,wrap_add_right,Nat.mul_comm,bind,Except.bind,pure,Except.pure]
  have h2 : Scalar.step ctx oracle code s2 = .ok (s3,[]) := by
    apply integer_local_step (instruction := .bin .add 64 64 "%w" (.reg "%w") (.reg "%plane"))
      (by simpa [s2,s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simp [s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.moe_experts.program])
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s2,s1,hi.m,hi.n,hi.k,hi.w,hi.h,hm,hn,hk,hw,hh,wBase,hBase,
      wrap_mul,wrap_add_right,Nat.mul_comm,bind,Except.bind,pure,Except.pure]
  have h3 : Scalar.step ctx oracle code s3 = .ok (s4,[]) := by
    apply integer_local_step (instruction := .bin .mul 32 64 "%plane" (.reg "%m") (.reg "%n"))
      (by simpa [s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simp [s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.moe_experts.program])
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s3,s2,s1,hi.m,hi.n,hi.k,hi.w,hi.h,hm,hn,hk,hw,hh,wBase,hBase,
      wrap_mul,wrap_add_right,Nat.mul_comm,bind,Except.bind,pure,Except.pure]
  have h4 : Scalar.step ctx oracle code s4 = .ok (s5,[]) := by
    apply integer_local_step (instruction := .bin .mul 64 64 "%plane" (.reg "%plane") (.imm 4))
      (by simpa [s4,s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simp [s4,s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.moe_experts.program])
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s4,s3,s2,s1,hi.m,hi.n,hi.k,hi.w,hi.h,hm,hn,hk,hw,hh,wBase,hBase,
      wrap_mul,wrap_add_right,Nat.mul_comm,bind,Except.bind,pure,Except.pure]
  have h5 : Scalar.step ctx oracle code s5 = .ok (s6,[]) := by
    apply integer_local_step (instruction := .bin .add 64 64 "%h" (.reg "%h") (.reg "%plane"))
      (by simpa [s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simp [s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.moe_experts.program])
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s5,s4,s3,s2,s1,hi.m,hi.n,hi.k,hi.w,hi.h,hm,hn,hk,hw,hh,wBase,hBase,
      wrap_mul,wrap_add_right,Nat.mul_comm,bind,Except.bind,pure,Except.pure]
  have hr : Scalar.run ctx oracle code 6 s = .ok (s6,[]) := by
    simp [Scalar.run,h0,h1,h2,h3,h4,h5,Except.bind]
  refine ⟨s6,hr,?_⟩
  constructor
  · simpa [s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running
  · simp [s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue]
  · exact hi.queries
  · simpa [s6,s5,s4,s3,s2,s1] using hi.x
  · simp [s6,s5,s4,s3]
  · simp [s6]
  · simpa [s6,s5,s4,s3,s2,s1] using hi.m
  · simpa [s6,s5,s4,s3,s2,s1] using hi.n
  · simpa [s6,s5,s4,s3,s2,s1] using hi.k
  · simpa [s6,s5,s4,s3,s2,s1] using hi.rowValue
  · simpa [s6,s5,s4,s3,s2,s1] using hi.colValue
  · simpa [s6,s5,s4,s3,s2,s1] using hi.expertValue
  · exact run_banks_disjoint hr hi.banks

def selectSteps (expert : Nat) : Nat := if expert = 0 then 4 else 10

theorem select_run (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) {expert : Nat}
    {s : Scalar.State} (hi : Loaded i ctx expert 24 s) (he : expert < 2) :
    ∃ next, Scalar.run ctx oracle code (selectSteps expert) s = .ok (next,[]) ∧ Selected i ctx expert next := by
  have h32 : expert < 2^32 := by omega
  let mid := afterGuard s 0 26
  have hguard : Scalar.run ctx oracle code 2 s = .ok (mid,[]) := by
    simpa [mid,Nat.not_le_of_lt he] using route_guard i ctx oracle hi h32
  have hmid : Loaded i ctx expert 26 mid := loaded_guard_facts hi 0 26
  rcases (show expert = 0 ∨ expert = 1 by omega) with rfl | rfl
  · have hbranch := expert_branch i ctx oracle hmid (by decide)
    have hf := loaded_guard_facts hmid 1 34
    have hr := run_append hguard hbranch
    exact ⟨_,by simpa [selectSteps] using hr,zero_selected hf⟩
  · have hbranch := expert_branch i ctx oracle hmid (by decide)
    have hf := loaded_guard_facts hmid 0 28
    obtain ⟨next,hplane,hselected⟩ := plane_run i ctx oracle hf
    have hr := run_append (run_append hguard hbranch) hplane
    exact ⟨next,by simpa [selectSteps] using hr,hselected⟩

end
end Ptx.MoeExperts
