import Ptx.Kernels.MoeExpertsGuards

/-! The actual first u32 route load. Neither its integer reply nor the selected
expert is prescribed by the precondition. Gate/route memory agreement is later. -/
namespace Ptx.MoeExperts
open Ptx.ISA Ptx.Scalar Ptx.MoeExpertsLoop
noncomputable section

def beforeRoute (i : Inputs) (ctx : Scalar.Context) : Scalar.State :=
  let s1 := intAssign (active i ctx) "%rp" (4*row ctx.block ctx.id)
  intAssign s1 "%rp" (i.r+4*row ctx.block ctx.id)

theorem rp_assign_facts {i ctx pc query s} (hi : At i ctx pc s query) (value : Nat) :
    At i ctx (pc+1) (intAssign s "%rp" value) query := by
  constructor
  · exact hi.running
  · simp [intAssign,finishInteger,assign,advance,hi.pcValue]
  · exact hi.queries
  · simpa using hi.x
  · simpa using hi.w
  · simpa using hi.r
  · simpa using hi.h
  · simpa using hi.m
  · simpa using hi.n
  · simpa using hi.k
  · simpa using hi.rowValue
  · simpa using hi.colValue
  · exact finish_integer_disjoint _ _

theorem route_pointer_run (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : IndexBounds ctx) (hr : row ctx.block ctx.id < i.m)
    (hc : col ctx.block ctx.id < i.n) (hptr : i.r+4*row ctx.block ctx.id < 2^64) :
    Scalar.run ctx oracle code 23 {} = .ok (beforeRoute i ctx,[]) ∧ At i ctx 23 (beforeRoute i ctx) 0 := by
  obtain ⟨hprefix,hi⟩ := active_prefix i ctx oracle hp hb hr hc
  let s := active i ctx
  let s1 := intAssign s "%rp" (4*row ctx.block ctx.id)
  let s2 := intAssign s1 "%rp" (i.r+4*row ctx.block ctx.id)
  have hw : wrap 64 (4*row ctx.block ctx.id) = 4*row ctx.block ctx.id :=
    Nat.mod_eq_of_lt (by have := hb.rowBound; omega)
  have h0 : Scalar.step ctx oracle code s = .ok (s1,[]) := by
    apply integer_local_step (instruction := .bin .mul 32 64 "%rp" (.reg "%row") (.imm 4)) hi.running
      (by rw [hi.pcValue]; rfl) rfl (by intro bid h; cases h)
    simp [s,localStep,Ptx.eval,hi.rowValue,show wrap 32 (row ctx.block ctx.id) = row ctx.block ctx.id from Nat.mod_eq_of_lt hb.rowBound,
      show wrap 32 4 = 4 by decide,Nat.mul_comm,hw,bind,Except.bind,pure,Except.pure]
  have h1 : Scalar.step ctx oracle code s1 = .ok (s2,[]) := by
    apply integer_local_step (instruction := .bin .add 64 64 "%rp" (.reg "%r") (.reg "%rp"))
      (by simpa [s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simp [s1,s,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.moe_experts.program])
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s1,s,hi.r,hw,show wrap 64 i.r = i.r from Nat.mod_eq_of_lt i.r64,
      show wrap 64 (i.r+4*row ctx.block ctx.id) = i.r+4*row ctx.block ctx.id from Nat.mod_eq_of_lt hptr,
      bind,Except.bind,pure,Except.pure]
  have hbody : Scalar.run ctx oracle code 2 s = .ok (s2,[]) := by simp [Scalar.run,h0,h1,Except.bind]
  change Scalar.run ctx oracle code 23 {} = .ok (s2,[]) ∧ At i ctx 23 s2 0
  exact ⟨run_append hprefix hbody,rp_assign_facts (rp_assign_facts hi _) _⟩

structure Loaded (i : Inputs) (ctx : Scalar.Context) (expert pc : Nat) (s : Scalar.State) extends At i ctx pc s 1 where
  expertValue : lookup "%e" s.core.thread.regs = some expert

theorem route_load (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) {value : Nat}
    (hi : At i ctx 23 (beforeRoute i ctx) 0) (hptr : i.r+4*row ctx.block ctx.id < 2^64)
    (hq : oracle 0 = .integer value) :
    Scalar.step ctx oracle code (beforeRoute i ctx) = .ok
      (loadedInteger (beforeRoute i ctx) "%e" value,
        [.read ⟨.global,i.r+4*row ctx.block ctx.id⟩ (u32Bytes (wrap 32 value))]) := by
  have h := integer_load_step (ctx := ctx) (oracle := oracle) (code := code)
    (space := .global) (dst := "%e") (address := {base := .reg "%rp"})
    (addr := i.r+4*row ctx.block ctx.id) (value := value) hi.running (by rw [hi.pcValue]; rfl)
    (by simp [evalAddr,Ptx.eval,beforeRoute,
      show wrap 64 (i.r+4*row ctx.block ctx.id) = i.r+4*row ctx.block ctx.id from Nat.mod_eq_of_lt hptr])
    (by simpa only [hi.queries] using hq)
  simpa only [loadedInteger,u32Bytes,Location.resolve] using h

theorem loaded_facts (i : Inputs) (ctx : Scalar.Context) (value : Nat) {s : Scalar.State} (hi : At i ctx 23 s 0) :
    Loaded i ctx (wrap 32 value) 24 (loadedInteger s "%e" value) := by
  refine ⟨?_,by simp⟩
  constructor
  · exact hi.running
  · simp [loadedInteger,finishInteger,assign,advance,hi.pcValue]
  · change s.core.queries+1 = 1
    rw [hi.queries]
  · simpa using hi.x
  · simpa using hi.w
  · simpa using hi.r
  · simpa using hi.h
  · simpa using hi.m
  · simpa using hi.n
  · simpa using hi.k
  · simpa using hi.rowValue
  · simpa using hi.colValue
  · exact finish_integer_disjoint _ _

theorem loaded_guard_facts {i ctx expert pc s} (hi : Loaded i ctx expert pc s) (flag nextPC : Nat) :
    Loaded i ctx expert nextPC (afterGuard s flag nextPC) :=
  ⟨after_guard_facts hi.toAt flag nextPC,by simpa [afterGuard] using hi.expertValue⟩

theorem route_guard (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) {expert : Nat}
    {s : Scalar.State} (hi : Loaded i ctx expert 24 s) (he : expert < 2^32) :
    Scalar.run ctx oracle code 2 s = .ok
      (afterGuard s (if expert ≥ 2 then 1 else 0) (if expert ≥ 2 then 56 else 26),[]) := by
  have h := ge_operand_branch_run (ctx := ctx) (oracle := oracle) (code := code) hi.running (by rw [hi.pcValue]; rfl) (by rw [hi.pcValue]; rfl)
    (by simp [Ptx.eval,hi.expertValue]) rfl he (by decide)
  simpa only [hi.pcValue,afterGuard] using h

theorem expert_branch (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) {expert : Nat}
    {s : Scalar.State} (hi : Loaded i ctx expert 26 s) (he : expert < 2^32) :
    Scalar.run ctx oracle code 2 s = .ok
      (afterGuard s (if expert = 0 then 1 else 0) (if expert = 0 then 34 else 28),[]) := by
  have h := eq_branch_run (ctx := ctx) (oracle := oracle) (code := code) hi.running (by rw [hi.pcValue]; rfl) (by rw [hi.pcValue]; rfl)
    (by simp [Ptx.eval,hi.expertValue]) rfl he (by decide)
  simpa only [hi.pcValue,afterGuard] using h

end
end Ptx.MoeExperts
