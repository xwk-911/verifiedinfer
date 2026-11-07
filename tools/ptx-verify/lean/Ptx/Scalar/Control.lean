import Ptx.Scalar.Updates

/-! Two-instruction unsigned comparison/branch rules over the fixed interpreter.
Both branches are kept; no inactive thread is discarded by a specification. -/
namespace Ptx.Scalar
noncomputable section

theorem ge_operand_branch_run {ctx oracle code s lhs rhs pred target x y}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.integer (.setp .ge pred lhs rhs)))
    (hb : code[s.core.thread.pc+1]? = some (.integer (.branch pred true target)))
    (hx : Ptx.eval ctx.id.tid.x s.core.thread lhs = .ok x) (hy : Ptx.eval ctx.id.tid.x s.core.thread rhs = .ok y)
    (x32 : x < 2^32) (y32 : y < 2^32) :
    run ctx oracle code 2 s = .ok
      (intPC (intAssign s pred (if x ≥ y then 1 else 0)) (if x ≥ y then target else s.core.thread.pc+2),[]) := by
  let flag := if x ≥ y then 1 else 0
  let mid := intAssign s pred flag
  let next := intPC mid (if x ≥ y then target else s.core.thread.pc+2)
  have h0 : step ctx oracle code s = .ok (mid,[]) := by
    apply integer_local_step hr hc rfl (by intro bid h; cases h)
    simp [localStep,hx,hy,flag,show wrap 32 x = x from Nat.mod_eq_of_lt x32,
      show wrap 32 y = y from Nat.mod_eq_of_lt y32,bind,Except.bind,pure,Except.pure]
  have h1 : step ctx oracle code mid = .ok (next,[]) := by
    apply integer_local_step (instruction := .branch pred true target)
      (by simpa [mid,intAssign,finishInteger,assign,advance] using hr)
      (by simpa [mid,intAssign,finishInteger,assign,advance] using hb) rfl (by intro bid h; cases h)
    by_cases h : x ≥ y <;>
      simp [localStep,mid,intAssign,finishInteger,assign,advance,flag,h,bind,Except.bind,pure,Except.pure]
  simp [run,h0,h1,Except.bind,mid,next,flag]

theorem ge_branch_run {ctx oracle code s lhs rhs pred target x y}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.integer (.setp .ge pred (.reg lhs) (.reg rhs))))
    (hb : code[s.core.thread.pc+1]? = some (.integer (.branch pred true target)))
    (hx : lookup lhs s.core.thread.regs = some x) (hy : lookup rhs s.core.thread.regs = some y)
    (x32 : x < 2^32) (y32 : y < 2^32) :
    run ctx oracle code 2 s = .ok
      (intPC (intAssign s pred (if x ≥ y then 1 else 0)) (if x ≥ y then target else s.core.thread.pc+2),[]) := by
  exact ge_operand_branch_run hr hc hb (by simp [Ptx.eval,hx]) (by simp [Ptx.eval,hy]) x32 y32

theorem eq_branch_run {ctx oracle code s lhs rhs pred target x y}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.integer (.setp .eq pred lhs rhs)))
    (hb : code[s.core.thread.pc+1]? = some (.integer (.branch pred true target)))
    (hx : Ptx.eval ctx.id.tid.x s.core.thread lhs = .ok x)
    (hy : Ptx.eval ctx.id.tid.x s.core.thread rhs = .ok y)
    (x32 : x < 2^32) (y32 : y < 2^32) :
    run ctx oracle code 2 s = .ok
      (intPC (intAssign s pred (if x = y then 1 else 0)) (if x = y then target else s.core.thread.pc+2),[]) := by
  let flag := if x = y then 1 else 0
  let mid := intAssign s pred flag
  let next := intPC mid (if x = y then target else s.core.thread.pc+2)
  have h0 : step ctx oracle code s = .ok (mid,[]) := by
    apply integer_local_step hr hc rfl (by intro bid h; cases h)
    simp [localStep,hx,hy,flag,show wrap 32 x = x from Nat.mod_eq_of_lt x32,
      show wrap 32 y = y from Nat.mod_eq_of_lt y32,bind,Except.bind,pure,Except.pure]
  have h1 : step ctx oracle code mid = .ok (next,[]) := by
    apply integer_local_step (instruction := .branch pred true target)
      (by simpa [mid,intAssign,finishInteger,assign,advance] using hr)
      (by simpa [mid,intAssign,finishInteger,assign,advance] using hb) rfl (by intro bid h; cases h)
    by_cases h : x = y <;>
      simp [localStep,mid,intAssign,finishInteger,assign,advance,flag,h,bind,Except.bind,pure,Except.pure]
  simp [run,h0,h1,Except.bind,mid,next,flag]

end
end Ptx.Scalar
