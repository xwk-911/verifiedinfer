import Ptx.Kernels.MoeExpertsInit
import Ptx.Scalar.Control

/-! Checked row/column masking for arbitrary parameterized threads. Inactive
threads execute the actual return and emit no memory events. -/
namespace Ptx.MoeExperts
open Ptx.ISA Ptx.Scalar Ptx.MoeExpertsLoop
noncomputable section

structure At (i : Inputs) (ctx : Scalar.Context) (pc : Nat) (s : Scalar.State) (query : Nat) : Prop where
  running : s.core.thread.status = .running
  pcValue : s.core.thread.pc = pc
  queries : s.core.queries = query
  x : lookup "%x" s.core.thread.regs = some i.x
  w : lookup "%w" s.core.thread.regs = some i.w
  r : lookup "%r" s.core.thread.regs = some i.r
  h : lookup "%h" s.core.thread.regs = some i.h
  m : lookup "%m" s.core.thread.regs = some i.m
  n : lookup "%n" s.core.thread.regs = some i.n
  k : lookup "%kmax" s.core.thread.regs = some i.k
  rowValue : lookup "%row" s.core.thread.regs = some (row ctx.block ctx.id)
  colValue : lookup "%col" s.core.thread.regs = some (col ctx.block ctx.id)
  banks : BanksDisjoint s

theorem indexed_facts (i : Inputs) (ctx : Scalar.Context) (hp : Params i ctx.params) (hb : IndexBounds ctx) :
    At i ctx 17 (indexed i ctx) 0 := by
  constructor
  · rfl
  · rfl
  · rfl
  · simp [indexed]
  · simp [indexed]
  · simp [indexed]
  · simp [indexed]
  · simp [indexed]
  · simp [indexed]
  · simp [indexed]
  · simp [indexed]
  · simp [indexed]
  · exact run_banks_disjoint (index_run i ctx (fun _ => .integer 0) hp hb) empty_banks_disjoint

def afterGuard (s : Scalar.State) (flag pc : Nat) : Scalar.State := intPC (intAssign s "%p" flag) pc

theorem after_guard_facts {i ctx pc s query} (hi : At i ctx pc s query) (flag nextPC : Nat) :
    At i ctx nextPC (afterGuard s flag nextPC) query := by
  constructor
  · simpa [afterGuard,intPC,intAssign,finishInteger,assign,advance] using hi.running
  · rfl
  · simpa [afterGuard,intPC,intAssign,finishInteger] using hi.queries
  · simpa [afterGuard] using hi.x
  · simpa [afterGuard] using hi.w
  · simpa [afterGuard] using hi.r
  · simpa [afterGuard] using hi.h
  · simpa [afterGuard] using hi.m
  · simpa [afterGuard] using hi.n
  · simpa [afterGuard] using hi.k
  · simpa [afterGuard] using hi.rowValue
  · simpa [afterGuard] using hi.colValue
  · exact finish_integer_disjoint _ _

theorem row_guard_run (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {s : Scalar.State} (hi : At i ctx 17 s 0) (hb : IndexBounds ctx) :
    Scalar.run ctx oracle code 2 s = .ok
      (afterGuard s (if row ctx.block ctx.id ≥ i.m then 1 else 0)
        (if row ctx.block ctx.id ≥ i.m then 56 else 19),[]) := by
  have h := ge_branch_run (ctx := ctx) (oracle := oracle) hi.running
    (show code[s.core.thread.pc]? = some (.integer (.setp .ge "%p" (.reg "%row") (.reg "%m"))) from by rw [hi.pcValue]; rfl)
    (show code[s.core.thread.pc+1]? = some (.integer (.branch "%p" true 56)) from by rw [hi.pcValue]; rfl)
    hi.rowValue hi.m hb.rowBound i.m32
  simpa only [hi.pcValue,afterGuard] using h

theorem col_guard_run (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {s : Scalar.State} (hi : At i ctx 19 s 0) (hb : IndexBounds ctx) :
    Scalar.run ctx oracle code 2 s = .ok
      (afterGuard s (if col ctx.block ctx.id ≥ i.n then 1 else 0)
        (if col ctx.block ctx.id ≥ i.n then 56 else 21),[]) := by
  have h := ge_branch_run (ctx := ctx) (oracle := oracle) hi.running
    (show code[s.core.thread.pc]? = some (.integer (.setp .ge "%p" (.reg "%col") (.reg "%n"))) from by rw [hi.pcValue]; rfl)
    (show code[s.core.thread.pc+1]? = some (.integer (.branch "%p" true 56)) from by rw [hi.pcValue]; rfl)
    hi.colValue hi.n hb.colBound i.n32
  simpa only [hi.pcValue,afterGuard] using h

theorem masked_return (ctx : Scalar.Context) (oracle : Scalar.Oracle) {s : Scalar.State}
    (hr : s.core.thread.status = .running) (hp : s.core.thread.pc = 56) :
    ∃ final, Scalar.run ctx oracle code 1 s = .ok (final,[]) ∧
      final.core.thread.status = .done ∧ final.core.queries = s.core.queries := by
  let final := finishInteger s {s.core with thread := {s.core.thread with status := .done}}
  have hstep : Scalar.step ctx oracle code s = .ok (final,[]) := by
    apply integer_local_step hr (by rw [hp]; rfl) rfl (by intro bid h; cases h)
    rfl
  exact ⟨final,by simp [Scalar.run,hstep,Except.bind],rfl,rfl⟩

theorem masked_row (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : IndexBounds ctx) (hr : i.m ≤ row ctx.block ctx.id) :
    ∃ final, Scalar.run ctx oracle code 20 {} = .ok (final,[]) ∧
      final.core.thread.status = .done ∧ final.core.queries = 0 := by
  let checked := afterGuard (indexed i ctx) 1 56
  have hf := indexed_facts i ctx hp hb
  have hg : Scalar.run ctx oracle code 2 (indexed i ctx) = .ok (checked,[]) := by
    simpa only [ite_eq_left hr] using row_guard_run i ctx oracle hf hb
  have hc := after_guard_facts hf 1 56
  obtain ⟨final,hret,hd,hq⟩ := masked_return ctx oracle hc.running hc.pcValue
  have hfull := Scalar.run_append (Scalar.run_append (index_run i ctx oracle hp hb) hg) hret
  exact ⟨final,hfull,hd,hq.trans hc.queries⟩

theorem masked_col (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : IndexBounds ctx)
    (hr : row ctx.block ctx.id < i.m) (hn : i.n ≤ col ctx.block ctx.id) :
    ∃ final, Scalar.run ctx oracle code 22 {} = .ok (final,[]) ∧
      final.core.thread.status = .done ∧ final.core.queries = 0 := by
  let rowPassed := afterGuard (indexed i ctx) 0 19
  let colMasked := afterGuard rowPassed 1 56
  have hf := indexed_facts i ctx hp hb
  have hg : Scalar.run ctx oracle code 2 (indexed i ctx) = .ok (rowPassed,[]) := by
    simpa only [ite_eq_right (Nat.not_le_of_lt hr)] using row_guard_run i ctx oracle hf hb
  have hrow := after_guard_facts hf 0 19
  have hcol : Scalar.run ctx oracle code 2 rowPassed = .ok (colMasked,[]) := by
    simpa only [ite_eq_left hn] using col_guard_run i ctx oracle hrow hb
  have hmask := after_guard_facts hrow 1 56
  obtain ⟨final,hret,hd,hq⟩ := masked_return ctx oracle hmask.running hmask.pcValue
  have hfull := Scalar.run_append (Scalar.run_append (Scalar.run_append (index_run i ctx oracle hp hb) hg) hcol) hret
  exact ⟨final,hfull,hd,hq.trans hmask.queries⟩

def active (i : Inputs) (ctx : Scalar.Context) : Scalar.State :=
  afterGuard (afterGuard (indexed i ctx) 0 19) 0 21

theorem active_prefix (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : IndexBounds ctx)
    (hr : row ctx.block ctx.id < i.m) (hn : col ctx.block ctx.id < i.n) :
    Scalar.run ctx oracle code 21 {} = .ok (active i ctx,[]) ∧ At i ctx 21 (active i ctx) 0 := by
  have hf := indexed_facts i ctx hp hb
  have hrow : Scalar.run ctx oracle code 2 (indexed i ctx) = .ok (afterGuard (indexed i ctx) 0 19,[]) := by
    simpa only [ite_eq_right (Nat.not_le_of_lt hr)] using row_guard_run i ctx oracle hf hb
  have hrf := after_guard_facts hf 0 19
  have hcol : Scalar.run ctx oracle code 2 (afterGuard (indexed i ctx) 0 19) = .ok (active i ctx,[]) := by
    simpa only [active,ite_eq_right (Nat.not_le_of_lt hn)] using col_guard_run i ctx oracle hrf hb
  exact ⟨Scalar.run_append (Scalar.run_append (index_run i ctx oracle hp hb) hrow) hcol,
    after_guard_facts hrf 0 21⟩

end
end Ptx.MoeExperts
