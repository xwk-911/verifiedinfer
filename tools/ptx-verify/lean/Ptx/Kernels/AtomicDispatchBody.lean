import Ptx.Kernels.AtomicDispatchTrace
import Ptx.Scalar.Control

/-! Every data-dependent branch of the actual atomic-dispatch source. The ticket
is arbitrary here; only a separate memory proof can restrict it to {0,1}. -/
namespace Ptx.AtomicDispatchTrace
open Ptx.ISA Ptx.Scalar
noncomputable section

def bodyEntry (counter x y ticket : Nat) : Scalar.State := {
  core := {thread := {pc := 4,regs := [("%r0",ticket),("%rd2",y),("%rd1",x),("%rd0",counter)]},queries := 1}
}
def checkZero (counter x y ticket : Nat) : Scalar.State :=
  intPC (intAssign (bodyEntry counter x y ticket) "%p0" (if ticket = 0 then 1 else 0)) (if ticket = 0 then 9 else 6)
def checkOne (counter x y ticket : Nat) : Scalar.State :=
  intPC (intAssign (checkZero counter x y ticket) "%p1" (if ticket = 1 then 1 else 0)) (if ticket = 1 then 12 else 8)
def doneState (s : Scalar.State) : Scalar.State :=
  finishInteger s {s.core with thread := {s.core.thread with status := .done}}
def finalState (counter x y ticket : Nat) : Scalar.State :=
  if ticket = 0 then doneState (intPC (intAssign (checkZero counter x y ticket) "%r1" 1) 14)
  else if ticket = 1 then doneState (intPC (intAssign (checkOne counter x y ticket) "%r2" 2) 14)
  else doneState (intPC (checkOne counter x y ticket) 14)
def outputEvents (x y ticket : Nat) : List Scalar.Kind :=
  if ticket = 0 then [.write ⟨.global,x⟩ ((encodeU32 1).map Symbolic.Byte.bits)]
  else if ticket = 1 then [.write ⟨.global,y⟩ ((encodeU32 2).map Symbolic.Byte.bits)] else []
def bodyCount (ticket : Nat) : Nat := if ticket = 1 then 7 else 6

theorem after_atomic_entry (counter x y value : Nat) :
    afterAtomic counter x y value = bodyEntry counter x y (wrap 32 value) := by
  simp [afterAtomic,bodyEntry,ready,finishInteger,assign,advance,put]

theorem zero_guard (ctx : Scalar.Context) (oracle : Scalar.Oracle) (counter x y ticket : Nat)
    (ht : ticket < 2^32) :
    Scalar.run ctx oracle code 2 (bodyEntry counter x y ticket) = .ok (checkZero counter x y ticket,[]) := by
  exact Scalar.eq_branch_run rfl rfl rfl (by simp [Ptx.eval,bodyEntry,lookup]) rfl ht (by decide)

theorem one_guard (ctx : Scalar.Context) (oracle : Scalar.Oracle) (counter x y ticket : Nat)
    (ht : ticket < 2^32) (hzero : ticket ≠ 0) :
    Scalar.run ctx oracle code 2 (checkZero counter x y ticket) = .ok (checkOne counter x y ticket,[]) := by
  have h := Scalar.eq_branch_run (ctx := ctx) (oracle := oracle) (code := code) (s := checkZero counter x y ticket)
    (lhs := .reg "%r0") (rhs := .imm 1) (pred := "%p1") (target := 12)
    (x := ticket) (y := 1) (by simp [checkZero,intPC,intAssign,finishInteger,assign,advance,bodyEntry])
    (by simp [code,Generated.atomic_dispatch.program,checkZero,hzero,intPC,intAssign,finishInteger,assign,advance,bodyEntry])
    (by simp [code,Generated.atomic_dispatch.program,checkZero,hzero,intPC,intAssign,finishInteger,assign,advance,bodyEntry])
    (by simp [Ptx.eval,checkZero,bodyEntry,lookup]) rfl ht (by decide)
  have hpc : (checkZero counter x y ticket).core.thread.pc = 6 := by simp [checkZero,hzero,intPC,finishInteger]
  simpa only [checkOne,hpc,show 6+2 = 8 from rfl] using h

theorem zero_job (ctx : Scalar.Context) (oracle : Scalar.Oracle) (counter x y ticket : Nat)
    (hz : ticket = 0) (hx : x < 2^64) :
    Scalar.run ctx oracle code 4 (checkZero counter x y ticket) =
      .ok (finalState counter x y ticket,outputEvents x y ticket) := by
  let s := checkZero counter x y ticket
  let moved := intAssign s "%r1" 1
  let stored := intPC moved 11
  let leaving := intPC moved 14
  have h0 : Scalar.step ctx oracle code s = .ok (moved,[]) := by
    apply Scalar.integer_local_step (instruction := .mov 32 "%r1" (.imm 1))
      (by simp [s,checkZero,intPC,intAssign,finishInteger,assign,advance,bodyEntry])
      (by simp [s,code,Generated.atomic_dispatch.program,checkZero,hz,intPC,intAssign,finishInteger,assign,advance,bodyEntry]) rfl
      (by intro bid h; cases h)
    simp [localStep,Ptx.eval,wrap,bind,Except.bind,pure,Except.pure]
  have h1 : Scalar.step ctx oracle code moved = .ok (stored,[.write ⟨.global,x⟩ ((encodeU32 1).map Symbolic.Byte.bits)]) := by
    have h := Scalar.integer_store_step (ctx := ctx) (oracle := oracle) (code := code) (s := moved)
      (space := .global) (address := {base := .reg "%rd1"}) (operand := .reg "%r1") (addr := x) (value := 1)
      (by simp [moved,s,checkZero,intAssign,intPC,finishInteger,assign,advance,bodyEntry])
      (by simp [moved,s,code,Generated.atomic_dispatch.program,checkZero,hz,intAssign,intPC,finishInteger,assign,advance,bodyEntry])
      (by simp [evalAddr,Ptx.eval,moved,s,checkZero,bodyEntry,lookup,show wrap 64 x = x from Nat.mod_eq_of_lt hx])
      (by simp [Ptx.eval,moved])
    simpa [stored,moved,s,checkZero,hz,bodyEntry,intAssign,intPC,finishInteger,assign,advance,Location.resolve] using h
  have h2 : Scalar.step ctx oracle code stored = .ok (leaving,[]) := by
    apply Scalar.integer_local_step (instruction := .jump 14)
      (by simp [stored,moved,s,checkZero,intPC,intAssign,finishInteger,assign,advance,bodyEntry])
      (by simp [stored,code,Generated.atomic_dispatch.program,intPC,finishInteger]) rfl (by intro bid h; cases h)
    simp [localStep,stored,intPC,finishInteger,pure,Except.pure]
  have h3 : Scalar.step ctx oracle code leaving = .ok (finalState counter x y ticket,[]) := by
    have h := Scalar.integer_local_step (ctx := ctx) (oracle := oracle) (code := code) (s := leaving)
      (instruction := .ret)
      (by simp [leaving,moved,s,checkZero,intPC,intAssign,finishInteger,assign,advance,bodyEntry])
      (by simp [leaving,code,Generated.atomic_dispatch.program,intPC,finishInteger]) rfl (by intro bid h; cases h) rfl
    simpa [finalState,hz,doneState,leaving,moved,s] using h
  change Scalar.run ctx oracle code 4 s = _
  simp only [Scalar.run,h0,h1,h2,h3,Except.bind,List.nil_append,List.append_nil]
  simp only [outputEvents,ite_eq_left hz]

theorem one_job (ctx : Scalar.Context) (oracle : Scalar.Oracle) (counter x y ticket : Nat)
    (hz : ticket ≠ 0) (hone : ticket = 1) (hy : y < 2^64) :
    Scalar.run ctx oracle code 3 (checkOne counter x y ticket) =
      .ok (finalState counter x y ticket,outputEvents x y ticket) := by
  let s := checkOne counter x y ticket
  let moved := intAssign s "%r2" 2
  let leaving := intPC moved 14
  have h0 : Scalar.step ctx oracle code s = .ok (moved,[]) := by
    apply Scalar.integer_local_step (instruction := .mov 32 "%r2" (.imm 2))
      (by simp [s,checkOne,checkZero,intPC,intAssign,finishInteger,assign,advance,bodyEntry])
      (by simp [s,code,Generated.atomic_dispatch.program,checkOne,hone,intPC,intAssign,finishInteger,assign,advance,checkZero,bodyEntry]) rfl
      (by intro bid h; cases h)
    simp [localStep,Ptx.eval,wrap,bind,Except.bind,pure,Except.pure]
  have h1 : Scalar.step ctx oracle code moved = .ok (leaving,[.write ⟨.global,y⟩ ((encodeU32 2).map Symbolic.Byte.bits)]) := by
    have h := Scalar.integer_store_step (ctx := ctx) (oracle := oracle) (code := code) (s := moved)
      (space := .global) (address := {base := .reg "%rd2"}) (operand := .reg "%r2") (addr := y) (value := 2)
      (by simp [moved,s,checkOne,checkZero,intAssign,intPC,finishInteger,assign,advance,bodyEntry])
      (by simp [moved,s,code,Generated.atomic_dispatch.program,checkOne,hone,intAssign,intPC,finishInteger,assign,advance,checkZero,bodyEntry])
      (by simp [evalAddr,Ptx.eval,moved,s,checkOne,checkZero,bodyEntry,lookup,show wrap 64 y = y from Nat.mod_eq_of_lt hy])
      (by simp [Ptx.eval,moved])
    simpa [leaving,moved,s,checkOne,checkZero,hone,bodyEntry,intAssign,intPC,finishInteger,assign,advance,Location.resolve] using h
  have h2 : Scalar.step ctx oracle code leaving = .ok (finalState counter x y ticket,[]) := by
    have h := Scalar.integer_local_step (ctx := ctx) (oracle := oracle) (code := code) (s := leaving)
      (instruction := .ret)
      (by simp [leaving,moved,s,checkOne,checkZero,intPC,intAssign,finishInteger,assign,advance,bodyEntry])
      (by simp [leaving,code,Generated.atomic_dispatch.program,intPC,finishInteger]) rfl (by intro bid h; cases h) rfl
    simpa [finalState,hz,hone,doneState,leaving,moved,s] using h
  change Scalar.run ctx oracle code 3 s = _
  simp only [Scalar.run,h0,h1,h2,Except.bind,List.nil_append,List.append_nil]
  simp only [outputEvents,ite_eq_right hz,ite_eq_left hone]

theorem no_job (ctx : Scalar.Context) (oracle : Scalar.Oracle) (counter x y ticket : Nat)
    (hz : ticket ≠ 0) (hone : ticket ≠ 1) :
    Scalar.run ctx oracle code 2 (checkOne counter x y ticket) =
      .ok (finalState counter x y ticket,outputEvents x y ticket) := by
  let s := checkOne counter x y ticket
  let leaving := intPC s 14
  have h0 : Scalar.step ctx oracle code s = .ok (leaving,[]) := by
    apply Scalar.integer_local_step (instruction := .jump 14)
      (by simp [s,checkOne,checkZero,intPC,intAssign,finishInteger,assign,advance,bodyEntry])
      (by simp [s,code,Generated.atomic_dispatch.program,checkOne,hone,intPC,intAssign,finishInteger,assign,advance,checkZero,bodyEntry]) rfl
      (by intro bid h; cases h)
    simp [localStep,leaving,pure,Except.pure]
  have h1 : Scalar.step ctx oracle code leaving = .ok (finalState counter x y ticket,[]) := by
    have h := Scalar.integer_local_step (ctx := ctx) (oracle := oracle) (code := code) (s := leaving)
      (instruction := .ret)
      (by simp [leaving,s,checkOne,checkZero,intPC,intAssign,finishInteger,assign,advance,bodyEntry])
      (by simp [leaving,code,Generated.atomic_dispatch.program,intPC,finishInteger]) rfl (by intro bid h; cases h) rfl
    simpa [finalState,hz,hone,doneState,leaving,s] using h
  change Scalar.run ctx oracle code 2 s = _
  simp only [Scalar.run,h0,h1,Except.bind,List.append_nil]
  simp only [outputEvents,ite_eq_right hz,ite_eq_right hone]

theorem body_run (ctx : Scalar.Context) (oracle : Scalar.Oracle) (counter x y ticket : Nat)
    (ht : ticket < 2^32) (hx : x < 2^64) (hy : y < 2^64) :
    Scalar.run ctx oracle code (bodyCount ticket) (bodyEntry counter x y ticket) =
      .ok (finalState counter x y ticket,outputEvents x y ticket) := by
  by_cases hz : ticket = 0
  · have h := Scalar.run_append (zero_guard ctx oracle counter x y ticket ht) (zero_job ctx oracle counter x y ticket hz hx)
    simpa [bodyCount,hz] using h
  · have hg := Scalar.run_append (zero_guard ctx oracle counter x y ticket ht) (one_guard ctx oracle counter x y ticket ht hz)
    by_cases hone : ticket = 1
    · have h := Scalar.run_append hg (one_job ctx oracle counter x y ticket hz hone hy)
      simpa [bodyCount,hone] using h
    · have h := Scalar.run_append hg (no_job ctx oracle counter x y ticket hz hone)
      simpa [bodyCount,hone] using h

theorem final_done (counter x y ticket : Nat) : (finalState counter x y ticket).core.thread.status = .done := by
  unfold finalState
  split
  · rfl
  · split <;> rfl

end
end Ptx.AtomicDispatchTrace
