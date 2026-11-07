import Ptx.Generated.AtomicDispatch
import Ptx.Scalar.Atomic
import Ptx.Scalar.Execution

/-! Actual source entry through the atomic instruction, with arbitrary runtime
addresses, thread/context and parameter environment. This prefix does not prove
ticket uniqueness, complete global execution, or a permitted final observation. -/
namespace Ptx.AtomicDispatchTrace
open Ptx.ISA Ptx.Scalar
noncomputable section
abbrev code := Generated.atomic_dispatch.program

def Params (counter x y : Nat) (params : Bindings) : Prop :=
  lookup "Counter" params = some counter ∧ lookup "X" params = some x ∧ lookup "Y" params = some y
def firstParam (counter : Nat) : Scalar.State := {core := {thread := {pc := 1,regs := [("%rd0",counter)]}}}
def secondParam (counter x : Nat) : Scalar.State := {core := {thread := {pc := 2,regs := [("%rd1",x),("%rd0",counter)]}}}
def ready (counter x y : Nat) : Scalar.State := {
  core := {thread := {pc := 3,regs := [("%rd2",y),("%rd1",x),("%rd0",counter)]}}
}
def afterAtomic (counter x y value : Nat) : Scalar.State :=
  finishInteger (ready counter x y) {
    (ready counter x y).core with thread := assign (ready counter x y).core.thread "%r0" (wrap 32 value),queries := 1}

theorem parameters_run (ctx : Scalar.Context) (oracle : Scalar.Oracle) (counter x y : Nat)
    (hp : Params counter x y ctx.params) (hc : counter < 2^64) (hx : x < 2^64) (hy : y < 2^64) :
    Scalar.run ctx oracle code 3 {} = .ok (ready counter x y,[]) := by
  have h0 : Scalar.step ctx oracle code {} = .ok (firstParam counter,[]) := by
    have hlocal : localStep ctx.params ctx.id.tid.x {} (.param 64 "%rd0" "Counter") =
        .ok (firstParam counter).core.thread := by
      simp [localStep,hp.1,show wrap 64 counter = counter from Nat.mod_eq_of_lt hc,
        firstParam,assign,advance,put,bind,Except.bind,pure,Except.pure]
    simpa [finishInteger,firstParam] using Scalar.integer_local_step
      (ctx := ctx) (oracle := oracle) (code := code) (s := {}) rfl rfl rfl (by intro bid h; cases h) hlocal
  have h1 : Scalar.step ctx oracle code (firstParam counter) = .ok (secondParam counter x,[]) := by
    have hlocal : localStep ctx.params ctx.id.tid.x (firstParam counter).core.thread (.param 64 "%rd1" "X") =
        .ok (secondParam counter x).core.thread := by
      simp [localStep,hp.2.1,show wrap 64 x = x from Nat.mod_eq_of_lt hx,
        firstParam,secondParam,assign,advance,put,bind,Except.bind,pure,Except.pure]
    simpa [finishInteger,firstParam,secondParam] using Scalar.integer_local_step
      (ctx := ctx) (oracle := oracle) (code := code) (s := firstParam counter) rfl rfl rfl (by intro bid h; cases h) hlocal
  have h2 : Scalar.step ctx oracle code (secondParam counter x) = .ok (ready counter x y,[]) := by
    have hlocal : localStep ctx.params ctx.id.tid.x (secondParam counter x).core.thread (.param 64 "%rd2" "Y") =
        .ok (ready counter x y).core.thread := by
      simp [localStep,hp.2.2,show wrap 64 y = y from Nat.mod_eq_of_lt hy,
        secondParam,ready,assign,advance,put,bind,Except.bind,pure,Except.pure]
    simpa [finishInteger,secondParam,ready] using Scalar.integer_local_step
      (ctx := ctx) (oracle := oracle) (code := code) (s := secondParam counter x) rfl rfl rfl (by intro bid h; cases h) hlocal
  simp [Scalar.run,h0,h1,h2,Except.bind]

theorem translated_atomic_prefix (ctx : Scalar.Context) (oracle : Scalar.Oracle) (counter x y value : Nat)
    (hp : Params counter x y ctx.params) (hc : counter < 2^64) (hx : x < 2^64) (hy : y < 2^64)
    (ho : oracle 0 = .integer value) :
    Scalar.run ctx oracle code 4 {} = .ok (afterAtomic counter x y value,
      [.rmw .gpu ⟨.global,counter⟩ (atomicAddBytes value 1)]) := by
  have hstep : Scalar.step ctx oracle code (ready counter x y) = .ok (afterAtomic counter x y value,
      [.rmw .gpu ⟨.global,counter⟩ (atomicAddBytes value 1)]) := by
    apply Scalar.atom_add_u32_step rfl rfl
    · simp [evalAddr,Ptx.eval,ready,lookup,show wrap 64 counter = counter from Nat.mod_eq_of_lt hc]
    · rfl
    · exact ho
  rw [show 4 = 3+1 by decide,Scalar.run_add,parameters_run ctx oracle counter x y hp hc hx hy]
  simp [Scalar.run,hstep,Except.bind]

end
end Ptx.AtomicDispatchTrace
