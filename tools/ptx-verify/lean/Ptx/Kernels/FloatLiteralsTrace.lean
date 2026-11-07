import Ptx.Generated.FloatLiterals
import Ptx.Scalar.Rules
import Mathlib.Tactic.NormNum

/-! Actual generated mov/add/mul/shared/global float fixture. The shared read
answer deliberately remains arbitrary: local provenance must NOT manufacture
the memory-consistency obligation that it equals the earlier store of 9.
-/
namespace Ptx.FloatLiteralsTrace
open Ptx.ISA Ptx.Scalar
noncomputable section
abbrev code := Generated.float_literals.program

def ready (dst : Nat) : Scalar.State := {core := {thread := {pc := 1,regs := [("%ptr",dst)]}}}
def beforeRet (dst : Nat) (answer : ℝ) : Scalar.State := {
  core := {thread := {pc := 7,regs := [("%ptr",dst)]},queries := 1}
  floats := [("%f0",(.f32,answer)),("%f2",(.f32,9)),("%f1",(.f32,3))]
}
def finalState (dst : Nat) (answer : ℝ) : Scalar.State := {
  (beforeRet dst answer) with core := {(beforeRet dst answer).core with
    thread := {(beforeRet dst answer).core.thread with status := .done}}
}
def events (thread : ThreadId) (dst : Nat) (answer : ℝ) : List Scalar.Kind := [
  .write ⟨.shared thread.cta,0⟩ (Symbolic.encode .f32 9),
  .read ⟨.shared thread.cta,0⟩ (Symbolic.encode .f32 answer),
  .write ⟨.global,dst⟩ (Symbolic.encode .f32 answer)]

theorem parameters_run (ctx : Scalar.Context) (answers : Scalar.Oracle) (dst : Nat)
    (hp : lookup "dst" ctx.params = some dst) (hd : dst < 2^64) :
    Scalar.run ctx answers code 1 {} = .ok (ready dst,[]) := by
  have hdst : wrap 64 dst = dst := Nat.mod_eq_of_lt hd
  have hlocal : localStep ctx.params ctx.id.tid.x {} (.param 64 "%ptr" "dst") = .ok (ready dst).core.thread := by
    simp [localStep,hp,hdst,ready,assign,advance,put,bind,Except.bind,pure,Except.pure]
  have h := Scalar.integer_local_step (ctx := ctx) (oracle := answers) (code := code) (s := {})
    rfl rfl rfl (by intro bid h; cases h) hlocal
  have hs : Scalar.step ctx answers code {} = .ok (ready dst,[]) := by simpa [finishInteger,ready] using h
  simp [Scalar.run,hs,Except.bind]

theorem float_body_run (ctx : Scalar.Context) (dst : Nat) (answer : ℝ) (hd : dst < 2^64) :
    Scalar.run ctx (fun _ => .real .f32 answer) code 6 (ready dst) =
      .ok (beforeRet dst answer,events ctx.id dst answer) := by
  have hdst : wrap 64 dst = dst := Nat.mod_eq_of_lt hd
  simp only [wrap] at hdst
  norm_num [Scalar.run,Scalar.step,code,Generated.float_literals.program,ready,beforeRet,events,
    Scalar.eval,F32Literal.value,writeFloat,Scalar.require,liftInteger,evalAddr,Ptx.eval,
    advance,lookup,declarationLookup,Location.resolve,hdst,wrap,bind,Except.bind,pure,Except.pure]

theorem translated_trace (ctx : Scalar.Context) (dst : Nat) (answer : ℝ)
    (hp : lookup "dst" ctx.params = some dst) (hd : dst < 2^64) :
    Scalar.run ctx (fun _ => .real .f32 answer) code 8 {} = .ok (finalState dst answer,events ctx.id dst answer) := by
  have hret : Scalar.step ctx (fun _ => .real .f32 answer) code (beforeRet dst answer) = .ok (finalState dst answer,[]) := by
    have h := Scalar.integer_local_step (ctx := ctx) (oracle := fun _ => .real .f32 answer)
      (code := code) (s := beforeRet dst answer) rfl rfl rfl (by intro bid h; cases h) rfl
    simpa [finishInteger,beforeRet,finalState,lookup] using h
  rw [show 8 = 1+7 by decide,Scalar.run_add,parameters_run ctx (fun _ => .real .f32 answer) dst hp hd]
  simp only [Except.bind,List.nil_append]
  rw [show 7 = 6+1 by decide,Scalar.run_add,float_body_run ctx dst answer hd]
  simp [Scalar.run,hret,Except.bind]

end
end Ptx.FloatLiteralsTrace
