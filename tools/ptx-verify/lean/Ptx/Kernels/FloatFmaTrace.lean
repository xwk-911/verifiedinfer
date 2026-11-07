import Ptx.Generated.FloatFma
import Ptx.Scalar.Rules
import Lean.Elab.Tactic.Omega

/-! Parametric local trace of the MECHANICALLY translated float_fma.ptx.
This is not an allowed-execution/global-output contract: load answers are still
independent oracles, and allocation/UB/memory consistency remain separate duties.
-/
namespace Ptx.FloatFmaTrace
open Ptx.ISA Ptx.Scalar
noncomputable section
abbrev code := Generated.float_fma.program

def Params (src dst : Nat) (params : Bindings) : Prop := lookup "src" params = some src ∧ lookup "dst" params = some dst
def firstParam (src : Nat) : Scalar.State := {core := {thread := {pc := 1,regs := [("%rd0",src)]}}}
def ready (src dst : Nat) : Scalar.State := {core := {thread := {pc := 2,regs := [("%rd1",dst),("%rd0",src)]}}}
def oracle (a b c : ℝ) : Scalar.Oracle := fun query => .real .f32 (if query = 0 then a else if query = 1 then b else c)
def beforeRet (src dst : Nat) (a b c : ℝ) : Scalar.State := {
  core := {thread := {pc := 7,regs := [("%rd1",dst),("%rd0",src)]},queries := 3}
  floats := [("%f3",(.f32,a*b+c)),("%f2",(.f32,c)),("%f1",(.f32,b)),("%f0",(.f32,a))]
}
def finalState (src dst : Nat) (a b c : ℝ) : Scalar.State := {
  (beforeRet src dst a b c) with core := {(beforeRet src dst a b c).core with
    thread := {(beforeRet src dst a b c).core.thread with status := .done}}
}
def events (src dst : Nat) (a b c : ℝ) : List Scalar.Kind := [
  .read ⟨.global,src⟩ (Symbolic.encode .f32 a),.read ⟨.global,src+4⟩ (Symbolic.encode .f32 b),
  .read ⟨.global,src+8⟩ (Symbolic.encode .f32 c),.write ⟨.global,dst⟩ (Symbolic.encode .f32 (a*b+c))]

theorem parameters_run (ctx : Scalar.Context) (answers : Scalar.Oracle) (src dst : Nat)
    (hp : Params src dst ctx.params) (hs : src < 2^64) (hd : dst < 2^64) :
    Scalar.run ctx answers code 2 {} = .ok (ready src dst,[]) := by
  have hsrc : wrap 64 src = src := Nat.mod_eq_of_lt hs
  have hdst : wrap 64 dst = dst := Nat.mod_eq_of_lt hd
  have hlocal0 : localStep ctx.params ctx.id.tid.x {} (.param 64 "%rd0" "src") = .ok (firstParam src).core.thread := by
    simp [localStep,hp.1,hsrc,firstParam,assign,advance,put,bind,Except.bind,pure,Except.pure]
  have hlocal1 : localStep ctx.params ctx.id.tid.x (firstParam src).core.thread (.param 64 "%rd1" "dst") =
      .ok (ready src dst).core.thread := by
    simp [localStep,hp.2,hdst,firstParam,ready,assign,advance,put,bind,Except.bind,pure,Except.pure]
  have h0 := Scalar.integer_local_step (ctx := ctx) (oracle := answers) (code := code) (s := {})
    rfl rfl rfl (by intro bid h; cases h) hlocal0
  have h1 := Scalar.integer_local_step (ctx := ctx) (oracle := answers) (code := code) (s := firstParam src)
    rfl rfl rfl (by intro bid h; cases h) hlocal1
  have hs0 : Scalar.step ctx answers code {} = .ok (firstParam src,[]) := by
    simpa [finishInteger,firstParam] using h0
  have hs1 : Scalar.step ctx answers code (firstParam src) = .ok (ready src dst,[]) := by
    simpa [finishInteger,firstParam,ready] using h1
  simp [Scalar.run,hs0,hs1,Except.bind]

theorem float_body_run (ctx : Scalar.Context) (src dst : Nat) (a b c : ℝ)
    (hs : src+8 < 2^64) (hd : dst < 2^64) :
    Scalar.run ctx (oracle a b c) code 5 (ready src dst) = .ok (beforeRet src dst a b c,events src dst a b c) := by
  have hs0 : wrap 64 src = src := Nat.mod_eq_of_lt (by omega)
  have hs4 : wrap 64 (src+4) = src+4 := Nat.mod_eq_of_lt (by omega)
  have hs8 : wrap 64 (src+8) = src+8 := Nat.mod_eq_of_lt hs
  have hd0 : wrap 64 dst = dst := Nat.mod_eq_of_lt hd
  simp only [wrap] at hs0 hs4 hs8 hd0
  simp [Scalar.run,Scalar.step,code,Generated.float_fma.program,ready,oracle,beforeRet,events,
    Scalar.eval,writeFloat,Scalar.require,liftInteger,evalAddr,Ptx.eval,advance,lookup,declarationLookup,
    Location.resolve,hs0,hs4,hs8,hd0,wrap,bind,Except.bind,pure,Except.pure]

theorem translated_trace (ctx : Scalar.Context) (src dst : Nat) (a b c : ℝ)
    (hp : Params src dst ctx.params) (hs : src+8 < 2^64) (hd : dst < 2^64) :
    Scalar.run ctx (oracle a b c) code 8 {} = .ok (finalState src dst a b c,events src dst a b c) := by
  have hret : Scalar.step ctx (oracle a b c) code (beforeRet src dst a b c) = .ok (finalState src dst a b c,[]) := by
    have h := Scalar.integer_local_step (ctx := ctx) (oracle := oracle a b c) (code := code) (s := beforeRet src dst a b c)
      rfl rfl rfl (by intro bid h; cases h) rfl
    simpa [finishInteger,beforeRet,finalState,lookup] using h
  rw [show 8 = 2+6 by decide,Scalar.run_add,parameters_run ctx (oracle a b c) src dst hp (by omega) hd]
  simp only [Except.bind,List.nil_append]
  rw [show 6 = 5+1 by decide,Scalar.run_add,float_body_run ctx src dst a b c hs hd]
  simp [Scalar.run,hret,Except.bind]

theorem translated_register_banks (ctx : Scalar.Context) (src dst : Nat) (a b c : ℝ)
    (hp : Params src dst ctx.params) (hs : src+8 < 2^64) (hd : dst < 2^64) :
    BanksDisjoint (finalState src dst a b c) :=
  run_banks_disjoint (translated_trace ctx src dst a b c hp hs hd) empty_banks_disjoint

end
end Ptx.FloatFmaTrace
