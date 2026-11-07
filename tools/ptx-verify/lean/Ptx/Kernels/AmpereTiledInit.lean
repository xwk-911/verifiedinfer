import Ptx.Kernels.AmpereTiledLoop
import Ptx.Kernels.AmpereTiledSpec

/-! Actual PC-zero initialization. Wrapping is retained even for unused inputs;
no extra padding/alignment conditions are imposed on zero-K configurations. -/
namespace Ptx.AmpereTiledInit
open Ptx.ISA Ptx.Ampere
noncomputable section
abbrev code := Generated.ampere_tiled_matmul.program

structure Params (cfg : AmpereTiledSpec.Config) (bindings : Bindings) : Prop where
  a : lookup "A" bindings = some cfg.a
  b : lookup "B" bindings = some cfg.b
  c : lookup "C" bindings = some cfg.c
  m : lookup "M" bindings = some cfg.m
  n : lookup "N" bindings = some cfg.n
  k : lookup "K" bindings = some cfg.k

theorem canonical_params (cfg : AmpereTiledSpec.Config) : Params cfg (AmpereTiledSpec.params cfg) := by
  constructor <;> rfl

def parameters (cfg : AmpereTiledSpec.Config) : State := {
  scalar := {core := {thread := {pc := 6,regs := [
    ("%k",wrap 32 cfg.k),("%n",wrap 32 cfg.n),("%m",wrap 32 cfg.m),
    ("%c",wrap 64 cfg.c),("%b",wrap 64 cfg.b),("%a",wrap 64 cfg.a)]}}}
}
def tileRow (ctx : Scalar.Context) : Nat := wrap 32 (wrap 32 ctx.id.cta.y*16)
def tileCol (ctx : Scalar.Context) : Nat := wrap 32 (wrap 32 ctx.id.cta.x*8)
@[simp] theorem tileRow_wrap (ctx : Scalar.Context) : wrap 32 (tileRow ctx) = tileRow ctx := Scalar.wrap_idempotent _ _
@[simp] theorem tileCol_wrap (ctx : Scalar.Context) : wrap 32 (tileCol ctx) = tileCol ctx := Scalar.wrap_idempotent _ _
def indexed (cfg : AmpereTiledSpec.Config) (ctx : Scalar.Context) : State := {
  scalar := {core := {thread := {pc := 12,regs := [
    ("%tn",tileCol ctx),("%tm",tileRow ctx),("%y",wrap 32 ctx.id.tid.y),("%x",wrap 32 ctx.id.tid.x),
    ("%k",wrap 32 cfg.k),("%n",wrap 32 cfg.n),("%m",wrap 32 cfg.m),
    ("%c",wrap 64 cfg.c),("%b",wrap 64 cfg.b),("%a",wrap 64 cfg.a)]}}}
}

theorem parameters_run (cfg : AmpereTiledSpec.Config) (ctx : Scalar.Context) (oracle : Oracle)
    (hp : Params cfg ctx.params) : Ampere.run ctx oracle code 6 {} = .ok (parameters cfg,[]) := by
  norm_num [Ampere.run,Ampere.step,code,Generated.ampere_tiled_matmul.program,parameters,
    scalarSkeleton,Scalar.step,Scalar.require,Scalar.integer_delegate_fetch,
    Scalar.liftInteger,Scalar.finishInteger,Scalar.liftKind,Ptx.Event.step,localStep,
    liftScalar,finishScalar,scalarWritten,assign,Ptx.advance,put,lookup,hp.a,hp.b,hp.c,hp.m,hp.n,hp.k,
    bind,Except.bind,pure,Except.pure]

theorem indices_run (cfg : AmpereTiledSpec.Config) (ctx : Scalar.Context) (oracle : Oracle) :
    Ampere.run ctx oracle code 6 (parameters cfg) = .ok (indexed cfg ctx,[]) := by
  norm_num [Ampere.run,Ampere.step,code,Generated.ampere_tiled_matmul.program,parameters,indexed,tileRow,tileCol,
    scalarSkeleton,Scalar.step,Scalar.require,Scalar.integer_delegate_fetch,
    Scalar.liftInteger,Scalar.finishInteger,Scalar.liftKind,Ptx.Event.step,localStep,Ptx.eval,
    Scalar.SpecialRegister.value,Scalar.Axis.component,
    liftScalar,finishScalar,scalarWritten,assign,Ptx.advance,put,lookup,Scalar.wrap_idempotent,
    show wrap 32 16 = 16 by decide,show wrap 32 8 = 8 by decide,
    bind,Except.bind,pure,Except.pure]

theorem indexed_run (cfg : AmpereTiledSpec.Config) (ctx : Scalar.Context) (oracle : Oracle)
    (hp : Params cfg ctx.params) : Ampere.run ctx oracle code 12 {} = .ok (indexed cfg ctx,[]) := by
  rw [show 12 = 6+6 by decide,Ampere.run_add,parameters_run cfg ctx oracle hp]
  simp only [Except.bind,List.nil_append]
  rw [indices_run]

def guarded (cfg : AmpereTiledSpec.Config) (ctx : Scalar.Context) : State :=
  Ampere.intPC (Ampere.intAssign (indexed cfg ctx) "%p" 0) 16
def maskedFinal (cfg : AmpereTiledSpec.Config) (ctx : Scalar.Context) : State := {
  (Ampere.intAssign (indexed cfg ctx) "%p" 1) with
  scalar := {core := {thread := {
    pc := 82
    status := .done
    regs := ("%p",1)::(indexed cfg ctx).scalar.core.thread.regs}}}
}

theorem guards_run (cfg : AmpereTiledSpec.Config) (ctx : Scalar.Context) (oracle : Oracle)
    (hr : tileRow ctx < wrap 32 cfg.m) (hc : tileCol ctx < wrap 32 cfg.n) :
    Ampere.run ctx oracle code 4 (indexed cfg ctx) = .ok (guarded cfg ctx,[]) := by
  norm_num [Ampere.run,Ampere.step,code,Generated.ampere_tiled_matmul.program,indexed,guarded,
    scalarSkeleton,Scalar.step,Scalar.require,Scalar.integer_delegate_fetch,
    Scalar.liftInteger,Scalar.finishInteger,Scalar.liftKind,Ptx.Event.step,localStep,Ptx.eval,
    liftScalar,finishScalar,scalarWritten,assign,Ptx.advance,put,lookup,Ampere.intPC,Ampere.intAssign,
    Scalar.intPC,Scalar.intAssign,Scalar.wrap_idempotent,
    Nat.not_le_of_lt hr,Nat.not_le_of_lt hc,
    bind,Except.bind,pure,Except.pure]

theorem row_mask_run (cfg : AmpereTiledSpec.Config) (ctx : Scalar.Context) (oracle : Oracle)
    (hr : wrap 32 cfg.m ≤ tileRow ctx) :
    Ampere.run ctx oracle code 3 (indexed cfg ctx) = .ok (maskedFinal cfg ctx,[]) := by
  norm_num [Ampere.run,Ampere.step,code,Generated.ampere_tiled_matmul.program,indexed,maskedFinal,
    scalarSkeleton,Scalar.step,Scalar.require,Scalar.integer_delegate_fetch,
    Scalar.liftInteger,Scalar.finishInteger,Scalar.liftKind,Ptx.Event.step,localStep,Ptx.eval,
    liftScalar,finishScalar,scalarWritten,assign,Ptx.advance,put,lookup,Ampere.intAssign,
    Scalar.intAssign,Scalar.wrap_idempotent,hr,
    bind,Except.bind,pure,Except.pure]

theorem col_mask_run (cfg : AmpereTiledSpec.Config) (ctx : Scalar.Context) (oracle : Oracle)
    (hr : tileRow ctx < wrap 32 cfg.m) (hc : wrap 32 cfg.n ≤ tileCol ctx) :
    Ampere.run ctx oracle code 5 (indexed cfg ctx) = .ok (maskedFinal cfg ctx,[]) := by
  norm_num [Ampere.run,Ampere.step,code,Generated.ampere_tiled_matmul.program,indexed,maskedFinal,
    scalarSkeleton,Scalar.step,Scalar.require,Scalar.integer_delegate_fetch,
    Scalar.liftInteger,Scalar.finishInteger,Scalar.liftKind,Ptx.Event.step,localStep,Ptx.eval,
    liftScalar,finishScalar,scalarWritten,assign,Ptx.advance,put,lookup,Ampere.intAssign,
    Scalar.intAssign,Scalar.wrap_idempotent,Nat.not_le_of_lt hr,hc,
    bind,Except.bind,pure,Except.pure]

end
end Ptx.AmpereTiledInit
