import Ptx.Kernels.AmpereTiledInit

/-! Checked address dataflow for actual slots 16..51. These formulas deliberately
retain all integer wrapping; physical/read bounds are separate obligations. -/
namespace Ptx.AmpereTiledAddresses
open Ptx.ISA Ptx.Ampere
noncomputable section
set_option maxRecDepth 4096
abbrev code := Generated.ampere_tiled_matmul.program
abbrev Config := AmpereTiledSpec.Config
def x (ctx : Scalar.Context) := wrap 32 ctx.id.tid.x
def y (ctx : Scalar.Context) := wrap 32 ctx.id.tid.y
def row (ctx : Scalar.Context) := wrap 32 (AmpereTiledInit.tileRow ctx+y ctx)
def col (ctx : Scalar.Context) := wrap 32 (AmpereTiledInit.tileCol ctx+y ctx)
def cCol (ctx : Scalar.Context) := wrap 32 (AmpereTiledInit.tileCol ctx+wrap 32 (x ctx*2))
def smallA (ctx : Scalar.Context) := wrap 64 (x ctx*8)
def aOffset (cfg : Config) (ctx : Scalar.Context) := wrap 64 (wrap 64 (row ctx*wrap 32 cfg.k)*2)
def bOffset (cfg : Config) (ctx : Scalar.Context) := wrap 64 (wrap 64 (col ctx*wrap 32 cfg.k)*2)
def cOffset (cfg : Config) (ctx : Scalar.Context) := wrap 64 (wrap 64 (row ctx*wrap 32 cfg.n)*4)
def a (cfg : Config) (ctx : Scalar.Context) := wrap 64 (wrap 64 cfg.a+wrap 64 (aOffset cfg ctx+smallA ctx))
def ah (cfg : Config) (ctx : Scalar.Context) := wrap 64 (a cfg ctx+wrap 64 (wrap 32 cfg.k*16))
def b (cfg : Config) (ctx : Scalar.Context) := wrap 64 (wrap 64 cfg.b+wrap 64 (bOffset cfg ctx+smallA ctx))
def c (cfg : Config) (ctx : Scalar.Context) := wrap 64 (wrap 64 cfg.c+wrap 64 (cOffset cfg ctx+wrap 64 (cCol ctx*4)))
def ch (cfg : Config) (ctx : Scalar.Context) := wrap 64 (c cfg ctx+wrap 64 (wrap 32 cfg.n*32))
def copyOffset (ctx : Scalar.Context) := wrap 32 (wrap 32 (y ctx*32)+wrap 32 (x ctx*8))
def readOffset (ctx : Scalar.Context) := wrap 32 (wrap 32 (y ctx*32)+wrap 32 (x ctx*4))
def sa (ctx : Scalar.Context) := wrap 64 (copyOffset ctx)
def sah (ctx : Scalar.Context) := wrap 64 (sa ctx+256)
def sb (ctx : Scalar.Context) := wrap 64 (sa ctx+512)
def la (ctx : Scalar.Context) := wrap 64 (readOffset ctx)
def lb (ctx : Scalar.Context) := wrap 64 (la ctx+512)

def assignments (s : State) (values : Bindings) : State :=
  values.foldl (fun state kv => Ampere.intAssign state kv.1 kv.2) s

def ab (cfg : Config) (ctx : Scalar.Context) : State := assignments (AmpereTiledInit.guarded cfg ctx) [
  ("%row",row ctx),("%col",col ctx),("%off",wrap 64 (row ctx*wrap 32 cfg.k)),
  ("%off",aOffset cfg ctx),("%small",smallA ctx),("%off",wrap 64 (aOffset cfg ctx+smallA ctx)),
  ("%a",a cfg ctx),("%off",wrap 64 (wrap 32 cfg.k*16)),("%ah",ah cfg ctx),
  ("%off",wrap 64 (col ctx*wrap 32 cfg.k)),("%off",bOffset cfg ctx),
  ("%off",wrap 64 (bOffset cfg ctx+smallA ctx)),("%b",b cfg ctx)]
def output (cfg : Config) (ctx : Scalar.Context) : State := assignments (ab cfg ctx) [
  ("%off",wrap 64 (row ctx*wrap 32 cfg.n)),("%off",cOffset cfg ctx),
  ("%tmp",wrap 32 (x ctx*2)),("%tmp",cCol ctx),("%small",wrap 64 (cCol ctx*4)),
  ("%off",wrap 64 (cOffset cfg ctx+wrap 64 (cCol ctx*4))),
  ("%c",c cfg ctx),("%off",wrap 64 (wrap 32 cfg.n*32)),("%ch",ch cfg ctx)]
def shared (cfg : Config) (ctx : Scalar.Context) : State := assignments (output cfg ctx) [
  ("%copyoff",wrap 32 (y ctx*32)),("%tmp",wrap 32 (x ctx*8)),("%copyoff",copyOffset ctx),
  ("%off",0),("%sa",sa ctx),("%sa",sa ctx),("%sah",sah ctx),("%sb",sb ctx),
  ("%readoff",wrap 32 (y ctx*32)),("%tmp",wrap 32 (x ctx*4)),("%readoff",readOffset ctx),
  ("%la",la ctx),("%la",la ctx),("%lb",lb ctx)]

theorem ab_run (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) :
    Ampere.run ctx oracle code 13 (AmpereTiledInit.guarded cfg ctx) = .ok (ab cfg ctx,[]) := by
  norm_num [Ampere.run,Ampere.step,code,Generated.ampere_tiled_matmul.program,ab,assignments,List.foldl,
    AmpereTiledInit.guarded,AmpereTiledInit.indexed,row,col,x,y,a,ah,b,aOffset,bOffset,smallA,
    scalarSkeleton,Scalar.step,Scalar.require,Scalar.integer_delegate_fetch,
    Scalar.liftInteger,Scalar.finishInteger,Scalar.liftKind,Ptx.Event.step,localStep,Ptx.eval,
    liftScalar,finishScalar,scalarWritten,Ampere.intPC,Ampere.intAssign,Scalar.intPC,Scalar.intAssign,
    assign,Ptx.advance,put,lookup,Scalar.wrap_idempotent,
    show wrap 32 8 = 8 by decide,show wrap 32 16 = 16 by decide,show wrap 64 2 = 2 by decide,
    bind,Except.bind,pure,Except.pure]

theorem output_run (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) :
    Ampere.run ctx oracle code 9 (ab cfg ctx) = .ok (output cfg ctx,[]) := by
  norm_num [Ampere.run,Ampere.step,code,Generated.ampere_tiled_matmul.program,output,ab,assignments,List.foldl,
    AmpereTiledInit.guarded,AmpereTiledInit.indexed,row,col,cCol,x,y,a,ah,b,c,ch,aOffset,bOffset,cOffset,smallA,
    scalarSkeleton,Scalar.step,Scalar.require,Scalar.integer_delegate_fetch,
    Scalar.liftInteger,Scalar.finishInteger,Scalar.liftKind,Ptx.Event.step,localStep,Ptx.eval,
    liftScalar,finishScalar,scalarWritten,Ampere.intPC,Ampere.intAssign,Scalar.intPC,Scalar.intAssign,
    assign,Ptx.advance,put,lookup,Scalar.wrap_idempotent,
    show wrap 32 2 = 2 by decide,show wrap 32 32 = 32 by decide,show wrap 32 4 = 4 by decide,
    show wrap 64 4 = 4 by decide,
    bind,Except.bind,pure,Except.pure]

theorem shared_run (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) :
    Ampere.run ctx oracle code 14 (output cfg ctx) = .ok (shared cfg ctx,[]) := by
  norm_num [Ampere.run,Ampere.step,code,Generated.ampere_tiled_matmul.program,shared,output,ab,assignments,List.foldl,
    AmpereTiledInit.guarded,AmpereTiledInit.indexed,row,col,cCol,x,y,a,ah,b,c,ch,aOffset,bOffset,cOffset,smallA,
    copyOffset,readOffset,sa,sah,sb,la,lb,
    scalarSkeleton,Scalar.step,Scalar.require,Scalar.integer_delegate_fetch,
    Scalar.liftInteger,Scalar.finishInteger,Scalar.liftKind,Ptx.Event.step,localStep,Ptx.eval,
    liftScalar,finishScalar,scalarWritten,Ampere.intPC,Ampere.intAssign,Scalar.intPC,Scalar.intAssign,
    assign,Ptx.advance,put,lookup,Scalar.wrap_idempotent,
    show wrap 32 32 = 32 by decide,show wrap 32 8 = 8 by decide,show wrap 32 4 = 4 by decide,
    show wrap 32 1 = 1 by decide,show wrap 64 0 = 0 by decide,
    show wrap 64 256 = 256 by decide,show wrap 64 512 = 512 by decide,
    bind,Except.bind,pure,Except.pure]

end
end Ptx.AmpereTiledAddresses
