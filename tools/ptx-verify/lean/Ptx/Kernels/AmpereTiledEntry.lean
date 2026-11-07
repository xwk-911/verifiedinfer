import Ptx.Kernels.AmpereTiledAddresses
import Ptx.Ampere.FloatSteps

/-! The actual 57-slot active initialization establishes the K-loop invariant.
This adds no caller invariant or read-value assumptions to the kernel Pre. -/
namespace Ptx.AmpereTiledEntry
open Ptx.ISA Ptx.Ampere
noncomputable section
set_option maxRecDepth 4096
abbrev code := Generated.ampere_tiled_matmul.program
abbrev Config := AmpereTiledSpec.Config

def zeroed (s : State) : State := Ampere.intAssign
  (floatAssign (floatAssign (floatAssign (floatAssign s "%acc0" .f32 0) "%acc1" .f32 0)
    "%acc2" .f32 0) "%acc3" .f32 0) "%it" 0
def ready (cfg : Config) (ctx : Scalar.Context) := zeroed (AmpereTiledAddresses.shared cfg ctx)
def loopConfig (cfg : Config) (ctx : Scalar.Context) : AmpereTiledLoop.Config := {
  pointers := ⟨AmpereTiledAddresses.a cfg ctx,AmpereTiledAddresses.ah cfg ctx,AmpereTiledAddresses.b cfg ctx,
    AmpereTiledAddresses.sa ctx,AmpereTiledAddresses.sah ctx,AmpereTiledAddresses.sb ctx⟩
  pa := AmpereTiledAddresses.la ctx
  pb := AmpereTiledAddresses.lb ctx
  low := AmpereTiledAddresses.c cfg ctx
  high := AmpereTiledAddresses.ch cfg ctx
  tiles := cfg.k/16
  firstQuery := 0
}

theorem zeroed_nat (s : State) (i : Fin 4) :
    lookup (MmaBlock.accumulators.get i) (zeroed s).scalar.core.thread.regs = none := by
  fin_cases i <;> simp [zeroed,MmaBlock.accumulators,Registers4.get]

theorem zeroed_accumulator (s : State) (i : Fin 4) :
    declarationLookup (MmaBlock.accumulators.get i) (zeroed s).scalar.floats = some (.f32,0) := by
  fin_cases i <;> simp [zeroed,Ampere.intAssign,Scalar.intAssign_float,MmaBlock.accumulators,Registers4.get]

theorem zero_run (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) :
    Ampere.run ctx oracle code 5 (AmpereTiledAddresses.shared cfg ctx) = .ok (ready cfg ctx,[]) := by
  let s := AmpereTiledAddresses.shared cfg ctx
  let s1 := floatAssign s "%acc0" .f32 0
  let s2 := floatAssign s1 "%acc1" .f32 0
  let s3 := floatAssign s2 "%acc2" .f32 0
  let s4 := floatAssign s3 "%acc3" .f32 0
  have h0 : Ampere.step ctx oracle code s = .ok (s1,[]) :=
    move_float_step rfl rfl (by simp [Scalar.eval])
  have h1 : Ampere.step ctx oracle code s1 = .ok (s2,[]) :=
    move_float_step rfl rfl (by simp [Scalar.eval])
  have h2 : Ampere.step ctx oracle code s2 = .ok (s3,[]) :=
    move_float_step rfl rfl (by simp [Scalar.eval])
  have h3 : Ampere.step ctx oracle code s3 = .ok (s4,[]) :=
    move_float_step rfl rfl (by simp [Scalar.eval])
  have h4 : Ampere.step ctx oracle code s4 = .ok (Ampere.intAssign s4 "%it" 0,[]) := by
    have hs := Ampere.integer_local_step (ctx := ctx) (oracle := oracle) (code := code) (s := s4)
      (instruction := .mov 32 "%it" (.imm 0)) rfl rfl rfl (by intro bid he; cases he)
      (show localStep ctx.params ctx.id.tid.x s4.scalar.core.thread (.mov 32 "%it" (.imm 0)) =
        .ok (assign s4.scalar.core.thread "%it" 0) by rfl)
    simpa [Ampere.intAssign,Scalar.intAssign,finishScalar,scalarWritten] using hs
  change Ampere.run ctx oracle code 5 s = _
  simp only [Ampere.run,h0,h1,h2,h3,h4,Except.bind,List.nil_append]
  rfl

theorem source_prefix (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle)
    (hp : AmpereTiledInit.Params cfg ctx.params)
    (hr : AmpereTiledInit.tileRow ctx < wrap 32 cfg.m) (hc : AmpereTiledInit.tileCol ctx < wrap 32 cfg.n) :
    Ampere.run ctx oracle code 57 {} = .ok (ready cfg ctx,[]) := by
  rw [show 57 = 12+45 by decide,Ampere.run_add,AmpereTiledInit.indexed_run cfg ctx oracle hp]
  simp only [Except.bind,List.nil_append]
  rw [show 45 = 4+41 by decide,Ampere.run_add,AmpereTiledInit.guards_run cfg ctx oracle hr hc]
  simp only [Except.bind,List.nil_append]
  rw [show 41 = 13+28 by decide,Ampere.run_add,AmpereTiledAddresses.ab_run]
  simp only [Except.bind,List.nil_append]
  rw [show 28 = 9+19 by decide,Ampere.run_add,AmpereTiledAddresses.output_run]
  simp only [Except.bind,List.nil_append]
  rw [show 19 = 14+5 by decide,Ampere.run_add,AmpereTiledAddresses.shared_run]
  simp only [Except.bind,List.nil_append]
  rw [zero_run]

theorem invariant (cfg : Config) (ctx : Scalar.Context)
    (hk : cfg.k < 2^32) (ht : cfg.k%16 = 0) :
    AmpereTiledLoop.Invariant (loopConfig cfg ctx) 0 (ready cfg ctx) := by
  have hkw : wrap 32 cfg.k = 16*(cfg.k/16) := by
    rw [show wrap 32 cfg.k = cfg.k from Nat.mod_eq_of_lt hk]
    omega
  constructor
  · rfl
  · rfl
  · simp [ready,zeroed]
  · intro i
    fin_cases i <;>
      simp [ready,zeroed,loopConfig,AmpereTiledLoop.pointersAt,CopyStage.sourceName,CopyStage.source,
        AmpereTiledAddresses.shared,AmpereTiledAddresses.output,AmpereTiledAddresses.ab,AmpereTiledAddresses.assignments,
        AmpereTiledInit.guarded,AmpereTiledInit.indexed,List.foldl,
        AmpereTiledAddresses.a,AmpereTiledAddresses.ah,AmpereTiledAddresses.b]
  · intro i
    fin_cases i <;>
      simp [ready,zeroed,loopConfig,AmpereTiledLoop.fixedName,AmpereTiledLoop.fixedValue,
        AmpereTiledAddresses.shared,AmpereTiledAddresses.output,AmpereTiledAddresses.ab,AmpereTiledAddresses.assignments,
        AmpereTiledInit.guarded,AmpereTiledInit.indexed,List.foldl,lookup,hkw]
  · rfl
  · exact ⟨fun _ => 0,zeroed_accumulator _⟩
  · exact zeroed_nat _

end
end Ptx.AmpereTiledEntry
