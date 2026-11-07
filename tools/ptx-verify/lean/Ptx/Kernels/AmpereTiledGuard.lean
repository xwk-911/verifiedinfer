import Ptx.Generated.AmpereTiledMatmul
import Ptx.Ampere.ScalarSteps
import Ptx.Ampere.Trace

/-! The real unsigned loop test. Counter bounds justify unwrapping the compared
values. No matrix/memory property is assumed by this control fragment. -/
namespace Ptx.AmpereTiledGuard
open Ptx.ISA Ptx.Ampere
noncomputable section
abbrev code := Generated.ampere_tiled_matmul.program

def activeState (s : State) : State := Ampere.intPC (Ampere.intAssign s "%p" 0) 59
def exitState (s : State) : State := Ampere.intPC (Ampere.intAssign s "%p" 1) 78

theorem active (ctx : Scalar.Context) (oracle : Oracle) (s : State) (index bound : Nat)
    (hr : s.scalar.core.thread.status = .running) (hp : s.scalar.core.thread.pc = 57)
    (hi : lookup "%it" s.scalar.core.thread.regs = some index)
    (hb : lookup "%k" s.scalar.core.thread.regs = some bound)
    (hlt : index < bound) (hbound : bound < 2^32) :
    Ampere.run ctx oracle code 2 s = .ok (activeState s,[]) := by
  let s1 := Ampere.intAssign s "%p" 0
  have hindex : wrap 32 index = index := Nat.mod_eq_of_lt (by omega)
  have hmax : wrap 32 bound = bound := Nat.mod_eq_of_lt hbound
  have h0 : Ampere.step ctx oracle code s = .ok (s1,[]) := by
    have hs := Ampere.integer_local_step (ctx := ctx) (oracle := oracle) (code := code) (s := s)
      (instruction := .setp .ge "%p" (.reg "%it") (.reg "%k")) hr
      (by simp [hp,code,Generated.ampere_tiled_matmul.program]) rfl (by intro bid he; cases he)
      (show localStep ctx.params ctx.id.tid.x s.scalar.core.thread (.setp .ge "%p" (.reg "%it") (.reg "%k")) =
        .ok (assign s.scalar.core.thread "%p" 0) by
        simp [localStep,Ptx.eval,hi,hb,hindex,hmax,Nat.not_le_of_lt hlt,bind,Except.bind,pure,Except.pure])
    simpa [s1,Ampere.intAssign,finishScalar,scalarWritten,Scalar.intAssign] using hs
  have h1 : Ampere.step ctx oracle code s1 = .ok (activeState s,[]) := by
    have hs := Ampere.integer_local_step (ctx := ctx) (oracle := oracle) (code := code) (s := s1)
      (instruction := .branch "%p" true 78) (by simp [s1,hr])
      (by simp [s1,hp,code,Generated.ampere_tiled_matmul.program]) rfl (by intro bid he; cases he)
      (show localStep ctx.params ctx.id.tid.x s1.scalar.core.thread (.branch "%p" true 78) =
        .ok {s1.scalar.core.thread with pc := 59} by
        simp [localStep,Ptx.eval,s1,Ampere.intAssign,Scalar.intAssign,Scalar.finishInteger,assign,Ptx.advance,hp,
          bind,Except.bind,pure,Except.pure])
    simpa [activeState,s1,Ampere.intPC,finishScalar,scalarWritten,Scalar.intPC] using hs
  simp only [Ampere.run,h0,h1,Except.bind,List.nil_append]

theorem exit (ctx : Scalar.Context) (oracle : Oracle) (s : State) (bound : Nat)
    (hr : s.scalar.core.thread.status = .running) (hp : s.scalar.core.thread.pc = 57)
    (hi : lookup "%it" s.scalar.core.thread.regs = some bound)
    (hb : lookup "%k" s.scalar.core.thread.regs = some bound) (hbound : bound < 2^32) :
    Ampere.run ctx oracle code 2 s = .ok (exitState s,[]) := by
  let s1 := Ampere.intAssign s "%p" 1
  have hmax : wrap 32 bound = bound := Nat.mod_eq_of_lt hbound
  have h0 : Ampere.step ctx oracle code s = .ok (s1,[]) := by
    have hs := Ampere.integer_local_step (ctx := ctx) (oracle := oracle) (code := code) (s := s)
      (instruction := .setp .ge "%p" (.reg "%it") (.reg "%k")) hr
      (by simp [hp,code,Generated.ampere_tiled_matmul.program]) rfl (by intro bid he; cases he)
      (show localStep ctx.params ctx.id.tid.x s.scalar.core.thread (.setp .ge "%p" (.reg "%it") (.reg "%k")) =
        .ok (assign s.scalar.core.thread "%p" 1) by
        simp [localStep,Ptx.eval,hi,hb,hmax,bind,Except.bind,pure,Except.pure])
    simpa [s1,Ampere.intAssign,finishScalar,scalarWritten,Scalar.intAssign] using hs
  have h1 : Ampere.step ctx oracle code s1 = .ok (exitState s,[]) := by
    have hs := Ampere.integer_local_step (ctx := ctx) (oracle := oracle) (code := code) (s := s1)
      (instruction := .branch "%p" true 78) (by simp [s1,hr])
      (by simp [s1,hp,code,Generated.ampere_tiled_matmul.program]) rfl (by intro bid he; cases he)
      (show localStep ctx.params ctx.id.tid.x s1.scalar.core.thread (.branch "%p" true 78) =
        .ok {s1.scalar.core.thread with pc := 78} by
        simp [localStep,Ptx.eval,s1,Ampere.intAssign,Scalar.intAssign,Scalar.finishInteger,assign,
          bind,Except.bind,pure,Except.pure])
    simpa [exitState,s1,Ampere.intPC,finishScalar,scalarWritten,Scalar.intPC] using hs
  simp only [Ampere.run,h0,h1,Except.bind,List.nil_append]

@[simp] theorem active_nat (s : State) (name : String) :
    lookup name (activeState s).scalar.core.thread.regs = if name = "%p" then some 0 else lookup name s.scalar.core.thread.regs := by
  simp [activeState]

theorem active_float (s : State) (name : String) (hp : name ≠ "%p")
    (hn : lookup name s.scalar.core.thread.regs = none) :
    declarationLookup name (activeState s).scalar.floats = declarationLookup name s.scalar.floats := by
  rw [activeState,Ampere.intPC_float]
  · exact Ampere.intAssign_float s "%p" name 0 hp hn
  · simp [hp,hn]

end
end Ptx.AmpereTiledGuard
