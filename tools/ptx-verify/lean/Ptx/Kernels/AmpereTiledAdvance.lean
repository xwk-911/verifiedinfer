import Ptx.Generated.AmpereTiledMatmul
import Ptx.Ampere.ScalarSteps
import Ptx.Ampere.Trace
import Mathlib.Tactic.NormNum

/-! Actual five-slot pointer/index advancement and loop backedge. Pointer
arithmetic stays wrapped, including the unused one-past-end final pointers.
Read address bounds belong to active iterations in the full kernel proof. -/
namespace Ptx.AmpereTiledAdvance
open Ptx.ISA Ptx.Ampere
noncomputable section
abbrev code := Generated.ampere_tiled_matmul.program

def nextState (s : State) (pa pah pb index : Nat) : State :=
  Ampere.intPC (Ampere.intAssign (Ampere.intAssign (Ampere.intAssign (Ampere.intAssign s
    "%a" (wrap 64 (pa+32))) "%ah" (wrap 64 (pah+32))) "%b" (wrap 64 (pb+32)))
    "%it" (wrap 32 (index+16))) 57

theorem execute (ctx : Scalar.Context) (oracle : Oracle) (s : State) (pa pah pb index : Nat)
    (hr : s.scalar.core.thread.status = .running) (hp : s.scalar.core.thread.pc = 73)
    (ha : lookup "%a" s.scalar.core.thread.regs = some pa)
    (hah : lookup "%ah" s.scalar.core.thread.regs = some pah)
    (hb : lookup "%b" s.scalar.core.thread.regs = some pb)
    (hi : lookup "%it" s.scalar.core.thread.regs = some index) :
    Ampere.run ctx oracle code 5 s = .ok (nextState s pa pah pb index,[]) := by
  let s1 := Ampere.intAssign s "%a" (wrap 64 (pa+32))
  let s2 := Ampere.intAssign s1 "%ah" (wrap 64 (pah+32))
  let s3 := Ampere.intAssign s2 "%b" (wrap 64 (pb+32))
  let s4 := Ampere.intAssign s3 "%it" (wrap 32 (index+16))
  let s5 := Ampere.intPC s4 57
  have h0 : Ampere.step ctx oracle code s = .ok (s1,[]) := by
    have hs := Ampere.integer_local_step (ctx := ctx) (oracle := oracle) (code := code) (s := s)
      (instruction := .bin .add 64 64 "%a" (.reg "%a") (.imm 32))
      (by simp [hr,hp]) (by simp [hr,hp,code,Generated.ampere_tiled_matmul.program])
      rfl (by intro bid he; cases he)
      (show localStep ctx.params ctx.id.tid.x s.scalar.core.thread
        (.bin .add 64 64 "%a" (.reg "%a") (.imm 32)) =
        .ok (assign s.scalar.core.thread "%a" (wrap 64 (pa+32))) by
        simp [localStep,Ptx.eval,ha,Scalar.wrap_add,Scalar.wrap_add_left,
          show wrap 64 32 = 32 by decide,bind,Except.bind,pure,Except.pure])
    simpa [s1,Ampere.intAssign,finishScalar,scalarWritten,Scalar.intAssign] using hs
  have h1 : Ampere.step ctx oracle code s1 = .ok (s2,[]) := by
    have hs := Ampere.integer_local_step (ctx := ctx) (oracle := oracle) (code := code) (s := s1)
      (instruction := .bin .add 64 64 "%ah" (.reg "%ah") (.imm 32))
      (by simp [s1,hr,hp]) (by simp [s1,hr,hp,code,Generated.ampere_tiled_matmul.program])
      rfl (by intro bid he; cases he)
      (show localStep ctx.params ctx.id.tid.x s1.scalar.core.thread
        (.bin .add 64 64 "%ah" (.reg "%ah") (.imm 32)) =
        .ok (assign s1.scalar.core.thread "%ah" (wrap 64 (pah+32))) by
        simp [localStep,Ptx.eval,s1,hah,Scalar.wrap_add,Scalar.wrap_add_left,
          show wrap 64 32 = 32 by decide,bind,Except.bind,pure,Except.pure])
    simpa [s2,Ampere.intAssign,finishScalar,scalarWritten,Scalar.intAssign] using hs
  have h2 : Ampere.step ctx oracle code s2 = .ok (s3,[]) := by
    have hs := Ampere.integer_local_step (ctx := ctx) (oracle := oracle) (code := code) (s := s2)
      (instruction := .bin .add 64 64 "%b" (.reg "%b") (.imm 32))
      (by simp [s2,s1,hr,hp]) (by simp [s2,s1,hr,hp,code,Generated.ampere_tiled_matmul.program])
      rfl (by intro bid he; cases he)
      (show localStep ctx.params ctx.id.tid.x s2.scalar.core.thread
        (.bin .add 64 64 "%b" (.reg "%b") (.imm 32)) =
        .ok (assign s2.scalar.core.thread "%b" (wrap 64 (pb+32))) by
        simp [localStep,Ptx.eval,s2,s1,hb,Scalar.wrap_add,Scalar.wrap_add_left,
          show wrap 64 32 = 32 by decide,bind,Except.bind,pure,Except.pure])
    simpa [s3,Ampere.intAssign,finishScalar,scalarWritten,Scalar.intAssign] using hs
  have h3 : Ampere.step ctx oracle code s3 = .ok (s4,[]) := by
    have hs := Ampere.integer_local_step (ctx := ctx) (oracle := oracle) (code := code) (s := s3)
      (instruction := .bin .add 32 32 "%it" (.reg "%it") (.imm 16))
      (by simp [s3,s2,s1,hr,hp]) (by simp [s3,s2,s1,hr,hp,code,Generated.ampere_tiled_matmul.program])
      rfl (by intro bid he; cases he)
      (show localStep ctx.params ctx.id.tid.x s3.scalar.core.thread
        (.bin .add 32 32 "%it" (.reg "%it") (.imm 16)) =
        .ok (assign s3.scalar.core.thread "%it" (wrap 32 (index+16))) by
        simp [localStep,Ptx.eval,s3,s2,s1,hi,Scalar.wrap_add,Scalar.wrap_add_left,
          show wrap 32 16 = 16 by decide,bind,Except.bind,pure,Except.pure])
    simpa [s4,Ampere.intAssign,finishScalar,scalarWritten,Scalar.intAssign] using hs
  have h4 : Ampere.step ctx oracle code s4 = .ok (s5,[]) := by
    have hs := Ampere.integer_local_step (ctx := ctx) (oracle := oracle) (code := code) (s := s4)
      (instruction := .jump 57)
      (by simp [s4,s3,s2,s1,hr]) (by simp [s4,s3,s2,s1,hp,code,Generated.ampere_tiled_matmul.program])
      rfl (by intro bid he; cases he)
      (show localStep ctx.params ctx.id.tid.x s4.scalar.core.thread (.jump 57) =
        .ok {s4.scalar.core.thread with pc := 57} by rfl)
    simpa [s5,Ampere.intPC,finishScalar,scalarWritten,Scalar.intPC] using hs
  simp only [Ampere.run,h0,h1,h2,h3,h4,Except.bind,List.nil_append]
  rfl

@[simp] theorem final_pc (s : State) (pa pah pb index : Nat) :
    (nextState s pa pah pb index).scalar.core.thread.pc = 57 := rfl
@[simp] theorem final_queries (s : State) (pa pah pb index : Nat) :
    (nextState s pa pah pb index).scalar.core.queries = s.scalar.core.queries := rfl

theorem final_pointers (s : State) (pa pah pb index : Nat) :
    lookup "%a" (nextState s pa pah pb index).scalar.core.thread.regs = some (wrap 64 (pa+32)) ∧
    lookup "%ah" (nextState s pa pah pb index).scalar.core.thread.regs = some (wrap 64 (pah+32)) ∧
    lookup "%b" (nextState s pa pah pb index).scalar.core.thread.regs = some (wrap 64 (pb+32)) ∧
    lookup "%it" (nextState s pa pah pb index).scalar.core.thread.regs = some (wrap 32 (index+16)) := by
  simp [nextState]


@[simp] theorem final_status (s : State) (pa pah pb index : Nat) :
    (nextState s pa pah pb index).scalar.core.thread.status = s.scalar.core.thread.status := rfl

theorem final_register_frame (s : State) (pa pah pb index : Nat) (name : String)
    (ha : name ≠ "%a") (hah : name ≠ "%ah") (hb : name ≠ "%b") (hi : name ≠ "%it") :
    lookup name (nextState s pa pah pb index).scalar.core.thread.regs = lookup name s.scalar.core.thread.regs := by
  simp [nextState,ha,hah,hb,hi]

theorem final_float_frame (s : State) (pa pah pb index : Nat) (name : String)
    (ha : name ≠ "%a") (hah : name ≠ "%ah") (hb : name ≠ "%b") (hi : name ≠ "%it")
    (hn : lookup name s.scalar.core.thread.regs = none) :
    declarationLookup name (nextState s pa pah pb index).scalar.floats = declarationLookup name s.scalar.floats := by
  simp [nextState,Ampere.intPC,Ampere.intAssign,ha,hah,hb,hi,hn]

end
end Ptx.AmpereTiledAdvance
