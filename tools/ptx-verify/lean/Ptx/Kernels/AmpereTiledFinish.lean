import Ptx.Generated.AmpereTiledMatmul
import Ptx.Ampere.ScalarSteps
import Ptx.Ampere.MmaBlock
import Ptx.Ampere.Trace

/-! Actual four f32 stores and return. This describes arbitrary accumulator
values; the matrix result must be derived separately from memory/MMA agreement. -/
namespace Ptx.AmpereTiledFinish
open Ptx.ISA Ptx.Ampere
noncomputable section
abbrev code := Generated.ampere_tiled_matmul.program

def stopped (s : State) : State := {s with scalar := Scalar.finishInteger s.scalar {
  s.scalar.core with thread := {s.scalar.core.thread with status := .done}}}
def finalState (s : State) : State := stopped (Ampere.advance (Ampere.advance (Ampere.advance (Ampere.advance s))))
def events (low high : Nat) (acc : Fin 4 → ℝ) : List Event := [
  .ordinary (.write ⟨.global,wrap 64 low⟩ (Symbolic.encode .f32 (acc 0))),
  .ordinary (.write ⟨.global,wrap 64 (low+4)⟩ (Symbolic.encode .f32 (acc 1))),
  .ordinary (.write ⟨.global,wrap 64 high⟩ (Symbolic.encode .f32 (acc 2))),
  .ordinary (.write ⟨.global,wrap 64 (high+4)⟩ (Symbolic.encode .f32 (acc 3)))]

theorem execute (ctx : Scalar.Context) (oracle : Oracle) (s : State) (low high : Nat) (acc : Fin 4 → ℝ)
    (hr : s.scalar.core.thread.status = .running) (hp : s.scalar.core.thread.pc = 78)
    (hl : lookup "%c" s.scalar.core.thread.regs = some low)
    (hh : lookup "%ch" s.scalar.core.thread.regs = some high)
    (hc : ∀ i, declarationLookup (MmaBlock.accumulators.get i) s.scalar.floats = some (.f32,acc i)) :
    Ampere.run ctx oracle code 5 s = .ok (finalState s,events low high acc) := by
  let s1 := Ampere.advance s
  let s2 := Ampere.advance s1
  let s3 := Ampere.advance s2
  let s4 := Ampere.advance s3
  let s5 := stopped s4
  have hc0 := hc (0 : Fin 4)
  have hc1 := hc (1 : Fin 4)
  have hc2 := hc (2 : Fin 4)
  have hc3 := hc (3 : Fin 4)
  dsimp [MmaBlock.accumulators,Registers4.get] at hc0 hc1 hc2 hc3
  have hi0 : code[s.scalar.core.thread.pc]? = some (.scalar (.store .f32 .global
      {base := .reg "%c",offset := 0} (.reg "%acc0"))) := by
    simp [Ampere.advance,Ptx.advance,hp,code,Generated.ampere_tiled_matmul.program]
  have hs0 := Scalar.store_step (ctx := ctx) (oracle := oracle.scalar) (code := scalarSkeleton code) (s := s.scalar)
    (format := .f32) (space := .global) (address := {base := .reg "%c",offset := 0})
    (value := .reg "%acc0") (addr := wrap 64 (low+0)) (x := acc 0)
    (by simpa [Ampere.advance,Ptx.advance] using hr) (scalarSkeleton_slot hi0)
    (by simp [evalAddr,Ptx.eval,Ampere.advance,Ptx.advance,hl,hh,bind,Except.bind,pure,Except.pure])
    (by simp [Scalar.eval,Scalar.require,Ampere.advance,hc0,bind,Except.bind,pure,Except.pure])
  have h0 : Ampere.step ctx oracle code s =
      .ok (s1,[.ordinary (.write ⟨.global,wrap 64 (low+0)⟩ (Symbolic.encode .f32 (acc 0)))]) := by
    simpa [s1,Ampere.advance,finishScalar,scalarWritten,Location.resolve] using scalar_step
      (by simpa [Ampere.advance,Ptx.advance] using hr) hi0 hs0
  have hi1 : code[s1.scalar.core.thread.pc]? = some (.scalar (.store .f32 .global
      {base := .reg "%c",offset := 4} (.reg "%acc1"))) := by
    simp [s1,Ampere.advance,Ptx.advance,hp,code,Generated.ampere_tiled_matmul.program]
  have hs1 := Scalar.store_step (ctx := ctx) (oracle := oracle.scalar) (code := scalarSkeleton code) (s := s1.scalar)
    (format := .f32) (space := .global) (address := {base := .reg "%c",offset := 4})
    (value := .reg "%acc1") (addr := wrap 64 (low+4)) (x := acc 1)
    (by simpa [s1,Ampere.advance,Ptx.advance] using hr) (scalarSkeleton_slot hi1)
    (by simp [evalAddr,Ptx.eval,s1,Ampere.advance,Ptx.advance,hl,hh,bind,Except.bind,pure,Except.pure])
    (by simp [Scalar.eval,Scalar.require,s1,Ampere.advance,hc1,bind,Except.bind,pure,Except.pure])
  have h1 : Ampere.step ctx oracle code s1 =
      .ok (s2,[.ordinary (.write ⟨.global,wrap 64 (low+4)⟩ (Symbolic.encode .f32 (acc 1)))]) := by
    simpa [s2,Ampere.advance,finishScalar,scalarWritten,Location.resolve] using scalar_step
      (by simpa [s1,Ampere.advance,Ptx.advance] using hr) hi1 hs1
  have hi2 : code[s2.scalar.core.thread.pc]? = some (.scalar (.store .f32 .global
      {base := .reg "%ch",offset := 0} (.reg "%acc2"))) := by
    simp [s2,s1,Ampere.advance,Ptx.advance,hp,code,Generated.ampere_tiled_matmul.program]
  have hs2 := Scalar.store_step (ctx := ctx) (oracle := oracle.scalar) (code := scalarSkeleton code) (s := s2.scalar)
    (format := .f32) (space := .global) (address := {base := .reg "%ch",offset := 0})
    (value := .reg "%acc2") (addr := wrap 64 (high+0)) (x := acc 2)
    (by simpa [s2,s1,Ampere.advance,Ptx.advance] using hr) (scalarSkeleton_slot hi2)
    (by simp [evalAddr,Ptx.eval,s2,s1,Ampere.advance,Ptx.advance,hl,hh,bind,Except.bind,pure,Except.pure])
    (by simp [Scalar.eval,Scalar.require,s2,s1,Ampere.advance,hc2,bind,Except.bind,pure,Except.pure])
  have h2 : Ampere.step ctx oracle code s2 =
      .ok (s3,[.ordinary (.write ⟨.global,wrap 64 (high+0)⟩ (Symbolic.encode .f32 (acc 2)))]) := by
    simpa [s3,Ampere.advance,finishScalar,scalarWritten,Location.resolve] using scalar_step
      (by simpa [s2,s1,Ampere.advance,Ptx.advance] using hr) hi2 hs2
  have hi3 : code[s3.scalar.core.thread.pc]? = some (.scalar (.store .f32 .global
      {base := .reg "%ch",offset := 4} (.reg "%acc3"))) := by
    simp [s3,s2,s1,Ampere.advance,Ptx.advance,hp,code,Generated.ampere_tiled_matmul.program]
  have hs3 := Scalar.store_step (ctx := ctx) (oracle := oracle.scalar) (code := scalarSkeleton code) (s := s3.scalar)
    (format := .f32) (space := .global) (address := {base := .reg "%ch",offset := 4})
    (value := .reg "%acc3") (addr := wrap 64 (high+4)) (x := acc 3)
    (by simpa [s3,s2,s1,Ampere.advance,Ptx.advance] using hr) (scalarSkeleton_slot hi3)
    (by simp [evalAddr,Ptx.eval,s3,s2,s1,Ampere.advance,Ptx.advance,hl,hh,bind,Except.bind,pure,Except.pure])
    (by simp [Scalar.eval,Scalar.require,s3,s2,s1,Ampere.advance,hc3,bind,Except.bind,pure,Except.pure])
  have h3 : Ampere.step ctx oracle code s3 =
      .ok (s4,[.ordinary (.write ⟨.global,wrap 64 (high+4)⟩ (Symbolic.encode .f32 (acc 3)))]) := by
    simpa [s4,Ampere.advance,finishScalar,scalarWritten,Location.resolve] using scalar_step
      (by simpa [s3,s2,s1,Ampere.advance,Ptx.advance] using hr) hi3 hs3
  have h4 : Ampere.step ctx oracle code s4 = .ok (s5,[]) := by
    have hs := Ampere.integer_local_step (ctx := ctx) (oracle := oracle) (code := code) (s := s4)
      (instruction := .ret) (by simpa [s4,s3,s2,s1,Ampere.advance,Ptx.advance] using hr)
      (by simp [s4,s3,s2,s1,Ampere.advance,Ptx.advance,hp,code,Generated.ampere_tiled_matmul.program])
      rfl (by intro bid he; cases he)
      (show localStep ctx.params ctx.id.tid.x s4.scalar.core.thread .ret =
        .ok {s4.scalar.core.thread with status := .done} by rfl)
    simpa [s5,stopped,finishScalar,scalarWritten] using hs
  simp only [Ampere.run,h0,h1,h2,h3,h4,Except.bind]
  simp [finalState,events,s5,s4,s3,s2,s1]

@[simp] theorem final_done (s : State) : (finalState s).scalar.core.thread.status = .done := rfl
@[simp] theorem final_queries (s : State) : (finalState s).scalar.core.queries = s.scalar.core.queries := rfl

end
end Ptx.AmpereTiledFinish
