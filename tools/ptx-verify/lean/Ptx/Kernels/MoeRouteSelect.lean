import Ptx.Generated.MoeRoute
import Ptx.Kernels.MoeSpec
import Ptx.Scalar.Compare
import Ptx.Scalar.Execution
import Mathlib.Tactic.NormNum

/-! Actual route source PCs 16--22: ordered score comparison, both branch paths,
u32 selection store and return. Gate-load/entry and global-memory correspondence
are separate duties; no claim about complete kernel candidates is made here. -/
namespace Ptx.MoeRouteSelect
open Ptx.ISA Ptx.Scalar
noncomputable section
abbrev code := Generated.moe_route.program

structure Ready (gates : Moe.Matrix) (row dst : Nat) (s : Scalar.State) : Prop where
  running : s.core.thread.status = .running
  pc : s.core.thread.pc = 16
  pointer : lookup "%rp" s.core.thread.regs = some dst
  first : declarationLookup "%g0" s.floats = some (.f32,gates row 0)
  second : declarationLookup "%g1" s.floats = some (.f32,gates row 1)

def final (s : Scalar.State) (expert : Nat) : Scalar.State :=
  let compared := intAssign s "%p" expert
  let zeroed := intAssign compared "%expert" 0
  let branched := intPC zeroed (if expert = 1 then 20 else 19)
  let chosen := if expert = 1 then intAssign branched "%expert" 1 else intPC branched 21
  let stored := intPC chosen 22
  finishInteger stored {stored.core with thread := {stored.core.thread with status := .done}}

theorem selection_agrees (gates : Moe.Matrix) (row : Nat) : gtFlag (gates row 1) (gates row 0) = Moe.selected gates row := rfl

theorem complete_suffix (ctx : Scalar.Context) (oracle : Scalar.Oracle) (gates : Moe.Matrix) (row dst : Nat)
    {s : Scalar.State} (hi : Ready gates row dst s) (hd : dst < 2^64) :
    Scalar.run ctx oracle code 6 s = .ok
      (final s (Moe.selected gates row),[.write ⟨.global,dst⟩ (u32Bytes (Moe.selected gates row))]) := by
  let e := Moe.selected gates row
  let s1 := intAssign s "%p" e
  let s2 := intAssign s1 "%expert" 0
  let s3 := intPC s2 (if e = 1 then 20 else 19)
  let s4 := if e = 1 then intAssign s3 "%expert" 1 else intPC s3 21
  let s5 := intPC s4 22
  have he : e = 0 ∨ e = 1 := by have := Moe.selected_bound gates row; omega
  have h0 : Scalar.step ctx oracle code s = .ok (s1,[]) := by
    apply setp_gt_step (format := .f32) (a := .reg "%g1") (b := .reg "%g0")
      (x := gates row 1) (y := gates row 0) hi.running (by simp [code,Generated.moe_route.program,hi.pc])
      (by simp [Scalar.eval,hi.second,Scalar.require,bind,Except.bind,pure,Except.pure])
      (by simp [Scalar.eval,hi.first,Scalar.require,bind,Except.bind,pure,Except.pure])
  have h1 : Scalar.step ctx oracle code s1 = .ok (s2,[]) := by
    apply integer_local_step (instruction := .mov 32 "%expert" (.imm 0))
      (by simp [s1,intAssign,finishInteger,assign,advance,hi.running])
      (by simp [s1,intAssign,finishInteger,assign,advance,code,Generated.moe_route.program,hi.pc])
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s2,intAssign,wrap,bind,Except.bind,pure,Except.pure]
  have h2 : Scalar.step ctx oracle code s2 = .ok (s3,[]) := by
    apply integer_local_step (instruction := .branch "%p" true 20)
      (by simp [s2,s1,intAssign,finishInteger,assign,advance,hi.running])
      (by simp [s2,s1,intAssign,finishInteger,assign,advance,code,Generated.moe_route.program,hi.pc])
      rfl (by intro bid h; cases h)
    rcases he with hz | hz <;>
      simp [localStep,s3,s2,s1,intAssign,intPC,finishInteger,assign,advance,hz,hi.pc,
        bind,Except.bind,pure,Except.pure]
  have h3 : Scalar.step ctx oracle code s3 = .ok (s4,[]) := by
    rcases he with hz | hz
    · have hs4 : s4 = intPC s3 21 := by simp [s4,hz]
      rw [hs4]
      apply integer_local_step (instruction := .jump 21)
        (by simp [s3,s2,s1,intPC,intAssign,finishInteger,assign,advance,hi.running])
        (by simp [s3,intPC,finishInteger,hz,code,Generated.moe_route.program])
        rfl (by intro bid h; cases h)
      simp [s4,hz,localStep,intPC,pure,Except.pure]
    · have hs4 : s4 = intAssign s3 "%expert" 1 := by simp [s4,hz]
      rw [hs4]
      apply integer_local_step (instruction := .mov 32 "%expert" (.imm 1))
        (by simp [s3,s2,s1,intPC,intAssign,finishInteger,assign,advance,hi.running])
        (by simp [s3,intPC,finishInteger,hz,code,Generated.moe_route.program])
        rfl (by intro bid h; cases h)
      simp [s4,hz,localStep,Ptx.eval,intAssign,wrap,bind,Except.bind,pure,Except.pure]
  have hpc : s4.core.thread.pc = 21 := by
    rcases he with hz | hz <;> simp [s4,s3,intAssign,intPC,finishInteger,assign,advance,hz]
  have hr : s4.core.thread.status = .running := by
    rcases he with hz | hz <;> simp [s4,s3,s2,s1,intAssign,intPC,finishInteger,assign,advance,hz,hi.running]
  have hptr : lookup "%rp" s4.core.thread.regs = some dst := by
    rcases he with hz | hz <;> simp [s4,s3,s2,s1,hz,hi.pointer]
  have hexpert : lookup "%expert" s4.core.thread.regs = some e := by
    rcases he with hz | hz <;> simp [s4,s3,s2,s1,hz]
  have h4 : Scalar.step ctx oracle code s4 = .ok (s5,[.write ⟨.global,dst⟩ (u32Bytes e)]) := by
    have h := integer_store_step (ctx := ctx) (oracle := oracle) (code := code) (s := s4)
      (space := .global) (address := {base := .reg "%rp"}) (operand := .reg "%expert")
      (addr := dst) (value := e) hr
      (by simp [code,Generated.moe_route.program,hpc])
      (by simp [evalAddr,Ptx.eval,hptr,show wrap 64 dst = dst from Nat.mod_eq_of_lt hd])
      (by simp [Ptx.eval,hexpert])
    have hw : wrap 32 e = e := Nat.mod_eq_of_lt (by rcases he with hz | hz <;> simp [hz])
    simpa [s5,intPC,advance,hpc,u32Bytes,Location.resolve,hw] using h
  have h5 : Scalar.step ctx oracle code s5 = .ok (final s e,[]) := by
    have h := integer_local_step (ctx := ctx) (oracle := oracle) (code := code) (s := s5)
      (instruction := .ret)
      (by simpa [s5,intPC,finishInteger] using hr)
      (by simp [s5,intPC,finishInteger,code,Generated.moe_route.program])
      rfl (by intro bid h; cases h) rfl
    simpa [final,s5,s4,s3,s2,s1] using h
  simp only [Scalar.run,h0,h1,h2,h3,h4,h5,Except.bind,List.nil_append,List.append_nil]
  rfl

theorem final_done (s : Scalar.State) (expert : Nat) : (final s expert).core.thread.status = .done := rfl
theorem final_queries (s : Scalar.State) (expert : Nat) : (final s expert).core.queries = s.core.queries := by
  simp only [final,intAssign,intPC,finishInteger]
  split <;> rfl

theorem completed_suffix {ctx oracle gates row dst s n last events}
    (hi : Ready gates row dst s) (hd : dst < 2^64)
    (hn : Scalar.run ctx oracle code n s = .ok (last,events))
    (hfinished : last.core.thread.status = .done) :
    n = 6 ∧ last = final s (Moe.selected gates row) ∧
      events = [.write ⟨.global,dst⟩ (u32Bytes (Moe.selected gates row))] :=
  complete_run_unique hn hfinished (complete_suffix ctx oracle gates row dst hi hd) (final_done _ _)

end
end Ptx.MoeRouteSelect
