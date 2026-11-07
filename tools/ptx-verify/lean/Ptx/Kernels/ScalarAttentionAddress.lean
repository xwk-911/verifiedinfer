import Ptx.Kernels.ScalarAttentionGuards

/-! Actual output-address/zero initialization and the empty-key path. Only the
output start bound is used here; unused input/scale memory is not assumed valid.
Full four-byte allocation/UB safety remains a separate duty. -/
namespace Ptx.ScalarAttentionInit
open Ptx.ISA Ptx.Scalar Ptx.ScalarAttention
noncomputable section

def outputAddress (i : Inputs) (ctx : Scalar.Context) : Nat :=
  i.output+4*(row ctx.block ctx.id*i.dim+col ctx.block ctx.id)

structure Ready (i : Inputs) (ctx : Scalar.Context) (pc : Nat) (s : Scalar.State) : Prop extends At i ctx pc s where
  outputPointer : lookup "%op" s.core.thread.regs = some (outputAddress i ctx)
  offset : lookup "%offset" s.core.thread.regs = some (4*col ctx.block ctx.id)
  zero : declarationLookup "%out" s.floats = some (.f32,0)

theorem output_initialization (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {s : Scalar.State} (hi : At i ctx 22 s) (hb : IndexBounds ctx) (hout : outputAddress i ctx < 2^64) :
    ∃ next, Scalar.run ctx oracle code 6 s = .ok (next,[]) ∧ Ready i ctx 28 next := by
  let r := row ctx.block ctx.id
  let c := col ctx.block ctx.id
  let s1 := intAssign s "%op" (wrap 64 (r*i.dim))
  let s2 := intAssign s1 "%op" (wrap 64 ((r*i.dim)*4))
  let s3 := intAssign s2 "%offset" (4*c)
  let s4 := intAssign s3 "%op" (wrap 64 (4*(r*i.dim+c)))
  let s5 := intAssign s4 "%op" (outputAddress i ctx)
  let s6 := writeFloat s5 "%out" .f32 0
  have hrval : lookup "%row" s.core.thread.regs = some r := hi.rowValue
  have hcval : lookup "%col" s.core.thread.regs = some c := hi.colValue
  have hr32 : wrap 32 r = r := Nat.mod_eq_of_lt hb.rowBound
  have hc32 : wrap 32 c = c := Nat.mod_eq_of_lt hb.colBound
  have hd32 : wrap 32 i.dim = i.dim := Nat.mod_eq_of_lt i.dim32
  have hO64 : wrap 64 i.output = i.output := Nat.mod_eq_of_lt i.output64
  have hoff : wrap 64 (4*c) = 4*c := Nat.mod_eq_of_lt (by have := hb.colBound; change c < 2^32 at this; omega)
  have hout64 : wrap 64 (outputAddress i ctx) = outputAddress i ctx := Nat.mod_eq_of_lt hout
  have hcp : (r*i.dim)*4+4*c = 4*(r*i.dim+c) := by omega
  have hceq : c*4 = 4*c := Nat.mul_comm _ _
  have h22 : Scalar.step ctx oracle code s = .ok (s1,[]) := by
    apply integer_local_step (instruction := .bin .mul 32 64 "%op" (.reg "%row") (.reg "%d")) hi.running
      (by rw [hi.pcValue]; rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,hrval,hi.dim,hr32,hd32,bind,Except.bind,pure,Except.pure]
  have h23 : Scalar.step ctx oracle code s1 = .ok (s2,[]) := by
    apply integer_local_step (instruction := .bin .mul 64 64 "%op" (.reg "%op") (.imm 4))
      (by simpa [s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simp only [s1,intAssign,finishInteger,assign,advance,hi.pcValue]; rfl)
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s1,wrap_mul,bind,Except.bind,pure,Except.pure]
  have h24 : Scalar.step ctx oracle code s2 = .ok (s3,[]) := by
    apply integer_local_step (instruction := .bin .mul 32 64 "%offset" (.reg "%col") (.imm 4))
      (by simpa [s2,s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simp only [s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue]; rfl)
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s2,s1,hcval,hc32,hceq,hoff,show wrap 32 4 = 4 by decide,
      bind,Except.bind,pure,Except.pure]
  have h25 : Scalar.step ctx oracle code s3 = .ok (s4,[]) := by
    apply integer_local_step (instruction := .bin .add 64 64 "%op" (.reg "%op") (.reg "%offset"))
      (by simpa [s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simp only [s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue]; rfl)
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s3,s2,s1,hoff,wrap_add_left,hcp,bind,Except.bind,pure,Except.pure]
  have h26 : Scalar.step ctx oracle code s4 = .ok (s5,[]) := by
    apply integer_local_step (instruction := .bin .add 64 64 "%op" (.reg "%o") (.reg "%op"))
      (by simpa [s4,s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simp only [s4,s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue]; rfl)
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s4,s3,s2,s1,hi.output,hO64,wrap_add_right,
      show wrap 64 (i.output+4*(r*i.dim+c)) = outputAddress i ctx from hout64,
      bind,Except.bind,pure,Except.pure]
  have h27 : Scalar.step ctx oracle code s5 = .ok (s6,[]) := by
    apply mov_float_step
    · simpa [s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running
    · simp only [s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue]; rfl
    · simp [Scalar.eval]
  have hrun : Scalar.run ctx oracle code 6 s = .ok (s6,[]) := by
    simp [Scalar.run,h22,h23,h24,h25,h26,h27,Except.bind]
  refine ⟨s6,hrun,?_,?_,?_,?_⟩
  · constructor
    · simpa [s6,s5,s4,s3,s2,s1,writeFloat,intAssign,finishInteger,assign,advance] using hi.running
    · simp [s6,s5,s4,s3,s2,s1,writeFloat,intAssign,finishInteger,assign,advance,hi.pcValue]
    · simpa [s6,s5,s4,s3,s2,s1,writeFloat,intAssign,finishInteger] using hi.queries
    · simpa [s6,s5,s4,s3,s2,s1] using hi.q
    · simpa [s6,s5,s4,s3,s2,s1] using hi.key
    · simpa [s6,s5,s4,s3,s2,s1] using hi.value
    · simpa [s6,s5,s4,s3,s2,s1] using hi.output
    · simpa [s6,s5,s4,s3,s2,s1] using hi.scale
    · simpa [s6,s5,s4,s3,s2,s1] using hi.m
    · simpa [s6,s5,s4,s3,s2,s1] using hi.n
    · simpa [s6,s5,s4,s3,s2,s1] using hi.dim
    · simpa [s6,s5,s4,s3,s2,s1] using hi.rowValue
    · simpa [s6,s5,s4,s3,s2,s1] using hi.colValue
    · exact run_banks_disjoint hrun hi.banks
  · simp [s6,s5]
  · simp [s6,s5,s4,s3,c]
  · simp [s6]

theorem after_guard_ready {i ctx pc s} (hi : Ready i ctx pc s) (flag nextPC : Nat) :
    Ready i ctx nextPC (afterGuard s flag nextPC) := by
  have hf : RegisterFrame ["%p"] s (afterGuard s flag nextPC) := register_frame_trans
    (intAssign_register_frame hi.banks "%p" flag (by decide)) (intPC_register_frame (intAssign_banks _ _ _) nextPC)
  exact ⟨after_guard_facts hi.toAt flag nextPC,((hf "%op" (by decide)).1).trans hi.outputPointer,
    ((hf "%offset" (by decide)).1).trans hi.offset,((hf "%out" (by decide)).2).trans hi.zero⟩

theorem empty_guard_run (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {s} (hi : Ready i ctx 28 s) : Scalar.run ctx oracle code 2 s = .ok
      (afterGuard s (if i.n = 0 then 1 else 0) (if i.n = 0 then 74 else 30),[]) := by
  have h := eq_branch_run (ctx := ctx) (oracle := oracle) (code := code) (s := s)
    (lhs := .reg "%n") (rhs := .imm 0) (pred := "%p") (target := 74) (x := i.n) (y := 0)
    hi.running (by rw [hi.pcValue]; rfl) (by rw [hi.pcValue]; rfl)
    (by simp [Ptx.eval,hi.n]) rfl i.n32 (by decide)
  simpa only [hi.pcValue,afterGuard] using h

theorem empty_store_return (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {s} (hi : Ready i ctx 74 s) (hout : outputAddress i ctx < 2^64) :
    ∃ final, Scalar.run ctx oracle code 2 s = .ok
      (final,[.write ⟨.global,outputAddress i ctx⟩ (Symbolic.encode .f32 0)]) ∧
      final.core.thread.status = .done ∧ final.core.queries = 0 := by
  let mid : Scalar.State := {s with core := {s.core with thread := advance s.core.thread}}
  have h74 : Scalar.step ctx oracle code s = .ok
      (mid,[.write ⟨.global,outputAddress i ctx⟩ (Symbolic.encode .f32 0)]) := by
    apply store_step (format := .f32) (space := .global) (address := {base := .reg "%op"})
      (value := .reg "%out") (addr := outputAddress i ctx) (x := 0) hi.running (by rw [hi.pcValue]; rfl)
    · simp [evalAddr,Ptx.eval,hi.outputPointer,show wrap 64 (outputAddress i ctx) = outputAddress i ctx from Nat.mod_eq_of_lt hout,
        bind,Except.bind,pure,Except.pure]
    · simp [Scalar.eval,require,hi.zero,bind,Except.bind,pure,Except.pure]
  obtain ⟨final,hret,hd,hq⟩ := masked_return ctx oracle (s := mid)
    (by simpa [mid,advance] using hi.running) (by simp [mid,advance,hi.pcValue])
  have hstore : Scalar.run ctx oracle code 1 s = .ok
      (mid,[.write ⟨.global,outputAddress i ctx⟩ (Symbolic.encode .f32 0)]) := by
    simp [Scalar.run,h74,Except.bind]
  exact ⟨final,Scalar.run_append hstore hret,hd,hq.trans hi.queries⟩

end
end Ptx.ScalarAttentionInit
