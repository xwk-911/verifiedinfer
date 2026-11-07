import Ptx.Kernels.ScalarMatmulGuards

/-! Checked address/accumulator initialization (generated PCs 20--31).
Pointer expressions retain modular arithmetic; active-load bounds are separate.
No input-memory agreement or launch-wide consistency follows from this block. -/
namespace Ptx.ScalarMatmulInit
open Ptx.ISA Ptx.Scalar Ptx.ScalarMatmul
noncomputable section

structure AddressBounds (i : Inputs) (ctx : Scalar.Context) : Prop where
  output64 : i.c+4*(row ctx.block ctx.id*i.n+col ctx.block ctx.id) < 2^64
  aRead64 : ∀ k, k < i.k → i.a+4*(row ctx.block ctx.id*i.k)+4*k < 2^64
  bRead64 : ∀ k, k < i.k → i.b+4*col ctx.block ctx.id+(4*i.n)*k < 2^64

def threadLayout (i : Inputs) (ctx : Scalar.Context) (h : AddressBounds i ctx) : ScalarMatmulLoop.Layout := {
  count := i.k
  aBase := i.a+4*(row ctx.block ctx.id*i.k)
  bBase := i.b+4*col ctx.block ctx.id
  stride := 4*i.n
  output := i.c+4*(row ctx.block ctx.id*i.n+col ctx.block ctx.id)
  count32 := i.k32
  output64 := h.output64
  aRead64 := h.aRead64
  bRead64 := h.bRead64
}

theorem address_run (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {s : Scalar.State} (hi : At i ctx 20 s) (hb : IndexBounds ctx) (ha : AddressBounds i ctx) :
    ∃ next, Scalar.run ctx oracle code 12 s = .ok (next,[]) ∧
      ScalarMatmulLoop.Inv (threadLayout i ctx ha) 0 0 next := by
  let r := row ctx.block ctx.id
  let c := col ctx.block ctx.id
  let s1 := intAssign s "%ap" (wrap 64 (r*i.k))
  let s2 := intAssign s1 "%ap" (wrap 64 ((r*i.k)*4))
  let s3 := intAssign s2 "%ap" (wrap 64 (i.a+4*(r*i.k)))
  let s4 := intAssign s3 "%offset" (4*c)
  let s5 := intAssign s4 "%bp" (wrap 64 (i.b+4*c))
  let s6 := intAssign s5 "%stride" (4*i.n)
  let s7 := intAssign s6 "%cp" (wrap 64 (r*i.n))
  let s8 := intAssign s7 "%cp" (wrap 64 ((r*i.n)*4))
  let s9 := intAssign s8 "%cp" (wrap 64 (4*(r*i.n+c)))
  let s10 := intAssign s9 "%cp" (i.c+4*(r*i.n+c))
  let s11 := writeFloat s10 "%acc" .f32 0
  let s12 := intAssign s11 "%k" (0)
  have hrval : lookup "%row" s.core.thread.regs = some r := hi.rowValue
  have hcval : lookup "%col" s.core.thread.regs = some c := hi.colValue
  have hr32 : wrap 32 r = r := Nat.mod_eq_of_lt hb.rowBound
  have hc32 : wrap 32 c = c := Nat.mod_eq_of_lt hb.colBound
  have hk32 : wrap 32 i.k = i.k := Nat.mod_eq_of_lt i.k32
  have hn32 : wrap 32 i.n = i.n := Nat.mod_eq_of_lt i.n32
  have hA64 : wrap 64 i.a = i.a := Nat.mod_eq_of_lt i.a64
  have hB64 : wrap 64 i.b = i.b := Nat.mod_eq_of_lt i.b64
  have hC64 : wrap 64 i.c = i.c := Nat.mod_eq_of_lt i.c64
  have hoff : wrap 64 (4*c) = 4*c := Nat.mod_eq_of_lt (by have := hb.colBound; change c < 2^32 at this; omega)
  have hstride : wrap 64 (4*i.n) = 4*i.n := Nat.mod_eq_of_lt (by have := i.n32; omega)
  have hout : wrap 64 (i.c+4*(r*i.n+c)) = i.c+4*(r*i.n+c) := Nat.mod_eq_of_lt ha.output64
  have hcp : (r*i.n)*4+4*c = 4*(r*i.n+c) := by omega
  have hAeq : (r*i.k)*4 = 4*(r*i.k) := Nat.mul_comm _ _
  have hceq : c*4 = 4*c := Nat.mul_comm _ _
  have hneq : i.n*4 = 4*i.n := Nat.mul_comm _ _
  have h20 : Scalar.step ctx oracle code s = .ok (s1,[]) := by
    apply Scalar.integer_local_step (instruction := .bin .mul 32 64 "%ap" (.reg "%row") (.reg "%kmax"))
    · exact hi.running
    · simp [hi.pcValue,code,Generated.scalar_matmul.program]
    · rfl
    · intro bid h; cases h
    · simp [localStep,Ptx.eval,hrval,hi.k,hr32,hk32,
        bind,Except.bind,pure,Except.pure]
  have h21 : Scalar.step ctx oracle code s1 = .ok (s2,[]) := by
    apply Scalar.integer_local_step (instruction := .bin .mul 64 64 "%ap" (.reg "%ap") (.imm 4))
    · simpa [s1,intAssign,finishInteger,assign,advance] using hi.running
    · simp [s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.scalar_matmul.program]
    · rfl
    · intro bid h; cases h
    · simp [localStep,Ptx.eval,s1,wrap_mul,
        bind,Except.bind,pure,Except.pure]
  have h22 : Scalar.step ctx oracle code s2 = .ok (s3,[]) := by
    apply Scalar.integer_local_step (instruction := .bin .add 64 64 "%ap" (.reg "%a") (.reg "%ap"))
    · simpa [s2,s1,intAssign,finishInteger,assign,advance] using hi.running
    · simp [s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.scalar_matmul.program]
    · rfl
    · intro bid h; cases h
    · simp [localStep,Ptx.eval,s2,s1,hi.a,hA64,wrap_add_right,hAeq,
        bind,Except.bind,pure,Except.pure]
  have h23 : Scalar.step ctx oracle code s3 = .ok (s4,[]) := by
    apply Scalar.integer_local_step (instruction := .bin .mul 32 64 "%offset" (.reg "%col") (.imm 4))
    · simpa [s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running
    · simp [s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.scalar_matmul.program]
    · rfl
    · intro bid h; cases h
    · simp [localStep,Ptx.eval,s3,s2,s1,hcval,hc32,hceq,hoff,show wrap 32 4 = 4 by decide,
        bind,Except.bind,pure,Except.pure]
  have h24 : Scalar.step ctx oracle code s4 = .ok (s5,[]) := by
    apply Scalar.integer_local_step (instruction := .bin .add 64 64 "%bp" (.reg "%b") (.reg "%offset"))
    · simpa [s4,s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running
    · simp [s4,s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.scalar_matmul.program]
    · rfl
    · intro bid h; cases h
    · simp [localStep,Ptx.eval,s4,s3,s2,s1,hi.b,hB64,hoff,
        bind,Except.bind,pure,Except.pure]
  have h25 : Scalar.step ctx oracle code s5 = .ok (s6,[]) := by
    apply Scalar.integer_local_step (instruction := .bin .mul 32 64 "%stride" (.reg "%n") (.imm 4))
    · simpa [s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running
    · simp [s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.scalar_matmul.program]
    · rfl
    · intro bid h; cases h
    · simp [localStep,Ptx.eval,s5,s4,s3,s2,s1,hi.n,hn32,hneq,hstride,show wrap 32 4 = 4 by decide,
        bind,Except.bind,pure,Except.pure]
  have h26 : Scalar.step ctx oracle code s6 = .ok (s7,[]) := by
    apply Scalar.integer_local_step (instruction := .bin .mul 32 64 "%cp" (.reg "%row") (.reg "%n"))
    · simpa [s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running
    · simp [s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.scalar_matmul.program]
    · rfl
    · intro bid h; cases h
    · simp [localStep,Ptx.eval,s6,s5,s4,s3,s2,s1,hrval,hi.n,hr32,hn32,
        bind,Except.bind,pure,Except.pure]
  have h27 : Scalar.step ctx oracle code s7 = .ok (s8,[]) := by
    apply Scalar.integer_local_step (instruction := .bin .mul 64 64 "%cp" (.reg "%cp") (.imm 4))
    · simpa [s7,s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running
    · simp [s7,s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.scalar_matmul.program]
    · rfl
    · intro bid h; cases h
    · simp [localStep,Ptx.eval,s7,s6,s5,s4,s3,s2,s1,wrap_mul,
        bind,Except.bind,pure,Except.pure]
  have h28 : Scalar.step ctx oracle code s8 = .ok (s9,[]) := by
    apply Scalar.integer_local_step (instruction := .bin .add 64 64 "%cp" (.reg "%cp") (.reg "%offset"))
    · simpa [s8,s7,s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running
    · simp [s8,s7,s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.scalar_matmul.program]
    · rfl
    · intro bid h; cases h
    · simp [localStep,Ptx.eval,s8,s7,s6,s5,s4,s3,s2,s1,hoff,wrap_add_left,hcp,
        bind,Except.bind,pure,Except.pure]
  have h29 : Scalar.step ctx oracle code s9 = .ok (s10,[]) := by
    apply Scalar.integer_local_step (instruction := .bin .add 64 64 "%cp" (.reg "%c") (.reg "%cp"))
    · simpa [s9,s8,s7,s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running
    · simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.scalar_matmul.program]
    · rfl
    · intro bid h; cases h
    · simp [localStep,Ptx.eval,s9,s8,s7,s6,s5,s4,s3,s2,s1,hi.c,hC64,wrap_add_right,hout,
        bind,Except.bind,pure,Except.pure]
  have h30 : Scalar.step ctx oracle code s10 = .ok (s11,[]) := by
    have hr : s10.core.thread.status = .running := by
      simpa [s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running
    have hc : code[s10.core.thread.pc]? = some (.mov .f32 "%acc" (.literal {bits := 0,bounded := by decide,finite := by decide})) := by
      simp [s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.scalar_matmul.program]
    simp [s11,Scalar.step,hr,hc,Scalar.require,Scalar.eval,F32Literal.zero_value,bind,Except.bind,pure,Except.pure]
  have h31 : Scalar.step ctx oracle code s11 = .ok (s12,[]) := by
    apply Scalar.integer_local_step (instruction := .mov 32 "%k" (.imm 0))
    · simpa [s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance,writeFloat] using hi.running
    · simp [s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance,writeFloat,hi.pcValue,code,Generated.scalar_matmul.program]
    · rfl
    · intro bid h; cases h
    · simp [localStep,Ptx.eval,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,show wrap 32 0 = 0 by decide,
        bind,Except.bind,pure,Except.pure]
  have hr : Scalar.run ctx oracle code 12 s = .ok (s12,[]) := by
    simp [Scalar.run,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,Except.bind]
  refine ⟨s12,hr,?_⟩
  constructor
  · simpa [s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,intAssign,writeFloat,finishInteger,assign,advance] using hi.running
  · simp [s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,intAssign,writeFloat,finishInteger,assign,advance,hi.pcValue]
  · simpa [s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,intAssign,writeFloat,finishInteger] using hi.queries
  · simp [s12]
  · simp [s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,threadLayout,hi.k]
  · simp [s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,threadLayout,r]
  · simp [s12,s11,s10,s9,s8,s7,s6,s5,threadLayout,c]
  · simp [s12,s11,s10,s9,s8,s7,s6,threadLayout]
  · simp [s12,s11,s10,threadLayout,r,c]
  · simp [s12,s11]
  · exact run_banks_disjoint hr hi.banks

end
end Ptx.ScalarMatmulInit
