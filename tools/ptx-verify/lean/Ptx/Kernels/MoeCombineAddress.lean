import Ptx.Kernels.MoeCombineSelect

/-! Actual PC29--37 gather address calculation; no source load is assumed. -/
namespace Ptx.MoeCombine
open Ptx.ISA Ptx.Scalar
noncomputable section

def hAddress (i : Inputs) (ctx : Scalar.Context) (expert : Nat) : Nat :=
  hBase i expert+4*(row ctx.block ctx.id*i.n+col ctx.block ctx.id)
def yAddress (i : Inputs) (ctx : Scalar.Context) : Nat :=
  i.y+4*(row ctx.block ctx.id*i.n+col ctx.block ctx.id)
structure AddressBounds (i : Inputs) (ctx : Scalar.Context) (expert : Nat) : Prop where
  read64 : hAddress i ctx expert < 2^64
  write64 : yAddress i ctx < 2^64
structure Ready (i : Inputs) (ctx : Scalar.Context) (expert : Nat) (s : Scalar.State) : Prop where
  running : s.core.thread.status = .running
  pcValue : s.core.thread.pc = 38
  queries : s.core.queries = 1
  readPtr : lookup "%hp" s.core.thread.regs = some (hAddress i ctx expert)
  writePtr : lookup "%yp" s.core.thread.regs = some (yAddress i ctx)
  banks : BanksDisjoint s

theorem address_run (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) (expert : Nat)
    {s : Scalar.State} (hi : Selected i ctx expert s) (hb : IndexBounds ctx) (ha : AddressBounds i ctx expert) :
    ∃ next, Scalar.run ctx oracle code 9 s = .ok (next,[]) ∧ Ready i ctx expert next := by
  let r := row ctx.block ctx.id
  let c := col ctx.block ctx.id
  let s1 := intAssign s "%hp" (wrap 64 (r*i.n))
  let s2 := intAssign s1 "%hp" (wrap 64 (4*(r*i.n)))
  let s3 := intAssign s2 "%hp" (wrap 64 (4*(r*i.n)+hBase i expert))
  let s4 := intAssign s3 "%yp" (wrap 64 (r*i.n))
  let s5 := intAssign s4 "%yp" (wrap 64 (4*(r*i.n)))
  let s6 := intAssign s5 "%yp" (wrap 64 (4*(r*i.n)+i.y))
  let s7 := intAssign s6 "%rp" (4*c)
  let s8 := intAssign s7 "%hp" (hAddress i ctx expert)
  let s9 := intAssign s8 "%yp" (yAddress i ctx)
  have hrval : lookup "%row" s.core.thread.regs = some r := hi.rowValue
  have hcval : lookup "%col" s.core.thread.regs = some c := hi.colValue
  have hprod : (r*i.n)*4 = 4*(r*i.n) := Nat.mul_comm _ _
  have hcol : c*4 = 4*c := Nat.mul_comm _ _
  have hfour : wrap 32 4 = 4 := by decide
  have hr32 : wrap 32 r = r := Nat.mod_eq_of_lt hb.rowBound
  have hc32 : wrap 32 c = c := Nat.mod_eq_of_lt hb.colBound
  have hn32 : wrap 32 i.n = i.n := Nat.mod_eq_of_lt i.n32
  have hy64 : wrap 64 i.y = i.y := Nat.mod_eq_of_lt i.y64
  have hc64 : wrap 64 (4*c) = 4*c := Nat.mod_eq_of_lt (by have := hb.colBound; change c < 2^32 at this; omega)
  have hh : wrap 64 (hAddress i ctx expert) = hAddress i ctx expert := Nat.mod_eq_of_lt ha.read64
  have hy : wrap 64 (yAddress i ctx) = yAddress i ctx := Nat.mod_eq_of_lt ha.write64
  have haddr : 4*(r*i.n)+hBase i expert+4*c = hAddress i ctx expert := by dsimp [hAddress,r,c]; omega
  have yaddr : 4*(r*i.n)+i.y+4*c = yAddress i ctx := by dsimp [yAddress,r,c]; omega
  have h0 : Scalar.step ctx oracle code s = .ok (s1,[]) := by
    apply integer_local_step (instruction := .bin .mul 32 64 "%hp" (.reg "%row") (.reg "%n"))
      (by simpa [intAssign,finishInteger,assign,advance] using hi.running)
      (by simp [intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.moe_combine.program])
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,hi.h,hi.y,hi.n,hrval,hcval,hr32,hc32,hn32,hy64,hc64,
      wrap_mul,wrap_add,wrap_add_left,wrap_add_right,hprod,hcol,hfour,haddr,yaddr,hh,hy,
      bind,Except.bind,pure,Except.pure]
  have h1 : Scalar.step ctx oracle code s1 = .ok (s2,[]) := by
    apply integer_local_step (instruction := .bin .mul 64 64 "%hp" (.reg "%hp") (.imm 4))
      (by simpa [s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simp [s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.moe_combine.program])
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s1,hi.h,hi.y,hi.n,hrval,hcval,hr32,hc32,hn32,hy64,hc64,
      wrap_mul,wrap_add,wrap_add_left,wrap_add_right,hprod,hcol,hfour,haddr,yaddr,hh,hy,
      bind,Except.bind,pure,Except.pure]
  have h2 : Scalar.step ctx oracle code s2 = .ok (s3,[]) := by
    apply integer_local_step (instruction := .bin .add 64 64 "%hp" (.reg "%hp") (.reg "%h"))
      (by simpa [s2,s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simp [s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.moe_combine.program])
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s2,s1,hi.h,hi.y,hi.n,hrval,hcval,hr32,hc32,hn32,hy64,hc64,
      wrap_mul,wrap_add,wrap_add_left,wrap_add_right,hprod,hcol,hfour,haddr,yaddr,hh,hy,
      bind,Except.bind,pure,Except.pure]
  have h3 : Scalar.step ctx oracle code s3 = .ok (s4,[]) := by
    apply integer_local_step (instruction := .bin .mul 32 64 "%yp" (.reg "%row") (.reg "%n"))
      (by simpa [s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simp [s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.moe_combine.program])
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s3,s2,s1,hi.h,hi.y,hi.n,hrval,hcval,hr32,hc32,hn32,hy64,hc64,
      wrap_mul,wrap_add,wrap_add_left,wrap_add_right,hprod,hcol,hfour,haddr,yaddr,hh,hy,
      bind,Except.bind,pure,Except.pure]
  have h4 : Scalar.step ctx oracle code s4 = .ok (s5,[]) := by
    apply integer_local_step (instruction := .bin .mul 64 64 "%yp" (.reg "%yp") (.imm 4))
      (by simpa [s4,s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simp [s4,s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.moe_combine.program])
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s4,s3,s2,s1,hi.h,hi.y,hi.n,hrval,hcval,hr32,hc32,hn32,hy64,hc64,
      wrap_mul,wrap_add,wrap_add_left,wrap_add_right,hprod,hcol,hfour,haddr,yaddr,hh,hy,
      bind,Except.bind,pure,Except.pure]
  have h5 : Scalar.step ctx oracle code s5 = .ok (s6,[]) := by
    apply integer_local_step (instruction := .bin .add 64 64 "%yp" (.reg "%yp") (.reg "%y"))
      (by simpa [s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simp [s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.moe_combine.program])
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s5,s4,s3,s2,s1,hi.h,hi.y,hi.n,hrval,hcval,hr32,hc32,hn32,hy64,hc64,
      wrap_mul,wrap_add,wrap_add_left,wrap_add_right,hprod,hcol,hfour,haddr,yaddr,hh,hy,
      bind,Except.bind,pure,Except.pure]
  have h6 : Scalar.step ctx oracle code s6 = .ok (s7,[]) := by
    apply integer_local_step (instruction := .bin .mul 32 64 "%rp" (.reg "%col") (.imm 4))
      (by simpa [s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simp [s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.moe_combine.program])
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s6,s5,s4,s3,s2,s1,hi.h,hi.y,hi.n,hrval,hcval,hr32,hc32,hn32,hy64,hc64,
      wrap_mul,wrap_add,wrap_add_left,wrap_add_right,hprod,hcol,hfour,haddr,yaddr,hh,hy,
      bind,Except.bind,pure,Except.pure]
  have h7 : Scalar.step ctx oracle code s7 = .ok (s8,[]) := by
    apply integer_local_step (instruction := .bin .add 64 64 "%hp" (.reg "%hp") (.reg "%rp"))
      (by simpa [s7,s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simp [s7,s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.moe_combine.program])
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s7,s6,s5,s4,s3,s2,s1,hi.h,hi.y,hi.n,hrval,hcval,hr32,hc32,hn32,hy64,hc64,
      wrap_mul,wrap_add,wrap_add_left,wrap_add_right,hprod,hcol,hfour,haddr,yaddr,hh,hy,
      bind,Except.bind,pure,Except.pure]
  have h8 : Scalar.step ctx oracle code s8 = .ok (s9,[]) := by
    apply integer_local_step (instruction := .bin .add 64 64 "%yp" (.reg "%yp") (.reg "%rp"))
      (by simpa [s8,s7,s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simp [s8,s7,s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue,code,Generated.moe_combine.program])
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s8,s7,s6,s5,s4,s3,s2,s1,hi.h,hi.y,hi.n,hrval,hcval,hr32,hc32,hn32,hy64,hc64,
      wrap_mul,wrap_add,wrap_add_left,wrap_add_right,hprod,hcol,hfour,haddr,yaddr,hh,hy,
      bind,Except.bind,pure,Except.pure]
  have hr : Scalar.run ctx oracle code 9 s = .ok (s9,[]) := by
    simp [Scalar.run,h0,h1,h2,h3,h4,h5,h6,h7,h8,Except.bind]
  refine ⟨s9,hr,?_⟩
  constructor
  · simpa [s9,s8,s7,s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance] using hi.running
  · simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,advance,hi.pcValue]
  · exact hi.queries
  · simp [s9,s8]
  · simp [s9]
  · exact run_banks_disjoint hr hi.banks

end
end Ptx.MoeCombine
