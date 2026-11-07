import Ptx.Kernels.MoeExpertsInput

/-! Checked execution of generated PCs 0--16. Parameter bindings may contain
unrelated names; CTA/thread coordinates and dimensions are runtime inputs. -/
namespace Ptx.MoeExperts
open Ptx.ISA Ptx.Scalar Ptx.MoeExpertsLoop
noncomputable section

def indexed (i : Inputs) (ctx : Scalar.Context) : Scalar.State :=
  let s1 := intAssign {} "%x" (i.x)
  let s2 := intAssign s1 "%w" (i.w)
  let s3 := intAssign s2 "%r" i.r
  let s4 := intAssign s3 "%h" (i.h)
  let s5 := intAssign s4 "%m" (i.m)
  let s6 := intAssign s5 "%n" (i.n)
  let s7 := intAssign s6 "%kmax" (i.k)
  let s8 := intAssign s7 "%by" (ctx.id.cta.y)
  let s9 := intAssign s8 "%sy" (ctx.block.y)
  let s10 := intAssign s9 "%ty" (ctx.id.tid.y)
  let s11 := intAssign s10 "%row" (ctx.id.cta.y*ctx.block.y)
  let s12 := intAssign s11 "%row" (row ctx.block ctx.id)
  let s13 := intAssign s12 "%bx" (ctx.id.cta.x)
  let s14 := intAssign s13 "%sx" (ctx.block.x)
  let s15 := intAssign s14 "%tx" (ctx.id.tid.x)
  let s16 := intAssign s15 "%col" (ctx.id.cta.x*ctx.block.x)
  let s17 := intAssign s16 "%col" (col ctx.block ctx.id)
  s17

theorem index_run (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : IndexBounds ctx) :
    Scalar.run ctx oracle code 17 {} = .ok (indexed i ctx,[]) := by
  let s1 := intAssign {} "%x" (i.x)
  let s2 := intAssign s1 "%w" (i.w)
  let s3 := intAssign s2 "%r" i.r
  let s4 := intAssign s3 "%h" (i.h)
  let s5 := intAssign s4 "%m" (i.m)
  let s6 := intAssign s5 "%n" (i.n)
  let s7 := intAssign s6 "%kmax" (i.k)
  let s8 := intAssign s7 "%by" (ctx.id.cta.y)
  let s9 := intAssign s8 "%sy" (ctx.block.y)
  let s10 := intAssign s9 "%ty" (ctx.id.tid.y)
  let s11 := intAssign s10 "%row" (ctx.id.cta.y*ctx.block.y)
  let s12 := intAssign s11 "%row" (row ctx.block ctx.id)
  let s13 := intAssign s12 "%bx" (ctx.id.cta.x)
  let s14 := intAssign s13 "%sx" (ctx.block.x)
  let s15 := intAssign s14 "%tx" (ctx.id.tid.x)
  let s16 := intAssign s15 "%col" (ctx.id.cta.x*ctx.block.x)
  let s17 := intAssign s16 "%col" (col ctx.block ctx.id)
  have rowProduct : ctx.id.cta.y*ctx.block.y < 2^32 := by have := hb.rowBound; unfold row at this; omega
  have colProduct : ctx.id.cta.x*ctx.block.x < 2^32 := by have := hb.colBound; unfold col at this; omega
  have h0 : Scalar.step ctx oracle code {} = .ok (s1,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,hp.x,show wrap 64 (i.x) = i.x from Nat.mod_eq_of_lt i.x64,bind,Except.bind,pure,Except.pure]
  have h1 : Scalar.step ctx oracle code s1 = .ok (s2,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,s1,hp.w,show wrap 64 (i.w) = i.w from Nat.mod_eq_of_lt i.w64,bind,Except.bind,pure,Except.pure]
  have h2 : Scalar.step ctx oracle code s2 = .ok (s3,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,s2,s1,hp.r,show wrap 64 i.r = i.r from Nat.mod_eq_of_lt i.r64,bind,Except.bind,pure,Except.pure]
  have h3 : Scalar.step ctx oracle code s3 = .ok (s4,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,s3,s2,s1,hp.h,show wrap 64 (i.h) = i.h from Nat.mod_eq_of_lt i.h64,bind,Except.bind,pure,Except.pure]
  have h4 : Scalar.step ctx oracle code s4 = .ok (s5,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,s4,s2,s1,hp.m,show wrap 32 (i.m) = i.m from Nat.mod_eq_of_lt i.m32,bind,Except.bind,pure,Except.pure]
  have h5 : Scalar.step ctx oracle code s5 = .ok (s6,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,s5,s4,s2,s1,hp.n,show wrap 32 (i.n) = i.n from Nat.mod_eq_of_lt i.n32,bind,Except.bind,pure,Except.pure]
  have h6 : Scalar.step ctx oracle code s6 = .ok (s7,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,s6,s5,s4,s2,s1,hp.k,show wrap 32 (i.k) = i.k from Nat.mod_eq_of_lt i.k32,bind,Except.bind,pure,Except.pure]
  have h7 : Scalar.step ctx oracle code s7 = .ok (s8,[]) := by
    have hw : wrap 32 (ctx.id.cta.y) = ctx.id.cta.y := Nat.mod_eq_of_lt hb.byBound
    have h := Scalar.read_special_step (ctx := ctx) (oracle := oracle) (code := code)
      (s := s7) (dst := "%by") (source := .ctaid .y) rfl rfl
    simpa only [s8,intAssign,SpecialRegister.value,Axis.component,hw] using h
  have h8 : Scalar.step ctx oracle code s8 = .ok (s9,[]) := by
    have hw : wrap 32 (ctx.block.y) = ctx.block.y := Nat.mod_eq_of_lt hb.sy
    have h := Scalar.read_special_step (ctx := ctx) (oracle := oracle) (code := code)
      (s := s8) (dst := "%sy") (source := .ntid .y) rfl rfl
    simpa only [s9,intAssign,SpecialRegister.value,Axis.component,hw] using h
  have h9 : Scalar.step ctx oracle code s9 = .ok (s10,[]) := by
    have hw : wrap 32 (ctx.id.tid.y) = ctx.id.tid.y := Nat.mod_eq_of_lt hb.ty
    have h := Scalar.read_special_step (ctx := ctx) (oracle := oracle) (code := code)
      (s := s9) (dst := "%ty") (source := .tid .y) rfl rfl
    simpa only [s10,intAssign,SpecialRegister.value,Axis.component,hw] using h
  have h10 : Scalar.step ctx oracle code s10 = .ok (s11,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s10,s9,s8,s7,s6,s5,s4,s2,s1,
      show wrap 32 (ctx.id.cta.y) = ctx.id.cta.y from Nat.mod_eq_of_lt hb.byBound,
      show wrap 32 (ctx.block.y) = ctx.block.y from Nat.mod_eq_of_lt hb.sy,
      show wrap 32 (ctx.id.cta.y*ctx.block.y) = ctx.id.cta.y*ctx.block.y from Nat.mod_eq_of_lt rowProduct,
      bind,Except.bind,pure,Except.pure]
  have h11 : Scalar.step ctx oracle code s11 = .ok (s12,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s11,s10,s9,s8,s7,s6,s5,s4,s2,s1,row,
      show wrap 32 (ctx.id.cta.y*ctx.block.y) = ctx.id.cta.y*ctx.block.y from Nat.mod_eq_of_lt rowProduct,
      show wrap 32 (ctx.id.tid.y) = ctx.id.tid.y from Nat.mod_eq_of_lt hb.ty,
      show wrap 32 (ctx.id.cta.y*ctx.block.y+ctx.id.tid.y) = ctx.id.cta.y*ctx.block.y+ctx.id.tid.y from Nat.mod_eq_of_lt hb.rowBound,
      bind,Except.bind,pure,Except.pure]
  have h12 : Scalar.step ctx oracle code s12 = .ok (s13,[]) := by
    have hw : wrap 32 (ctx.id.cta.x) = ctx.id.cta.x := Nat.mod_eq_of_lt hb.bx
    have h := Scalar.read_special_step (ctx := ctx) (oracle := oracle) (code := code)
      (s := s12) (dst := "%bx") (source := .ctaid .x) rfl rfl
    simpa only [s13,intAssign,SpecialRegister.value,Axis.component,hw] using h
  have h13 : Scalar.step ctx oracle code s13 = .ok (s14,[]) := by
    have hw : wrap 32 (ctx.block.x) = ctx.block.x := Nat.mod_eq_of_lt hb.sx
    have h := Scalar.read_special_step (ctx := ctx) (oracle := oracle) (code := code)
      (s := s13) (dst := "%sx") (source := .ntid .x) rfl rfl
    simpa only [s14,intAssign,SpecialRegister.value,Axis.component,hw] using h
  have h14 : Scalar.step ctx oracle code s14 = .ok (s15,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s14,s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s2,s1,show wrap 32 (ctx.id.tid.x) = ctx.id.tid.x from Nat.mod_eq_of_lt hb.tx,bind,Except.bind,pure,Except.pure]
  have h15 : Scalar.step ctx oracle code s15 = .ok (s16,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s15,s14,s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s2,s1,
      show wrap 32 (ctx.id.cta.x) = ctx.id.cta.x from Nat.mod_eq_of_lt hb.bx,
      show wrap 32 (ctx.block.x) = ctx.block.x from Nat.mod_eq_of_lt hb.sx,
      show wrap 32 (ctx.id.cta.x*ctx.block.x) = ctx.id.cta.x*ctx.block.x from Nat.mod_eq_of_lt colProduct,
      bind,Except.bind,pure,Except.pure]
  have h16 : Scalar.step ctx oracle code s16 = .ok (s17,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s16,s15,s14,s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s2,s1,col,
      show wrap 32 (ctx.id.cta.x*ctx.block.x) = ctx.id.cta.x*ctx.block.x from Nat.mod_eq_of_lt colProduct,
      show wrap 32 (ctx.id.tid.x) = ctx.id.tid.x from Nat.mod_eq_of_lt hb.tx,
      show wrap 32 (ctx.id.cta.x*ctx.block.x+ctx.id.tid.x) = ctx.id.cta.x*ctx.block.x+ctx.id.tid.x from Nat.mod_eq_of_lt hb.colBound,
      bind,Except.bind,pure,Except.pure]
  change Scalar.run ctx oracle code 17 {} = .ok (s17,[])
  simp [Scalar.run,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,Except.bind]

end
end Ptx.MoeExperts
