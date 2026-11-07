import Ptx.Kernels.MoeCombineInput

/-! Actual PC0--14 parameter and two-dimensional index execution. -/
namespace Ptx.MoeCombine
open Ptx.ISA Ptx.Scalar
noncomputable section

def indexed (i : Inputs) (ctx : Scalar.Context) : Scalar.State :=
  let s1 := intAssign {} "%r" (i.r)
  let s2 := intAssign s1 "%h" (i.h)
  let s3 := intAssign s2 "%y" (i.y)
  let s4 := intAssign s3 "%m" (i.m)
  let s5 := intAssign s4 "%n" (i.n)
  let s6 := intAssign s5 "%by" (ctx.id.cta.y)
  let s7 := intAssign s6 "%sy" (ctx.block.y)
  let s8 := intAssign s7 "%ty" (ctx.id.tid.y)
  let s9 := intAssign s8 "%row" (ctx.id.cta.y*ctx.block.y)
  let s10 := intAssign s9 "%row" (row ctx.block ctx.id)
  let s11 := intAssign s10 "%bx" (ctx.id.cta.x)
  let s12 := intAssign s11 "%sx" (ctx.block.x)
  let s13 := intAssign s12 "%tx" (ctx.id.tid.x)
  let s14 := intAssign s13 "%col" (ctx.id.cta.x*ctx.block.x)
  let s15 := intAssign s14 "%col" (col ctx.block ctx.id)
  s15

theorem index_run (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : IndexBounds ctx) :
    Scalar.run ctx oracle code 15 {} = .ok (indexed i ctx,[]) := by
  let s1 := intAssign {} "%r" (i.r)
  let s2 := intAssign s1 "%h" (i.h)
  let s3 := intAssign s2 "%y" (i.y)
  let s4 := intAssign s3 "%m" (i.m)
  let s5 := intAssign s4 "%n" (i.n)
  let s6 := intAssign s5 "%by" (ctx.id.cta.y)
  let s7 := intAssign s6 "%sy" (ctx.block.y)
  let s8 := intAssign s7 "%ty" (ctx.id.tid.y)
  let s9 := intAssign s8 "%row" (ctx.id.cta.y*ctx.block.y)
  let s10 := intAssign s9 "%row" (row ctx.block ctx.id)
  let s11 := intAssign s10 "%bx" (ctx.id.cta.x)
  let s12 := intAssign s11 "%sx" (ctx.block.x)
  let s13 := intAssign s12 "%tx" (ctx.id.tid.x)
  let s14 := intAssign s13 "%col" (ctx.id.cta.x*ctx.block.x)
  let s15 := intAssign s14 "%col" (col ctx.block ctx.id)
  have rowProduct : ctx.id.cta.y*ctx.block.y < 2^32 := by have := hb.rowBound; unfold row at this; omega
  have colProduct : ctx.id.cta.x*ctx.block.x < 2^32 := by have := hb.colBound; unfold col at this; omega
  have h0 : Scalar.step ctx oracle code {} = .ok (s1,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,hp.r,hp.h,hp.y,hp.m,hp.n,row,col,show wrap 32 (ctx.id.cta.y) = ctx.id.cta.y from Nat.mod_eq_of_lt hb.byBound,show wrap 32 (ctx.id.cta.x) = ctx.id.cta.x from Nat.mod_eq_of_lt hb.bx,show wrap 32 (ctx.block.y) = ctx.block.y from Nat.mod_eq_of_lt hb.sy,show wrap 32 (ctx.block.x) = ctx.block.x from Nat.mod_eq_of_lt hb.sx,show wrap 32 (ctx.id.tid.x) = ctx.id.tid.x from Nat.mod_eq_of_lt hb.tx,show wrap 32 (ctx.id.tid.y) = ctx.id.tid.y from Nat.mod_eq_of_lt hb.ty,show wrap 32 (ctx.id.cta.y*ctx.block.y) = ctx.id.cta.y*ctx.block.y from Nat.mod_eq_of_lt rowProduct,show wrap 32 (ctx.id.cta.x*ctx.block.x) = ctx.id.cta.x*ctx.block.x from Nat.mod_eq_of_lt colProduct,show wrap 32 (ctx.id.cta.y*ctx.block.y+ctx.id.tid.y) = ctx.id.cta.y*ctx.block.y+ctx.id.tid.y from Nat.mod_eq_of_lt hb.rowBound,show wrap 32 (ctx.id.cta.x*ctx.block.x+ctx.id.tid.x) = ctx.id.cta.x*ctx.block.x+ctx.id.tid.x from Nat.mod_eq_of_lt hb.colBound,show wrap 64 (i.r) = i.r from Nat.mod_eq_of_lt i.r64,show wrap 64 (i.h) = i.h from Nat.mod_eq_of_lt i.h64,show wrap 64 (i.y) = i.y from Nat.mod_eq_of_lt i.y64,show wrap 32 (i.m) = i.m from Nat.mod_eq_of_lt i.m32,show wrap 32 (i.n) = i.n from Nat.mod_eq_of_lt i.n32,bind,Except.bind,pure,Except.pure]
  have h1 : Scalar.step ctx oracle code s1 = .ok (s2,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s1,hp.r,hp.h,hp.y,hp.m,hp.n,row,col,show wrap 32 (ctx.id.cta.y) = ctx.id.cta.y from Nat.mod_eq_of_lt hb.byBound,show wrap 32 (ctx.id.cta.x) = ctx.id.cta.x from Nat.mod_eq_of_lt hb.bx,show wrap 32 (ctx.block.y) = ctx.block.y from Nat.mod_eq_of_lt hb.sy,show wrap 32 (ctx.block.x) = ctx.block.x from Nat.mod_eq_of_lt hb.sx,show wrap 32 (ctx.id.tid.x) = ctx.id.tid.x from Nat.mod_eq_of_lt hb.tx,show wrap 32 (ctx.id.tid.y) = ctx.id.tid.y from Nat.mod_eq_of_lt hb.ty,show wrap 32 (ctx.id.cta.y*ctx.block.y) = ctx.id.cta.y*ctx.block.y from Nat.mod_eq_of_lt rowProduct,show wrap 32 (ctx.id.cta.x*ctx.block.x) = ctx.id.cta.x*ctx.block.x from Nat.mod_eq_of_lt colProduct,show wrap 32 (ctx.id.cta.y*ctx.block.y+ctx.id.tid.y) = ctx.id.cta.y*ctx.block.y+ctx.id.tid.y from Nat.mod_eq_of_lt hb.rowBound,show wrap 32 (ctx.id.cta.x*ctx.block.x+ctx.id.tid.x) = ctx.id.cta.x*ctx.block.x+ctx.id.tid.x from Nat.mod_eq_of_lt hb.colBound,show wrap 64 (i.r) = i.r from Nat.mod_eq_of_lt i.r64,show wrap 64 (i.h) = i.h from Nat.mod_eq_of_lt i.h64,show wrap 64 (i.y) = i.y from Nat.mod_eq_of_lt i.y64,show wrap 32 (i.m) = i.m from Nat.mod_eq_of_lt i.m32,show wrap 32 (i.n) = i.n from Nat.mod_eq_of_lt i.n32,bind,Except.bind,pure,Except.pure]
  have h2 : Scalar.step ctx oracle code s2 = .ok (s3,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s2,s1,hp.r,hp.h,hp.y,hp.m,hp.n,row,col,show wrap 32 (ctx.id.cta.y) = ctx.id.cta.y from Nat.mod_eq_of_lt hb.byBound,show wrap 32 (ctx.id.cta.x) = ctx.id.cta.x from Nat.mod_eq_of_lt hb.bx,show wrap 32 (ctx.block.y) = ctx.block.y from Nat.mod_eq_of_lt hb.sy,show wrap 32 (ctx.block.x) = ctx.block.x from Nat.mod_eq_of_lt hb.sx,show wrap 32 (ctx.id.tid.x) = ctx.id.tid.x from Nat.mod_eq_of_lt hb.tx,show wrap 32 (ctx.id.tid.y) = ctx.id.tid.y from Nat.mod_eq_of_lt hb.ty,show wrap 32 (ctx.id.cta.y*ctx.block.y) = ctx.id.cta.y*ctx.block.y from Nat.mod_eq_of_lt rowProduct,show wrap 32 (ctx.id.cta.x*ctx.block.x) = ctx.id.cta.x*ctx.block.x from Nat.mod_eq_of_lt colProduct,show wrap 32 (ctx.id.cta.y*ctx.block.y+ctx.id.tid.y) = ctx.id.cta.y*ctx.block.y+ctx.id.tid.y from Nat.mod_eq_of_lt hb.rowBound,show wrap 32 (ctx.id.cta.x*ctx.block.x+ctx.id.tid.x) = ctx.id.cta.x*ctx.block.x+ctx.id.tid.x from Nat.mod_eq_of_lt hb.colBound,show wrap 64 (i.r) = i.r from Nat.mod_eq_of_lt i.r64,show wrap 64 (i.h) = i.h from Nat.mod_eq_of_lt i.h64,show wrap 64 (i.y) = i.y from Nat.mod_eq_of_lt i.y64,show wrap 32 (i.m) = i.m from Nat.mod_eq_of_lt i.m32,show wrap 32 (i.n) = i.n from Nat.mod_eq_of_lt i.n32,bind,Except.bind,pure,Except.pure]
  have h3 : Scalar.step ctx oracle code s3 = .ok (s4,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s3,s2,s1,hp.r,hp.h,hp.y,hp.m,hp.n,row,col,show wrap 32 (ctx.id.cta.y) = ctx.id.cta.y from Nat.mod_eq_of_lt hb.byBound,show wrap 32 (ctx.id.cta.x) = ctx.id.cta.x from Nat.mod_eq_of_lt hb.bx,show wrap 32 (ctx.block.y) = ctx.block.y from Nat.mod_eq_of_lt hb.sy,show wrap 32 (ctx.block.x) = ctx.block.x from Nat.mod_eq_of_lt hb.sx,show wrap 32 (ctx.id.tid.x) = ctx.id.tid.x from Nat.mod_eq_of_lt hb.tx,show wrap 32 (ctx.id.tid.y) = ctx.id.tid.y from Nat.mod_eq_of_lt hb.ty,show wrap 32 (ctx.id.cta.y*ctx.block.y) = ctx.id.cta.y*ctx.block.y from Nat.mod_eq_of_lt rowProduct,show wrap 32 (ctx.id.cta.x*ctx.block.x) = ctx.id.cta.x*ctx.block.x from Nat.mod_eq_of_lt colProduct,show wrap 32 (ctx.id.cta.y*ctx.block.y+ctx.id.tid.y) = ctx.id.cta.y*ctx.block.y+ctx.id.tid.y from Nat.mod_eq_of_lt hb.rowBound,show wrap 32 (ctx.id.cta.x*ctx.block.x+ctx.id.tid.x) = ctx.id.cta.x*ctx.block.x+ctx.id.tid.x from Nat.mod_eq_of_lt hb.colBound,show wrap 64 (i.r) = i.r from Nat.mod_eq_of_lt i.r64,show wrap 64 (i.h) = i.h from Nat.mod_eq_of_lt i.h64,show wrap 64 (i.y) = i.y from Nat.mod_eq_of_lt i.y64,show wrap 32 (i.m) = i.m from Nat.mod_eq_of_lt i.m32,show wrap 32 (i.n) = i.n from Nat.mod_eq_of_lt i.n32,bind,Except.bind,pure,Except.pure]
  have h4 : Scalar.step ctx oracle code s4 = .ok (s5,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s4,s3,s2,s1,hp.r,hp.h,hp.y,hp.m,hp.n,row,col,show wrap 32 (ctx.id.cta.y) = ctx.id.cta.y from Nat.mod_eq_of_lt hb.byBound,show wrap 32 (ctx.id.cta.x) = ctx.id.cta.x from Nat.mod_eq_of_lt hb.bx,show wrap 32 (ctx.block.y) = ctx.block.y from Nat.mod_eq_of_lt hb.sy,show wrap 32 (ctx.block.x) = ctx.block.x from Nat.mod_eq_of_lt hb.sx,show wrap 32 (ctx.id.tid.x) = ctx.id.tid.x from Nat.mod_eq_of_lt hb.tx,show wrap 32 (ctx.id.tid.y) = ctx.id.tid.y from Nat.mod_eq_of_lt hb.ty,show wrap 32 (ctx.id.cta.y*ctx.block.y) = ctx.id.cta.y*ctx.block.y from Nat.mod_eq_of_lt rowProduct,show wrap 32 (ctx.id.cta.x*ctx.block.x) = ctx.id.cta.x*ctx.block.x from Nat.mod_eq_of_lt colProduct,show wrap 32 (ctx.id.cta.y*ctx.block.y+ctx.id.tid.y) = ctx.id.cta.y*ctx.block.y+ctx.id.tid.y from Nat.mod_eq_of_lt hb.rowBound,show wrap 32 (ctx.id.cta.x*ctx.block.x+ctx.id.tid.x) = ctx.id.cta.x*ctx.block.x+ctx.id.tid.x from Nat.mod_eq_of_lt hb.colBound,show wrap 64 (i.r) = i.r from Nat.mod_eq_of_lt i.r64,show wrap 64 (i.h) = i.h from Nat.mod_eq_of_lt i.h64,show wrap 64 (i.y) = i.y from Nat.mod_eq_of_lt i.y64,show wrap 32 (i.m) = i.m from Nat.mod_eq_of_lt i.m32,show wrap 32 (i.n) = i.n from Nat.mod_eq_of_lt i.n32,bind,Except.bind,pure,Except.pure]
  have h5 : Scalar.step ctx oracle code s5 = .ok (s6,[]) := by
    have h := Scalar.read_special_step (ctx := ctx) (oracle := oracle) (code := code)
      (s := s5) (dst := "%by") (source := .ctaid .y) rfl rfl
    simpa only [s6,intAssign,SpecialRegister.value,Axis.component,
      show wrap 32 (ctx.id.cta.y) = ctx.id.cta.y from Nat.mod_eq_of_lt hb.byBound] using h
  have h6 : Scalar.step ctx oracle code s6 = .ok (s7,[]) := by
    have h := Scalar.read_special_step (ctx := ctx) (oracle := oracle) (code := code)
      (s := s6) (dst := "%sy") (source := .ntid .y) rfl rfl
    simpa only [s7,intAssign,SpecialRegister.value,Axis.component,
      show wrap 32 (ctx.block.y) = ctx.block.y from Nat.mod_eq_of_lt hb.sy] using h
  have h7 : Scalar.step ctx oracle code s7 = .ok (s8,[]) := by
    have h := Scalar.read_special_step (ctx := ctx) (oracle := oracle) (code := code)
      (s := s7) (dst := "%ty") (source := .tid .y) rfl rfl
    simpa only [s8,intAssign,SpecialRegister.value,Axis.component,
      show wrap 32 (ctx.id.tid.y) = ctx.id.tid.y from Nat.mod_eq_of_lt hb.ty] using h
  have h8 : Scalar.step ctx oracle code s8 = .ok (s9,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s8,s7,s6,s5,s4,s3,s2,s1,hp.r,hp.h,hp.y,hp.m,hp.n,row,col,show wrap 32 (ctx.id.cta.y) = ctx.id.cta.y from Nat.mod_eq_of_lt hb.byBound,show wrap 32 (ctx.id.cta.x) = ctx.id.cta.x from Nat.mod_eq_of_lt hb.bx,show wrap 32 (ctx.block.y) = ctx.block.y from Nat.mod_eq_of_lt hb.sy,show wrap 32 (ctx.block.x) = ctx.block.x from Nat.mod_eq_of_lt hb.sx,show wrap 32 (ctx.id.tid.x) = ctx.id.tid.x from Nat.mod_eq_of_lt hb.tx,show wrap 32 (ctx.id.tid.y) = ctx.id.tid.y from Nat.mod_eq_of_lt hb.ty,show wrap 32 (ctx.id.cta.y*ctx.block.y) = ctx.id.cta.y*ctx.block.y from Nat.mod_eq_of_lt rowProduct,show wrap 32 (ctx.id.cta.x*ctx.block.x) = ctx.id.cta.x*ctx.block.x from Nat.mod_eq_of_lt colProduct,show wrap 32 (ctx.id.cta.y*ctx.block.y+ctx.id.tid.y) = ctx.id.cta.y*ctx.block.y+ctx.id.tid.y from Nat.mod_eq_of_lt hb.rowBound,show wrap 32 (ctx.id.cta.x*ctx.block.x+ctx.id.tid.x) = ctx.id.cta.x*ctx.block.x+ctx.id.tid.x from Nat.mod_eq_of_lt hb.colBound,show wrap 64 (i.r) = i.r from Nat.mod_eq_of_lt i.r64,show wrap 64 (i.h) = i.h from Nat.mod_eq_of_lt i.h64,show wrap 64 (i.y) = i.y from Nat.mod_eq_of_lt i.y64,show wrap 32 (i.m) = i.m from Nat.mod_eq_of_lt i.m32,show wrap 32 (i.n) = i.n from Nat.mod_eq_of_lt i.n32,bind,Except.bind,pure,Except.pure]
  have h9 : Scalar.step ctx oracle code s9 = .ok (s10,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s9,s8,s7,s6,s5,s4,s3,s2,s1,hp.r,hp.h,hp.y,hp.m,hp.n,row,col,show wrap 32 (ctx.id.cta.y) = ctx.id.cta.y from Nat.mod_eq_of_lt hb.byBound,show wrap 32 (ctx.id.cta.x) = ctx.id.cta.x from Nat.mod_eq_of_lt hb.bx,show wrap 32 (ctx.block.y) = ctx.block.y from Nat.mod_eq_of_lt hb.sy,show wrap 32 (ctx.block.x) = ctx.block.x from Nat.mod_eq_of_lt hb.sx,show wrap 32 (ctx.id.tid.x) = ctx.id.tid.x from Nat.mod_eq_of_lt hb.tx,show wrap 32 (ctx.id.tid.y) = ctx.id.tid.y from Nat.mod_eq_of_lt hb.ty,show wrap 32 (ctx.id.cta.y*ctx.block.y) = ctx.id.cta.y*ctx.block.y from Nat.mod_eq_of_lt rowProduct,show wrap 32 (ctx.id.cta.x*ctx.block.x) = ctx.id.cta.x*ctx.block.x from Nat.mod_eq_of_lt colProduct,show wrap 32 (ctx.id.cta.y*ctx.block.y+ctx.id.tid.y) = ctx.id.cta.y*ctx.block.y+ctx.id.tid.y from Nat.mod_eq_of_lt hb.rowBound,show wrap 32 (ctx.id.cta.x*ctx.block.x+ctx.id.tid.x) = ctx.id.cta.x*ctx.block.x+ctx.id.tid.x from Nat.mod_eq_of_lt hb.colBound,show wrap 64 (i.r) = i.r from Nat.mod_eq_of_lt i.r64,show wrap 64 (i.h) = i.h from Nat.mod_eq_of_lt i.h64,show wrap 64 (i.y) = i.y from Nat.mod_eq_of_lt i.y64,show wrap 32 (i.m) = i.m from Nat.mod_eq_of_lt i.m32,show wrap 32 (i.n) = i.n from Nat.mod_eq_of_lt i.n32,bind,Except.bind,pure,Except.pure]
  have h10 : Scalar.step ctx oracle code s10 = .ok (s11,[]) := by
    have h := Scalar.read_special_step (ctx := ctx) (oracle := oracle) (code := code)
      (s := s10) (dst := "%bx") (source := .ctaid .x) rfl rfl
    simpa only [s11,intAssign,SpecialRegister.value,Axis.component,
      show wrap 32 (ctx.id.cta.x) = ctx.id.cta.x from Nat.mod_eq_of_lt hb.bx] using h
  have h11 : Scalar.step ctx oracle code s11 = .ok (s12,[]) := by
    have h := Scalar.read_special_step (ctx := ctx) (oracle := oracle) (code := code)
      (s := s11) (dst := "%sx") (source := .ntid .x) rfl rfl
    simpa only [s12,intAssign,SpecialRegister.value,Axis.component,
      show wrap 32 (ctx.block.x) = ctx.block.x from Nat.mod_eq_of_lt hb.sx] using h
  have h12 : Scalar.step ctx oracle code s12 = .ok (s13,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,hp.r,hp.h,hp.y,hp.m,hp.n,row,col,show wrap 32 (ctx.id.cta.y) = ctx.id.cta.y from Nat.mod_eq_of_lt hb.byBound,show wrap 32 (ctx.id.cta.x) = ctx.id.cta.x from Nat.mod_eq_of_lt hb.bx,show wrap 32 (ctx.block.y) = ctx.block.y from Nat.mod_eq_of_lt hb.sy,show wrap 32 (ctx.block.x) = ctx.block.x from Nat.mod_eq_of_lt hb.sx,show wrap 32 (ctx.id.tid.x) = ctx.id.tid.x from Nat.mod_eq_of_lt hb.tx,show wrap 32 (ctx.id.tid.y) = ctx.id.tid.y from Nat.mod_eq_of_lt hb.ty,show wrap 32 (ctx.id.cta.y*ctx.block.y) = ctx.id.cta.y*ctx.block.y from Nat.mod_eq_of_lt rowProduct,show wrap 32 (ctx.id.cta.x*ctx.block.x) = ctx.id.cta.x*ctx.block.x from Nat.mod_eq_of_lt colProduct,show wrap 32 (ctx.id.cta.y*ctx.block.y+ctx.id.tid.y) = ctx.id.cta.y*ctx.block.y+ctx.id.tid.y from Nat.mod_eq_of_lt hb.rowBound,show wrap 32 (ctx.id.cta.x*ctx.block.x+ctx.id.tid.x) = ctx.id.cta.x*ctx.block.x+ctx.id.tid.x from Nat.mod_eq_of_lt hb.colBound,show wrap 64 (i.r) = i.r from Nat.mod_eq_of_lt i.r64,show wrap 64 (i.h) = i.h from Nat.mod_eq_of_lt i.h64,show wrap 64 (i.y) = i.y from Nat.mod_eq_of_lt i.y64,show wrap 32 (i.m) = i.m from Nat.mod_eq_of_lt i.m32,show wrap 32 (i.n) = i.n from Nat.mod_eq_of_lt i.n32,bind,Except.bind,pure,Except.pure]
  have h13 : Scalar.step ctx oracle code s13 = .ok (s14,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,hp.r,hp.h,hp.y,hp.m,hp.n,row,col,show wrap 32 (ctx.id.cta.y) = ctx.id.cta.y from Nat.mod_eq_of_lt hb.byBound,show wrap 32 (ctx.id.cta.x) = ctx.id.cta.x from Nat.mod_eq_of_lt hb.bx,show wrap 32 (ctx.block.y) = ctx.block.y from Nat.mod_eq_of_lt hb.sy,show wrap 32 (ctx.block.x) = ctx.block.x from Nat.mod_eq_of_lt hb.sx,show wrap 32 (ctx.id.tid.x) = ctx.id.tid.x from Nat.mod_eq_of_lt hb.tx,show wrap 32 (ctx.id.tid.y) = ctx.id.tid.y from Nat.mod_eq_of_lt hb.ty,show wrap 32 (ctx.id.cta.y*ctx.block.y) = ctx.id.cta.y*ctx.block.y from Nat.mod_eq_of_lt rowProduct,show wrap 32 (ctx.id.cta.x*ctx.block.x) = ctx.id.cta.x*ctx.block.x from Nat.mod_eq_of_lt colProduct,show wrap 32 (ctx.id.cta.y*ctx.block.y+ctx.id.tid.y) = ctx.id.cta.y*ctx.block.y+ctx.id.tid.y from Nat.mod_eq_of_lt hb.rowBound,show wrap 32 (ctx.id.cta.x*ctx.block.x+ctx.id.tid.x) = ctx.id.cta.x*ctx.block.x+ctx.id.tid.x from Nat.mod_eq_of_lt hb.colBound,show wrap 64 (i.r) = i.r from Nat.mod_eq_of_lt i.r64,show wrap 64 (i.h) = i.h from Nat.mod_eq_of_lt i.h64,show wrap 64 (i.y) = i.y from Nat.mod_eq_of_lt i.y64,show wrap 32 (i.m) = i.m from Nat.mod_eq_of_lt i.m32,show wrap 32 (i.n) = i.n from Nat.mod_eq_of_lt i.n32,bind,Except.bind,pure,Except.pure]
  have h14 : Scalar.step ctx oracle code s14 = .ok (s15,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s14,s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,hp.r,hp.h,hp.y,hp.m,hp.n,row,col,show wrap 32 (ctx.id.cta.y) = ctx.id.cta.y from Nat.mod_eq_of_lt hb.byBound,show wrap 32 (ctx.id.cta.x) = ctx.id.cta.x from Nat.mod_eq_of_lt hb.bx,show wrap 32 (ctx.block.y) = ctx.block.y from Nat.mod_eq_of_lt hb.sy,show wrap 32 (ctx.block.x) = ctx.block.x from Nat.mod_eq_of_lt hb.sx,show wrap 32 (ctx.id.tid.x) = ctx.id.tid.x from Nat.mod_eq_of_lt hb.tx,show wrap 32 (ctx.id.tid.y) = ctx.id.tid.y from Nat.mod_eq_of_lt hb.ty,show wrap 32 (ctx.id.cta.y*ctx.block.y) = ctx.id.cta.y*ctx.block.y from Nat.mod_eq_of_lt rowProduct,show wrap 32 (ctx.id.cta.x*ctx.block.x) = ctx.id.cta.x*ctx.block.x from Nat.mod_eq_of_lt colProduct,show wrap 32 (ctx.id.cta.y*ctx.block.y+ctx.id.tid.y) = ctx.id.cta.y*ctx.block.y+ctx.id.tid.y from Nat.mod_eq_of_lt hb.rowBound,show wrap 32 (ctx.id.cta.x*ctx.block.x+ctx.id.tid.x) = ctx.id.cta.x*ctx.block.x+ctx.id.tid.x from Nat.mod_eq_of_lt hb.colBound,show wrap 64 (i.r) = i.r from Nat.mod_eq_of_lt i.r64,show wrap 64 (i.h) = i.h from Nat.mod_eq_of_lt i.h64,show wrap 64 (i.y) = i.y from Nat.mod_eq_of_lt i.y64,show wrap 32 (i.m) = i.m from Nat.mod_eq_of_lt i.m32,show wrap 32 (i.n) = i.n from Nat.mod_eq_of_lt i.n32,bind,Except.bind,pure,Except.pure]
  change Scalar.run ctx oracle code 15 {} = .ok (s15,[])
  simp [Scalar.run,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,Except.bind]

end
end Ptx.MoeCombine
