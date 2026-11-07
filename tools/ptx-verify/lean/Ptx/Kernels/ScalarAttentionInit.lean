import Ptx.Kernels.ScalarAttentionInput

/-! Parameterized execution of ACTUAL generated PCs 0--17. Extra parameter
bindings are allowed. Runtime geometry uses shared checked indexing bounds. -/
namespace Ptx.ScalarAttentionInit
open Ptx.ISA Ptx.Scalar Ptx.ScalarAttention
noncomputable section

def indexed (i : Inputs) (ctx : Scalar.Context) : Scalar.State :=
  let s1 := intAssign {} "%q" (i.q)
  let s2 := intAssign s1 "%kr" (i.key)
  let s3 := intAssign s2 "%vp" (i.value)
  let s4 := intAssign s3 "%o" (i.output)
  let s5 := intAssign s4 "%sp" (i.scale)
  let s6 := intAssign s5 "%m" (i.m)
  let s7 := intAssign s6 "%n" (i.n)
  let s8 := intAssign s7 "%d" (i.dim)
  let s9 := intAssign s8 "%by" (ctx.id.cta.y)
  let s10 := intAssign s9 "%sy" (ctx.block.y)
  let s11 := intAssign s10 "%ty" (ctx.id.tid.y)
  let s12 := intAssign s11 "%row" (ctx.id.cta.y*ctx.block.y)
  let s13 := intAssign s12 "%row" (row ctx.block ctx.id)
  let s14 := intAssign s13 "%bx" (ctx.id.cta.x)
  let s15 := intAssign s14 "%sx" (ctx.block.x)
  let s16 := intAssign s15 "%tx" (ctx.id.tid.x)
  let s17 := intAssign s16 "%col" (ctx.id.cta.x*ctx.block.x)
  let s18 := intAssign s17 "%col" (col ctx.block ctx.id)
  s18

theorem index_run (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : IndexBounds ctx) :
    Scalar.run ctx oracle code 18 {} = .ok (indexed i ctx,[]) := by
  let s1 := intAssign {} "%q" (i.q)
  let s2 := intAssign s1 "%kr" (i.key)
  let s3 := intAssign s2 "%vp" (i.value)
  let s4 := intAssign s3 "%o" (i.output)
  let s5 := intAssign s4 "%sp" (i.scale)
  let s6 := intAssign s5 "%m" (i.m)
  let s7 := intAssign s6 "%n" (i.n)
  let s8 := intAssign s7 "%d" (i.dim)
  let s9 := intAssign s8 "%by" (ctx.id.cta.y)
  let s10 := intAssign s9 "%sy" (ctx.block.y)
  let s11 := intAssign s10 "%ty" (ctx.id.tid.y)
  let s12 := intAssign s11 "%row" (ctx.id.cta.y*ctx.block.y)
  let s13 := intAssign s12 "%row" (row ctx.block ctx.id)
  let s14 := intAssign s13 "%bx" (ctx.id.cta.x)
  let s15 := intAssign s14 "%sx" (ctx.block.x)
  let s16 := intAssign s15 "%tx" (ctx.id.tid.x)
  let s17 := intAssign s16 "%col" (ctx.id.cta.x*ctx.block.x)
  let s18 := intAssign s17 "%col" (col ctx.block ctx.id)
  have rowProduct : ctx.id.cta.y*ctx.block.y < 2^32 := by have := hb.rowBound; unfold row at this; omega
  have colProduct : ctx.id.cta.x*ctx.block.x < 2^32 := by have := hb.colBound; unfold col at this; omega
  have h0 : Scalar.step ctx oracle code {} = .ok (s1,[]) := by
    apply Scalar.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,
      hp.q,
      show wrap 64 (i.q) = i.q from Nat.mod_eq_of_lt i.q64,
      bind,
      Except.bind,
      pure,
      Except.pure]
  have h1 : Scalar.step ctx oracle code s1 = .ok (s2,[]) := by
    apply Scalar.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,
      s1,
      hp.key,
      show wrap 64 (i.key) = i.key from Nat.mod_eq_of_lt i.key64,
      bind,
      Except.bind,
      pure,
      Except.pure]
  have h2 : Scalar.step ctx oracle code s2 = .ok (s3,[]) := by
    apply Scalar.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,
      s2,s1,
      hp.value,
      show wrap 64 (i.value) = i.value from Nat.mod_eq_of_lt i.value64,
      bind,
      Except.bind,
      pure,
      Except.pure]
  have h3 : Scalar.step ctx oracle code s3 = .ok (s4,[]) := by
    apply Scalar.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,
      s3,s2,s1,
      hp.output,
      show wrap 64 (i.output) = i.output from Nat.mod_eq_of_lt i.output64,
      bind,
      Except.bind,
      pure,
      Except.pure]
  have h4 : Scalar.step ctx oracle code s4 = .ok (s5,[]) := by
    apply Scalar.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,
      s4,s3,s2,s1,
      hp.scale,
      show wrap 64 (i.scale) = i.scale from Nat.mod_eq_of_lt i.scale64,
      bind,
      Except.bind,
      pure,
      Except.pure]
  have h5 : Scalar.step ctx oracle code s5 = .ok (s6,[]) := by
    apply Scalar.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,
      s5,s4,s3,s2,s1,
      hp.m,
      show wrap 32 (i.m) = i.m from Nat.mod_eq_of_lt i.m32,
      bind,
      Except.bind,
      pure,
      Except.pure]
  have h6 : Scalar.step ctx oracle code s6 = .ok (s7,[]) := by
    apply Scalar.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,
      s6,s5,s4,s3,s2,s1,
      hp.n,
      show wrap 32 (i.n) = i.n from Nat.mod_eq_of_lt i.n32,
      bind,
      Except.bind,
      pure,
      Except.pure]
  have h7 : Scalar.step ctx oracle code s7 = .ok (s8,[]) := by
    apply Scalar.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,
      s7,s6,s5,s4,s3,s2,s1,
      hp.dim,
      show wrap 32 (i.dim) = i.dim from Nat.mod_eq_of_lt i.dim32,
      bind,
      Except.bind,
      pure,
      Except.pure]
  have h8 : Scalar.step ctx oracle code s8 = .ok (s9,[]) := by
    have hw : wrap 32 (ctx.id.cta.y) = ctx.id.cta.y := Nat.mod_eq_of_lt hb.byBound
    have hs := Scalar.read_special_step (ctx := ctx) (oracle := oracle) (code := code)
      (s := s8) (dst := "%by") (source := .ctaid .y) rfl rfl
    simpa only [s9,intAssign,SpecialRegister.value,Axis.component,hw] using hs
  have h9 : Scalar.step ctx oracle code s9 = .ok (s10,[]) := by
    have hw : wrap 32 (ctx.block.y) = ctx.block.y := Nat.mod_eq_of_lt hb.sy
    have hs := Scalar.read_special_step (ctx := ctx) (oracle := oracle) (code := code)
      (s := s9) (dst := "%sy") (source := .ntid .y) rfl rfl
    simpa only [s10,intAssign,SpecialRegister.value,Axis.component,hw] using hs
  have h10 : Scalar.step ctx oracle code s10 = .ok (s11,[]) := by
    have hw : wrap 32 (ctx.id.tid.y) = ctx.id.tid.y := Nat.mod_eq_of_lt hb.ty
    have hs := Scalar.read_special_step (ctx := ctx) (oracle := oracle) (code := code)
      (s := s10) (dst := "%ty") (source := .tid .y) rfl rfl
    simpa only [s11,intAssign,SpecialRegister.value,Axis.component,hw] using hs
  have h11 : Scalar.step ctx oracle code s11 = .ok (s12,[]) := by
    apply Scalar.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,
      s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,
      Ptx.eval,
      show wrap 32 (ctx.id.cta.y) = ctx.id.cta.y from Nat.mod_eq_of_lt hb.byBound,
      show wrap 32 (ctx.block.y) = ctx.block.y from Nat.mod_eq_of_lt hb.sy,
      show wrap 32 (ctx.id.cta.y*ctx.block.y) = ctx.id.cta.y*ctx.block.y from Nat.mod_eq_of_lt rowProduct,
      bind,
      Except.bind,
      pure,
      Except.pure]
  have h12 : Scalar.step ctx oracle code s12 = .ok (s13,[]) := by
    apply Scalar.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,
      s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,
      Ptx.eval,
      show wrap 32 (ctx.id.cta.y) = ctx.id.cta.y from Nat.mod_eq_of_lt hb.byBound,
      show wrap 32 (ctx.block.y) = ctx.block.y from Nat.mod_eq_of_lt hb.sy,
      show wrap 32 (ctx.id.cta.y*ctx.block.y) = ctx.id.cta.y*ctx.block.y from Nat.mod_eq_of_lt rowProduct,
      row,
      show wrap 32 (ctx.id.tid.y) = ctx.id.tid.y from Nat.mod_eq_of_lt hb.ty,
      show wrap 32 (ctx.id.cta.y*ctx.block.y+ctx.id.tid.y) = ctx.id.cta.y*ctx.block.y+ctx.id.tid.y from Nat.mod_eq_of_lt hb.rowBound,
      bind,
      Except.bind,
      pure,
      Except.pure]
  have h13 : Scalar.step ctx oracle code s13 = .ok (s14,[]) := by
    have hw : wrap 32 (ctx.id.cta.x) = ctx.id.cta.x := Nat.mod_eq_of_lt hb.bx
    have hs := Scalar.read_special_step (ctx := ctx) (oracle := oracle) (code := code)
      (s := s13) (dst := "%bx") (source := .ctaid .x) rfl rfl
    simpa only [s14,intAssign,SpecialRegister.value,Axis.component,hw] using hs
  have h14 : Scalar.step ctx oracle code s14 = .ok (s15,[]) := by
    have hw : wrap 32 (ctx.block.x) = ctx.block.x := Nat.mod_eq_of_lt hb.sx
    have hs := Scalar.read_special_step (ctx := ctx) (oracle := oracle) (code := code)
      (s := s14) (dst := "%sx") (source := .ntid .x) rfl rfl
    simpa only [s15,intAssign,SpecialRegister.value,Axis.component,hw] using hs
  have h15 : Scalar.step ctx oracle code s15 = .ok (s16,[]) := by
    apply Scalar.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,
      s15,s14,s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,
      Ptx.eval,
      show wrap 32 (ctx.id.tid.x) = ctx.id.tid.x from Nat.mod_eq_of_lt hb.tx,
      bind,
      Except.bind,
      pure,
      Except.pure]
  have h16 : Scalar.step ctx oracle code s16 = .ok (s17,[]) := by
    apply Scalar.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,
      s16,s15,s14,s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,
      Ptx.eval,
      show wrap 32 (ctx.id.cta.x) = ctx.id.cta.x from Nat.mod_eq_of_lt hb.bx,
      show wrap 32 (ctx.block.x) = ctx.block.x from Nat.mod_eq_of_lt hb.sx,
      show wrap 32 (ctx.id.cta.x*ctx.block.x) = ctx.id.cta.x*ctx.block.x from Nat.mod_eq_of_lt colProduct,
      bind,
      Except.bind,
      pure,
      Except.pure]
  have h17 : Scalar.step ctx oracle code s17 = .ok (s18,[]) := by
    apply Scalar.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,
      s17,s16,s15,s14,s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,
      Ptx.eval,
      show wrap 32 (ctx.id.cta.x) = ctx.id.cta.x from Nat.mod_eq_of_lt hb.bx,
      show wrap 32 (ctx.block.x) = ctx.block.x from Nat.mod_eq_of_lt hb.sx,
      show wrap 32 (ctx.id.cta.x*ctx.block.x) = ctx.id.cta.x*ctx.block.x from Nat.mod_eq_of_lt colProduct,
      col,
      show wrap 32 (ctx.id.tid.x) = ctx.id.tid.x from Nat.mod_eq_of_lt hb.tx,
      show wrap 32 (ctx.id.cta.x*ctx.block.x+ctx.id.tid.x) = ctx.id.cta.x*ctx.block.x+ctx.id.tid.x from Nat.mod_eq_of_lt hb.colBound,
      bind,
      Except.bind,
      pure,
      Except.pure]
  change Scalar.run ctx oracle code 18 {} = .ok (s18,[])
  simp [Scalar.run,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,Except.bind]

end
end Ptx.ScalarAttentionInit
