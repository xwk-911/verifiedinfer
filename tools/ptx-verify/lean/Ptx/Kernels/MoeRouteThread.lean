import Ptx.Kernels.MoeRouteSelect
import Ptx.Scalar.Control
import Ptx.Scalar.Indexing
import Ptx.Scalar.Replies

/-! Actual routing source from PC=0. Local arbitrary typed replies are kept
separate from represented gate memory and launch-wide consistency obligations. -/
namespace Ptx.MoeRouteThread
open Ptx.ISA Ptx.Scalar
noncomputable section
abbrev code := Generated.moe_route.program
structure Inputs where
  g : Nat
  r : Nat
  m : Nat
  g64 : g < 2^64
  r64 : r < 2^64
  m32 : m < 2^32
structure Params (i : Inputs) (params : Bindings) : Prop where
  g : lookup "G" params = some i.g
  r : lookup "R" params = some i.r
  m : lookup "M" params = some i.m
structure Bounds (ctx : Scalar.Context) : Prop where
  bx : ctx.id.cta.x < 2^32
  sx : ctx.block.x < 2^32
  tx : ctx.id.tid.x < 2^32
  index : col ctx.block ctx.id < 2^32

def indexed (i : Inputs) (ctx : Scalar.Context) : Scalar.State :=
  let s1 := intAssign {} "%g" (i.g)
  let s2 := intAssign s1 "%r" (i.r)
  let s3 := intAssign s2 "%m" (i.m)
  let s4 := intAssign s3 "%bx" (ctx.id.cta.x)
  let s5 := intAssign s4 "%sx" (ctx.block.x)
  let s6 := intAssign s5 "%tx" (ctx.id.tid.x)
  let s7 := intAssign s6 "%row" (ctx.id.cta.x*ctx.block.x)
  let s8 := intAssign s7 "%row" (col ctx.block ctx.id)
  s8

theorem index_run (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : Bounds ctx) :
    Scalar.run ctx oracle code 8 {} = .ok (indexed i ctx,[]) := by
  let s1 := intAssign {} "%g" (i.g)
  let s2 := intAssign s1 "%r" (i.r)
  let s3 := intAssign s2 "%m" (i.m)
  let s4 := intAssign s3 "%bx" (ctx.id.cta.x)
  let s5 := intAssign s4 "%sx" (ctx.block.x)
  let s6 := intAssign s5 "%tx" (ctx.id.tid.x)
  let s7 := intAssign s6 "%row" (ctx.id.cta.x*ctx.block.x)
  let s8 := intAssign s7 "%row" (col ctx.block ctx.id)
  have product : ctx.id.cta.x*ctx.block.x < 2^32 := by have := hb.index; unfold col at this; omega
  have h0 : Scalar.step ctx oracle code {} = .ok (s1,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,
      Ptx.eval,
      hp.g,
      show wrap 64 i.g = i.g from Nat.mod_eq_of_lt i.g64,
      bind,
      Except.bind,
      pure,
      Except.pure]
  have h1 : Scalar.step ctx oracle code s1 = .ok (s2,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,
      Ptx.eval,
      s1,
      hp.r,
      show wrap 64 i.r = i.r from Nat.mod_eq_of_lt i.r64,
      bind,
      Except.bind,
      pure,
      Except.pure]
  have h2 : Scalar.step ctx oracle code s2 = .ok (s3,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,
      Ptx.eval,
      s2,
      s1,
      hp.m,
      show wrap 32 i.m = i.m from Nat.mod_eq_of_lt i.m32,
      bind,
      Except.bind,
      pure,
      Except.pure]
  have h3 : Scalar.step ctx oracle code s3 = .ok (s4,[]) := by
    have h := Scalar.read_special_step (ctx := ctx) (oracle := oracle) (code := code)
      (s := s3) (dst := "%bx") (source := .ctaid .x) rfl rfl
    simpa only [s4,intAssign,SpecialRegister.value,Axis.component,
      show wrap 32 (ctx.id.cta.x) = ctx.id.cta.x from Nat.mod_eq_of_lt hb.bx] using h
  have h4 : Scalar.step ctx oracle code s4 = .ok (s5,[]) := by
    have h := Scalar.read_special_step (ctx := ctx) (oracle := oracle) (code := code)
      (s := s4) (dst := "%sx") (source := .ntid .x) rfl rfl
    simpa only [s5,intAssign,SpecialRegister.value,Axis.component,
      show wrap 32 (ctx.block.x) = ctx.block.x from Nat.mod_eq_of_lt hb.sx] using h
  have h5 : Scalar.step ctx oracle code s5 = .ok (s6,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,
      Ptx.eval,
      s5,
      s4,
      s3,
      s2,
      s1,
      show wrap 32 ctx.id.tid.x = ctx.id.tid.x from Nat.mod_eq_of_lt hb.tx,
      bind,
      Except.bind,
      pure,
      Except.pure]
  have h6 : Scalar.step ctx oracle code s6 = .ok (s7,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,
      Ptx.eval,
      s6,
      s5,
      s4,
      s3,
      s2,
      s1,
      show wrap 32 ctx.id.cta.x = ctx.id.cta.x from Nat.mod_eq_of_lt hb.bx,
      show wrap 32 ctx.block.x = ctx.block.x from Nat.mod_eq_of_lt hb.sx,
      show wrap 32 (ctx.id.cta.x*ctx.block.x) = ctx.id.cta.x*ctx.block.x from Nat.mod_eq_of_lt product,
      bind,
      Except.bind,
      pure,
      Except.pure]
  have h7 : Scalar.step ctx oracle code s7 = .ok (s8,[]) := by
    apply Scalar.integer_local_step (by rfl) (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,
      Ptx.eval,
      s7,
      s6,
      s5,
      s4,
      s3,
      s2,
      s1,
      col,
      show wrap 32 (ctx.id.cta.x*ctx.block.x) = ctx.id.cta.x*ctx.block.x from Nat.mod_eq_of_lt product,
      show wrap 32 ctx.id.tid.x = ctx.id.tid.x from Nat.mod_eq_of_lt hb.tx,
      show wrap 32 (ctx.id.cta.x*ctx.block.x+ctx.id.tid.x) = ctx.id.cta.x*ctx.block.x+ctx.id.tid.x from Nat.mod_eq_of_lt hb.index,
      bind,
      Except.bind,
      pure,
      Except.pure]
  change Scalar.run ctx oracle code 8 {} = .ok (s8,[])
  simp [Scalar.run,h0,h1,h2,h3,h4,h5,h6,h7,Except.bind]

def guarded (i : Inputs) (ctx : Scalar.Context) : Scalar.State :=
  intPC (intAssign (indexed i ctx) "%p" (if col ctx.block ctx.id ≥ i.m then 1 else 0))
    (if col ctx.block ctx.id ≥ i.m then 22 else 10)
theorem guard_run (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) (hb : Bounds ctx) :
    Scalar.run ctx oracle code 2 (indexed i ctx) = .ok (guarded i ctx,[]) := by
  exact ge_branch_run rfl rfl rfl (by simp [indexed]) (by simp [indexed]) hb.index i.m32

def beforeGates (i : Inputs) (ctx : Scalar.Context) : Scalar.State :=
  let s := guarded i ctx
  let s1 := intAssign s "%gp" (8*col ctx.block ctx.id)
  let s2 := intAssign s1 "%gp" (i.g+8*col ctx.block ctx.id)
  let s3 := intAssign s2 "%rp" (4*col ctx.block ctx.id)
  intAssign s3 "%rp" (i.r+4*col ctx.block ctx.id)

theorem addresses_run (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) (hb : Bounds ctx)
    (ha : col ctx.block ctx.id < i.m)
    (hg : i.g+8*col ctx.block ctx.id+8 ≤ 2^64) (hr : i.r+4*col ctx.block ctx.id+4 ≤ 2^64) :
    Scalar.run ctx oracle code 4 (guarded i ctx) = .ok (beforeGates i ctx,[]) := by
  let s := guarded i ctx
  let s1 := intAssign s "%gp" (8*col ctx.block ctx.id)
  let s2 := intAssign s1 "%gp" (i.g+8*col ctx.block ctx.id)
  let s3 := intAssign s2 "%rp" (4*col ctx.block ctx.id)
  let s4 := intAssign s3 "%rp" (i.r+4*col ctx.block ctx.id)
  have hnot : ¬ col ctx.block ctx.id ≥ i.m := by omega
  have hidx := hb.index
  have hidx32 : wrap 32 (col ctx.block ctx.id) = col ctx.block ctx.id := Nat.mod_eq_of_lt hidx
  have hg64 : wrap 64 (i.g+8*col ctx.block ctx.id) = i.g+8*col ctx.block ctx.id := Nat.mod_eq_of_lt (by omega)
  have hr64 : wrap 64 (i.r+4*col ctx.block ctx.id) = i.r+4*col ctx.block ctx.id := Nat.mod_eq_of_lt (by omega)
  have hwide8 : wrap 64 (8*col ctx.block ctx.id) = 8*col ctx.block ctx.id := Nat.mod_eq_of_lt (by omega)
  have hwide4 : wrap 64 (4*col ctx.block ctx.id) = 4*col ctx.block ctx.id := Nat.mod_eq_of_lt (by omega)
  have hg0 : wrap 64 i.g = i.g := Nat.mod_eq_of_lt i.g64
  have hr0 : wrap 64 i.r = i.r := Nat.mod_eq_of_lt i.r64
  have hc8 : wrap 32 8 = 8 := by decide
  have hc4 : wrap 32 4 = 4 := by decide
  have h0 : Scalar.step ctx oracle code s = .ok (s1,[]) := by
    apply Scalar.integer_local_step (instruction := .bin .mul 32 64 "%gp" (.reg "%row") (.imm 8)) (by simp [s,guarded,indexed,intPC,intAssign,finishInteger,assign,advance,hnot,hidx32,hg64,hr64,hwide8,hwide4,hg0,hr0,hc8,hc4,Nat.mul_comm])
      (by simp [code,Generated.moe_route.program,s,guarded,indexed,intPC,intAssign,finishInteger,assign,advance,hnot,hidx32,hg64,hr64,hwide8,hwide4,hg0,hr0,hc8,hc4,Nat.mul_comm]) rfl (by intro bid h; cases h)
    norm_num [localStep,Ptx.eval,s,guarded,indexed,intPC,intAssign,finishInteger,assign,advance,hnot,hidx32,hg64,hr64,hwide8,hwide4,hg0,hr0,hc8,hc4,Nat.mul_comm,bind,Except.bind,pure,Except.pure]
  have h1 : Scalar.step ctx oracle code s1 = .ok (s2,[]) := by
    apply Scalar.integer_local_step (instruction := .bin .add 64 64 "%gp" (.reg "%g") (.reg "%gp")) (by simp [s1,s,guarded,indexed,intPC,intAssign,finishInteger,assign,advance,hnot,hidx32,hg64,hr64,hwide8,hwide4,hg0,hr0,hc8,hc4,Nat.mul_comm])
      (by simp [code,Generated.moe_route.program,s1,s,guarded,indexed,intPC,intAssign,finishInteger,assign,advance,hnot,hidx32,hg64,hr64,hwide8,hwide4,hg0,hr0,hc8,hc4,Nat.mul_comm]) rfl (by intro bid h; cases h)
    norm_num [localStep,Ptx.eval,s1,s,guarded,indexed,intPC,intAssign,finishInteger,assign,advance,hnot,hidx32,hg64,hr64,hwide8,hwide4,hg0,hr0,hc8,hc4,Nat.mul_comm,bind,Except.bind,pure,Except.pure]
  have h2 : Scalar.step ctx oracle code s2 = .ok (s3,[]) := by
    apply Scalar.integer_local_step (instruction := .bin .mul 32 64 "%rp" (.reg "%row") (.imm 4)) (by simp [s2,s1,s,guarded,indexed,intPC,intAssign,finishInteger,assign,advance,hnot,hidx32,hg64,hr64,hwide8,hwide4,hg0,hr0,hc8,hc4,Nat.mul_comm])
      (by simp [code,Generated.moe_route.program,s2,s1,s,guarded,indexed,intPC,intAssign,finishInteger,assign,advance,hnot,hidx32,hg64,hr64,hwide8,hwide4,hg0,hr0,hc8,hc4,Nat.mul_comm]) rfl (by intro bid h; cases h)
    norm_num [localStep,Ptx.eval,s2,s1,s,guarded,indexed,intPC,intAssign,finishInteger,assign,advance,hnot,hidx32,hg64,hr64,hwide8,hwide4,hg0,hr0,hc8,hc4,Nat.mul_comm,bind,Except.bind,pure,Except.pure]
  have h3 : Scalar.step ctx oracle code s3 = .ok (s4,[]) := by
    apply Scalar.integer_local_step (instruction := .bin .add 64 64 "%rp" (.reg "%r") (.reg "%rp")) (by simp [s3,s2,s1,s,guarded,indexed,intPC,intAssign,finishInteger,assign,advance,hnot,hidx32,hg64,hr64,hwide8,hwide4,hg0,hr0,hc8,hc4,Nat.mul_comm])
      (by simp [code,Generated.moe_route.program,s3,s2,s1,s,guarded,indexed,intPC,intAssign,finishInteger,assign,advance,hnot,hidx32,hg64,hr64,hwide8,hwide4,hg0,hr0,hc8,hc4,Nat.mul_comm]) rfl (by intro bid h; cases h)
    norm_num [localStep,Ptx.eval,s3,s2,s1,s,guarded,indexed,intPC,intAssign,finishInteger,assign,advance,hnot,hidx32,hg64,hr64,hwide8,hwide4,hg0,hr0,hc8,hc4,Nat.mul_comm,bind,Except.bind,pure,Except.pure]
  change Scalar.run ctx oracle code 4 s = .ok (s4,[])
  simp [Scalar.run,h0,h1,h2,h3,Except.bind]


theorem entry_run (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : Bounds ctx) (ha : col ctx.block ctx.id < i.m)
    (hg : i.g+8*col ctx.block ctx.id+8 ≤ 2^64) (hr : i.r+4*col ctx.block ctx.id+4 ≤ 2^64) :
    Scalar.run ctx oracle code 14 {} = .ok (beforeGates i ctx,[]) := by
  have h := run_append (run_append (index_run i ctx oracle hp hb) (guard_run i ctx oracle hb))
    (addresses_run i ctx oracle hb ha hg hr)
  simpa using h

def loaded (i : Inputs) (ctx : Scalar.Context) (a b : ℝ) : Scalar.State :=
  loadedFloat (loadedFloat (beforeGates i ctx) "%g0" a) "%g1" b

def reads (i : Inputs) (ctx : Scalar.Context) (a b : ℝ) : List Scalar.Kind := [
  .read ⟨.global,i.g+8*col ctx.block ctx.id⟩ (Symbolic.encode .f32 a),
  .read ⟨.global,i.g+8*col ctx.block ctx.id+4⟩ (Symbolic.encode .f32 b)]

theorem first_load (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) (a : ℝ)
    (ha : col ctx.block ctx.id < i.m) (hg : i.g+8*col ctx.block ctx.id+8 ≤ 2^64)
    (ho : oracle 0 = .real .f32 a) :
    Scalar.step ctx oracle code (beforeGates i ctx) =
      .ok (loadedFloat (beforeGates i ctx) "%g0" a,
        [.read ⟨.global,i.g+8*col ctx.block ctx.id⟩ (Symbolic.encode .f32 a)]) := by
  have hnot : ¬ col ctx.block ctx.id ≥ i.m := by omega
  apply load_step (format := .f32) (space := .global) (dst := "%g0")
    (address := {base := .reg "%gp"}) (addr := i.g+8*col ctx.block ctx.id) (value := a)
  · rfl
  · simp [beforeGates,guarded,intAssign,intPC,finishInteger,assign,advance,hnot,code,Generated.moe_route.program]
  · simp [evalAddr,Ptx.eval,beforeGates,
      show wrap 64 (i.g+8*col ctx.block ctx.id) = i.g+8*col ctx.block ctx.id from Nat.mod_eq_of_lt (by omega)]
  · exact ho

theorem second_load (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) (a b : ℝ)
    (ha : col ctx.block ctx.id < i.m) (hg : i.g+8*col ctx.block ctx.id+8 ≤ 2^64)
    (ho : oracle 1 = .real .f32 b) :
    Scalar.step ctx oracle code (loadedFloat (beforeGates i ctx) "%g0" a) =
      .ok (loaded i ctx a b,[.read ⟨.global,i.g+8*col ctx.block ctx.id+4⟩ (Symbolic.encode .f32 b)]) := by
  have hnot : ¬ col ctx.block ctx.id ≥ i.m := by omega
  apply load_step (format := .f32) (space := .global) (dst := "%g1")
    (address := {base := .reg "%gp",offset := 4}) (addr := i.g+8*col ctx.block ctx.id+4) (value := b)
  · rfl
  · simp [loadedFloat,writeFloat,beforeGates,guarded,intAssign,intPC,finishInteger,assign,advance,hnot,code,Generated.moe_route.program]
  · simp [evalAddr,Ptx.eval,beforeGates,
      show wrap 64 (i.g+8*col ctx.block ctx.id+4) = i.g+8*col ctx.block ctx.id+4 from Nat.mod_eq_of_lt (by omega)]
  · exact ho

theorem loads_run (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) (a b : ℝ)
    (ha : col ctx.block ctx.id < i.m) (hg : i.g+8*col ctx.block ctx.id+8 ≤ 2^64)
    (h0 : oracle 0 = .real .f32 a) (h1 : oracle 1 = .real .f32 b) :
    Scalar.run ctx oracle code 2 (beforeGates i ctx) = .ok (loaded i ctx a b,reads i ctx a b) := by
  simp [Scalar.run,first_load i ctx oracle a ha hg h0,second_load i ctx oracle a b ha hg h1,Except.bind,reads]

theorem selection_ready (i : Inputs) (ctx : Scalar.Context) (gates : Moe.Matrix)
    (ha : col ctx.block ctx.id < i.m) :
    MoeRouteSelect.Ready gates (col ctx.block ctx.id) (i.r+4*col ctx.block ctx.id)
      (loaded i ctx (gates (col ctx.block ctx.id) 0) (gates (col ctx.block ctx.id) 1)) := by
  have hnot : ¬ col ctx.block ctx.id ≥ i.m := by omega
  constructor
  · rfl
  · simp [loaded,loadedFloat,writeFloat,beforeGates,guarded,intAssign,intPC,finishInteger,assign,advance,hnot]
  · simp [loaded,beforeGates]
  · simp [loaded]
  · simp [loaded]

theorem active_run (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) (gates : Moe.Matrix)
    (hp : Params i ctx.params) (hb : Bounds ctx) (ha : col ctx.block ctx.id < i.m)
    (hg : i.g+8*col ctx.block ctx.id+8 ≤ 2^64) (hr : i.r+4*col ctx.block ctx.id+4 ≤ 2^64)
    (h0 : oracle 0 = .real .f32 (gates (col ctx.block ctx.id) 0))
    (h1 : oracle 1 = .real .f32 (gates (col ctx.block ctx.id) 1)) :
    Scalar.run ctx oracle code 22 {} = .ok
      (MoeRouteSelect.final (loaded i ctx (gates (col ctx.block ctx.id) 0) (gates (col ctx.block ctx.id) 1))
        (Moe.selected gates (col ctx.block ctx.id)),
       reads i ctx (gates (col ctx.block ctx.id) 0) (gates (col ctx.block ctx.id) 1) ++
        [.write ⟨.global,i.r+4*col ctx.block ctx.id⟩ (u32Bytes (Moe.selected gates (col ctx.block ctx.id)))]) := by
  have h := run_append (run_append (entry_run i ctx oracle hp hb ha hg hr) (loads_run i ctx oracle _ _ ha hg h0 h1))
    (MoeRouteSelect.complete_suffix ctx oracle gates (col ctx.block ctx.id) _ (selection_ready i ctx gates ha) (by omega))
  simpa [code,MoeRouteSelect.code] using h

def maskedFinal (i : Inputs) (ctx : Scalar.Context) : Scalar.State :=
  let s := guarded i ctx
  finishInteger s {s.core with thread := {s.core.thread with status := .done}}

theorem masked_run (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : Bounds ctx) (hm : i.m ≤ col ctx.block ctx.id) :
    Scalar.run ctx oracle code 11 {} = .ok (maskedFinal i ctx,[]) := by
  have hret : Scalar.step ctx oracle code (guarded i ctx) = .ok (maskedFinal i ctx,[]) := by
    apply integer_local_step (instruction := .ret) rfl
      (by simp [guarded,intPC,finishInteger,hm,code,Generated.moe_route.program]) rfl (by intro bid h; cases h) rfl
  have h := run_append (run_append (index_run i ctx oracle hp hb) (guard_run i ctx oracle hb))
    (show Scalar.run ctx oracle code 1 (guarded i ctx) = .ok (maskedFinal i ctx,[]) by simp [Scalar.run,hret,Except.bind])
  simpa using h


theorem completed_gate_replies (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : Bounds ctx) (ha : col ctx.block ctx.id < i.m)
    (hg : i.g+8*col ctx.block ctx.id+8 ≤ 2^64) (hr : i.r+4*col ctx.block ctx.id+4 ≤ 2^64)
    {n last events} (hn : Scalar.run ctx oracle code n {} = .ok (last,events))
    (hd : last.core.thread.status = .done) :
    ∃ a b, oracle 0 = .real .f32 a ∧ oracle 1 = .real .f32 b := by
  have hnot : ¬ col ctx.block ctx.id ≥ i.m := by omega
  have hentry := entry_run i ctx oracle hp hb ha hg hr
  obtain ⟨mid,emitted,hstep⟩ := step_after_running_prefix hn hd hentry (by rfl)
  obtain ⟨a,hfirst⟩ := real_reply_of_successful_load (by rfl : (beforeGates i ctx).core.thread.status = .running)
    (show code[(beforeGates i ctx).core.thread.pc]? = some (.load .f32 .global "%g0" {base := .reg "%gp"}) by
      simp [code,Generated.moe_route.program,beforeGates,guarded,intAssign,intPC,finishInteger,assign,advance,hnot]) hstep
  have h0 : oracle 0 = .real .f32 a := hfirst
  have pre15 := run_append hentry
    (show Scalar.run ctx oracle code 1 (beforeGates i ctx) = .ok
      (loadedFloat (beforeGates i ctx) "%g0" a,
        [.read ⟨.global,i.g+8*col ctx.block ctx.id⟩ (Symbolic.encode .f32 a)]) by
      simp [Scalar.run,first_load i ctx oracle a ha hg h0,Except.bind])
  obtain ⟨mid2,emitted2,hstep2⟩ := step_after_running_prefix hn hd pre15 (by rfl)
  obtain ⟨b,hsecond⟩ := real_reply_of_successful_load
    (by rfl : (loadedFloat (beforeGates i ctx) "%g0" a).core.thread.status = .running)
    (show code[(loadedFloat (beforeGates i ctx) "%g0" a).core.thread.pc]? =
      some (.load .f32 .global "%g1" {base := .reg "%gp",offset := 4}) by
      simp [code,Generated.moe_route.program,loadedFloat,writeFloat,beforeGates,guarded,intAssign,intPC,finishInteger,assign,advance,hnot]) hstep2
  exact ⟨a,b,h0,hsecond⟩

theorem reconstruct_active (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : Bounds ctx) (ha : col ctx.block ctx.id < i.m)
    (hg : i.g+8*col ctx.block ctx.id+8 ≤ 2^64) (hr : i.r+4*col ctx.block ctx.id+4 ≤ 2^64)
    {n last events} (hn : Scalar.run ctx oracle code n {} = .ok (last,events))
    (hd : last.core.thread.status = .done) :
    ∃ a b, oracle 0 = .real .f32 a ∧ oracle 1 = .real .f32 b ∧ n = 22 ∧
      events = reads i ctx a b ++ [.write ⟨.global,i.r+4*col ctx.block ctx.id⟩ (u32Bytes (gtFlag b a))] := by
  obtain ⟨a,b,h0,h1⟩ := completed_gate_replies i ctx oracle hp hb ha hg hr hn hd
  let gates : Moe.Matrix := fun _ which => if which = 0 then a else b
  have h := active_run i ctx oracle gates hp hb ha hg hr (by simpa [gates] using h0) (by simpa [gates] using h1)
  obtain ⟨count,_,trace⟩ := complete_run_unique hn hd h (MoeRouteSelect.final_done _ _)
  refine ⟨a,b,h0,h1,count,?_⟩
  simpa [gates,Moe.selected,gtFlag] using trace

theorem reconstruct_masked (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : Bounds ctx) (hm : i.m ≤ col ctx.block ctx.id)
    {n last events} (hn : Scalar.run ctx oracle code n {} = .ok (last,events))
    (hd : last.core.thread.status = .done) : n = 11 ∧ last = maskedFinal i ctx ∧ events = [] :=
  complete_run_unique hn hd (masked_run i ctx oracle hp hb hm) rfl

end
end Ptx.MoeRouteThread
