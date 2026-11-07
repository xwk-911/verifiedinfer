import Ptx.Generated.ScalarFlashAttention
import Ptx.Scalar.OnlineSoftmax
import Ptx.Scalar.RegisterFrame

/-! The nine arithmetic instructions at PCs 56--64 of the ACTUAL generated
scalar attention kernel implement the reusable online-softmax update. This local
block neither assumes nor proves that memory supplied the right Q/K/V values.
Full loop reconstruction, memory safety/consistency and nonvacuity remain duties.
-/
namespace Ptx.ScalarAttentionUpdate
open Ptx.ISA Ptx.Scalar
noncomputable section
abbrev code := Generated.scalar_flash_attention.program

def Registers (s : Scalar.State) (v : OnlineSoftmax.State) : Prop :=
  declarationLookup "%max" s.floats = some (.f32,v.maximum) ∧
  declarationLookup "%l" s.floats = some (.f32,v.normalizer) ∧
  declarationLookup "%u" s.floats = some (.f32,v.accumulator)

def afterUpdate (s : Scalar.State) (v : OnlineSoftmax.State) (score value : ℝ) : Scalar.State :=
  let next := max v.maximum score
  let a := RealMath.exp2 (v.maximum-next)
  let w := RealMath.exp2 (score-next)
  let s1 := writeFloat s "%nextm" .f32 next
  let s2 := writeFloat s1 "%a" .f32 (v.maximum-next)
  let s3 := writeFloat s2 "%w" .f32 (score-next)
  let s4 := writeFloat s3 "%a" .f32 a
  let s5 := writeFloat s4 "%w" .f32 w
  let s6 := writeFloat s5 "%u" .f32 (v.accumulator*a)
  let s7 := writeFloat s6 "%u" .f32 (w*value+v.accumulator*a)
  let s8 := writeFloat s7 "%l" .f32 (v.normalizer*a+w)
  writeFloat s8 "%max" .f32 next

theorem eval_lookup {s : Scalar.State} {name : String} {value : ℝ}
    (h : declarationLookup name s.floats = some (.f32,value)) :
    Scalar.eval .f32 s (.reg name) = .ok value := by
  simp [Scalar.eval,require,h,bind,Except.bind,pure,Except.pure]

theorem update_block (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (s : Scalar.State) (v : OnlineSoftmax.State) (score value : ℝ)
    (hr : s.core.thread.status = .running) (hp : s.core.thread.pc = 56)
    (hv : Registers s v)
    (hscore : declarationLookup "%score" s.floats = some (.f32,score))
    (hvalue : declarationLookup "%vv" s.floats = some (.f32,value)) :
    Scalar.run ctx oracle code 9 s = .ok (afterUpdate s v score value,[]) := by
  let next := max v.maximum score
  let a := RealMath.exp2 (v.maximum-next)
  let w := RealMath.exp2 (score-next)
  let s1 := writeFloat s "%nextm" .f32 next
  let s2 := writeFloat s1 "%a" .f32 (v.maximum-next)
  let s3 := writeFloat s2 "%w" .f32 (score-next)
  let s4 := writeFloat s3 "%a" .f32 a
  let s5 := writeFloat s4 "%w" .f32 w
  let s6 := writeFloat s5 "%u" .f32 (v.accumulator*a)
  let s7 := writeFloat s6 "%u" .f32 (w*value+v.accumulator*a)
  let s8 := writeFloat s7 "%l" .f32 (v.normalizer*a+w)
  let s9 := writeFloat s8 "%max" .f32 next
  have h56 : Scalar.step ctx oracle code s = .ok (s1,[]) := by
    apply max_float_step hr (by rw [hp]; rfl) (eval_lookup hv.1) (eval_lookup hscore)
  have h57 : Scalar.step ctx oracle code s1 = .ok (s2,[]) := by
    apply sub_float_step
    · simpa [s1,writeFloat,advance] using hr
    · simp only [s1,writeFloat,advance,hp]; rfl
    · apply eval_lookup; simpa [s1] using hv.1
    · apply eval_lookup; simp [s1]
  have h58 : Scalar.step ctx oracle code s2 = .ok (s3,[]) := by
    apply sub_float_step
    · simpa [s2,s1,writeFloat,advance] using hr
    · simp only [s2,s1,writeFloat,advance,hp]; rfl
    · apply eval_lookup; simpa [s2,s1] using hscore
    · apply eval_lookup; simp [s2,s1]
  have h59 : Scalar.step ctx oracle code s3 = .ok (s4,[]) := by
    apply ex2_float_step
    · simpa [s3,s2,s1,writeFloat,advance] using hr
    · simp only [s3,s2,s1,writeFloat,advance,hp]; rfl
    · apply eval_lookup; simp [s3,s2]
  have h60 : Scalar.step ctx oracle code s4 = .ok (s5,[]) := by
    apply ex2_float_step
    · simpa [s4,s3,s2,s1,writeFloat,advance] using hr
    · simp only [s4,s3,s2,s1,writeFloat,advance,hp]; rfl
    · apply eval_lookup; simp [s4,s3]
  have h61 : Scalar.step ctx oracle code s5 = .ok (s6,[]) := by
    apply mul_float_step
    · simpa [s5,s4,s3,s2,s1,writeFloat,advance] using hr
    · simp only [s5,s4,s3,s2,s1,writeFloat,advance,hp]; rfl
    · apply eval_lookup; simpa [s5,s4,s3,s2,s1] using hv.2.2
    · apply eval_lookup; simp [s5,s4]
  have h62 : Scalar.step ctx oracle code s6 = .ok (s7,[]) := by
    apply fma_step
    · simpa [s6,s5,s4,s3,s2,s1,writeFloat,advance] using hr
    · simp only [s6,s5,s4,s3,s2,s1,writeFloat,advance,hp]; rfl
    · apply eval_lookup; simp [s6,s5]
    · apply eval_lookup; simpa [s6,s5,s4,s3,s2,s1] using hvalue
    · apply eval_lookup; simp [s6]
  have h63 : Scalar.step ctx oracle code s7 = .ok (s8,[]) := by
    apply fma_step
    · simpa [s7,s6,s5,s4,s3,s2,s1,writeFloat,advance] using hr
    · simp only [s7,s6,s5,s4,s3,s2,s1,writeFloat,advance,hp]; rfl
    · apply eval_lookup; simpa [s7,s6,s5,s4,s3,s2,s1] using hv.2.1
    · apply eval_lookup; simp [s7,s6,s5,s4]
    · apply eval_lookup; simp [s7,s6,s5]
  have h64 : Scalar.step ctx oracle code s8 = .ok (s9,[]) := by
    apply mov_float_step
    · simpa [s8,s7,s6,s5,s4,s3,s2,s1,writeFloat,advance] using hr
    · simp only [s8,s7,s6,s5,s4,s3,s2,s1,writeFloat,advance,hp]; rfl
    · apply eval_lookup; simp [s8,s7,s6,s5,s4,s3,s2,s1]
  simp only [Scalar.run,h56,h57,h58,h59,h60,h61,h62,h63,h64,Except.bind,List.nil_append]
  rfl

theorem update_registers (s : Scalar.State) (v : OnlineSoftmax.State) (score value : ℝ) :
    Registers (afterUpdate s v score value) (OnlineSoftmax.update v score value) := by
  simp [Registers,afterUpdate,OnlineSoftmax.update,add_comm]

theorem update_pc (s : Scalar.State) (v : OnlineSoftmax.State) (score value : ℝ)
    (hp : s.core.thread.pc = 56) : (afterUpdate s v score value).core.thread.pc = 65 := by
  simp [afterUpdate,writeFloat,advance,hp]

theorem update_queries (s : Scalar.State) (v : OnlineSoftmax.State) (score value : ℝ) :
    (afterUpdate s v score value).core.queries = s.core.queries := rfl

def changed : List String := ["%nextm","%a","%w","%u","%l","%max"]

theorem update_frame (s : Scalar.State) (v : OnlineSoftmax.State) (score value : ℝ) :
    RegisterFrame changed s (afterUpdate s v score value) := by
  unfold afterUpdate
  apply register_frame_trans (writeFloat_register_frame s "%nextm" .f32 _ (by decide))
  apply register_frame_trans (writeFloat_register_frame _ "%a" .f32 _ (by decide))
  apply register_frame_trans (writeFloat_register_frame _ "%w" .f32 _ (by decide))
  apply register_frame_trans (writeFloat_register_frame _ "%a" .f32 _ (by decide))
  apply register_frame_trans (writeFloat_register_frame _ "%w" .f32 _ (by decide))
  apply register_frame_trans (writeFloat_register_frame _ "%u" .f32 _ (by decide))
  apply register_frame_trans (writeFloat_register_frame _ "%u" .f32 _ (by decide))
  apply register_frame_trans (writeFloat_register_frame _ "%l" .f32 _ (by decide))
  exact writeFloat_register_frame _ "%max" .f32 _ (by decide)

theorem update_preserves_invariant (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (s : Scalar.State) (v : OnlineSoftmax.State) (score value : Nat → ℝ) (count : Nat)
    (hr : s.core.thread.status = .running) (hp : s.core.thread.pc = 56)
    (hv : Registers s v) (hi : OnlineSoftmax.Inv score value count v)
    (hscore : declarationLookup "%score" s.floats = some (.f32,score count))
    (hvalue : declarationLookup "%vv" s.floats = some (.f32,value count)) :
    ∃ next, Scalar.run ctx oracle code 9 s = .ok (next,[]) ∧
      Registers next (OnlineSoftmax.update v (score count) (value count)) ∧
      OnlineSoftmax.Inv score value (count+1) (OnlineSoftmax.update v (score count) (value count)) :=
  ⟨afterUpdate s v (score count) (value count),update_block ctx oracle s v _ _ hr hp hv hscore hvalue,
    update_registers s v _ _,OnlineSoftmax.update_inv hi⟩

def afterInitial (s : Scalar.State) (score value : ℝ) : Scalar.State :=
  writeFloat (writeFloat (writeFloat s "%max" .f32 score) "%l" .f32 1) "%u" .f32 value

theorem initial_block (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (s : Scalar.State) (score value : ℝ)
    (hr : s.core.thread.status = .running) (hp : s.core.thread.pc = 66)
    (hs : declarationLookup "%score" s.floats = some (.f32,score))
    (hv : declarationLookup "%vv" s.floats = some (.f32,value)) :
    Scalar.run ctx oracle code 3 s = .ok (afterInitial s score value,[]) := by
  let s1 := writeFloat s "%max" .f32 score
  let s2 := writeFloat s1 "%l" .f32 1
  let s3 := writeFloat s2 "%u" .f32 value
  have h66 : Scalar.step ctx oracle code s = .ok (s1,[]) :=
    mov_float_step hr (by rw [hp]; rfl) (eval_lookup hs)
  have h67 : Scalar.step ctx oracle code s1 = .ok (s2,[]) := by
    apply mov_float_step
    · simpa [s1,writeFloat,advance] using hr
    · simp only [s1,writeFloat,advance,hp]; rfl
    · norm_num [Scalar.eval,F32Literal.value]
  have h68 : Scalar.step ctx oracle code s2 = .ok (s3,[]) := by
    apply mov_float_step
    · simpa [s2,s1,writeFloat,advance] using hr
    · simp only [s2,s1,writeFloat,advance,hp]; rfl
    · apply eval_lookup; simpa [s2,s1] using hv
  simp only [Scalar.run,h66,h67,h68,Except.bind,List.nil_append]
  rfl

theorem initial_registers (s : Scalar.State) (score value : ℝ) :
    Registers (afterInitial s score value) (OnlineSoftmax.initial score value) := by
  simp [Registers,afterInitial,OnlineSoftmax.initial]

theorem initial_frame (s : Scalar.State) (score value : ℝ) :
    RegisterFrame ["%max","%l","%u"] s (afterInitial s score value) := by
  unfold afterInitial
  apply register_frame_trans (writeFloat_register_frame s "%max" .f32 _ (by decide))
  apply register_frame_trans (writeFloat_register_frame _ "%l" .f32 _ (by decide))
  exact writeFloat_register_frame _ "%u" .f32 _ (by decide)

/-- The positive normalizer is DERIVED from the reusable prefix invariant.
It is not assumed merely to make finite-real division succeed. This tail proof
does not yet establish that the full PTX reaches PC 73 with this invariant. -/
theorem normalize_store (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (s : Scalar.State) (v : OnlineSoftmax.State) (score value : Nat → ℝ) (count output : Nat)
    (hr : s.core.thread.status = .running) (hp : s.core.thread.pc = 73)
    (hv : Registers s v) (hi : OnlineSoftmax.Inv score value count v) (hn : 0 < count)
    (ho : lookup "%op" s.core.thread.regs = some output) (hbound : output < 2^64) :
    ∃ final, Scalar.run ctx oracle code 3 s = .ok
      (final,[.write ⟨.global,output⟩ (Symbolic.encode .f32 (OnlineSoftmax.average score value count))]) ∧
      final.core.thread.status = .done := by
  let s1 := writeFloat s "%out" .f32 (v.accumulator/v.normalizer)
  let s2 : Scalar.State := {s1 with core := {s1.core with thread := advance s1.core.thread}}
  let s3 := finishInteger s2 {s2.core with thread := {s2.core.thread with status := .done}}
  have h73 : Scalar.step ctx oracle code s = .ok (s1,[]) :=
    div_float_step hr (by rw [hp]; rfl) (eval_lookup hv.2.2) (eval_lookup hv.2.1)
      (OnlineSoftmax.normalizer_pos hi hn).ne'
  have h74 : Scalar.step ctx oracle code s1 = .ok
      (s2,[.write ⟨.global,output⟩ (Symbolic.encode .f32 (v.accumulator/v.normalizer))]) := by
    apply store_step (space := .global) (format := .f32) (address := {base := .reg "%op"})
      (value := .reg "%out") (addr := output) (x := v.accumulator/v.normalizer)
    · simpa [s1,writeFloat,advance] using hr
    · simp only [s1,writeFloat,advance,hp]; rfl
    · simp [evalAddr,Ptx.eval,s1,ho,show wrap 64 output = output from Nat.mod_eq_of_lt hbound,
        bind,Except.bind,pure,Except.pure]
    · exact eval_written_float _ _ _ _
  have h75 : Scalar.step ctx oracle code s2 = .ok (s3,[]) := by
    apply integer_local_step
    · simpa [s2,s1,writeFloat,advance] using hr
    · simp only [s2,s1,writeFloat,advance,hp]; rfl
    · rfl
    · intro bid h; cases h
    · rfl
  have hnorm : v.accumulator/v.normalizer = OnlineSoftmax.average score value count := by
    rw [OnlineSoftmax.normalized hi]
    simp [OnlineSoftmax.average,show count ≠ 0 from by omega]
  refine ⟨s3,?_,rfl⟩
  simp [Scalar.run,h73,h74,h75,Except.bind,hnorm]

end
end Ptx.ScalarAttentionUpdate
