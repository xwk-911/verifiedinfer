import Ptx.Kernels.ScalarMatmulLoopTrace
import Ptx.Tests.ScalarMatmul

/-! Loop proofs applied to actual source entry states and boundary cases.
These are exact-real local executions, not global memory/GPU witnesses. -/
namespace Ptx.ScalarMatmulLoopTests
open Ptx.ISA Ptx.Scalar Ptx.ScalarMatmul Ptx.ScalarMatmulLoop
noncomputable section

def layout : Layout := {
  count := 2, aBase := 8, bBase := 68, stride := 12, output := 144
  count32 := by decide
  output64 := by decide
  aRead64 := by intro k hk; omega
  bRead64 := by intro k hk; omega
}

def entry : Scalar.State := {
  core := {thread := {pc := 32,regs := [
    ("%k",0),("%cp",144),("%stride",12),("%bp",68),("%offset",4),("%ap",8),("%p",0),
    ("%col",1),("%tx",1),("%sx",2),("%bx",0),("%row",1),("%ty",1),("%sy",2),("%by",0),
    ("%kmax",2),("%n",3),("%m",2),("%c",128),("%b",64),("%a",0)]}}
  floats := [("%acc",(.f32,ScalarMatmulTests.literalZero))]
}

theorem actual_prefix (oracle : Scalar.Oracle) :
    Scalar.run ScalarMatmulTests.twoContext oracle code 32 {} = .ok (entry,[]) := rfl

theorem actual_entry_invariant : Inv layout 0 0 entry := by
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [entry,declarationLookup,ScalarMatmulTests.literal_zero]
  · exact run_banks_disjoint (actual_prefix (fun _ => .integer 0)) empty_banks_disjoint

/-- Fixed matrix dimensions/address instance, but ALL real matrices, connected
to the generated source from PC=0 via the actual prefix. No memory verdict. -/
theorem actual_program_arbitrary_data (a b : Matrix) :
    ∃ final, Scalar.run ScalarMatmulTests.twoContext (inputOracle a b 1 1) code 54 {} =
      .ok (final,loopReads layout a b 1 1 0 2 ++
        [.write ⟨.global,144⟩ (Symbolic.encode .f32 (prefixProduct a b 1 1 2))]) ∧
      Finished layout (prefixProduct a b 1 1 2) final := by
  obtain ⟨final,hr,hf⟩ := complete_from_entry layout ScalarMatmulTests.twoContext (inputOracle a b 1 1)
    a b 1 1 (fun k _ => inputOracle_even a b 1 1 k) (fun k _ => inputOracle_odd a b 1 1 k)
    actual_entry_invariant
  refine ⟨final,?_,hf⟩
  have hfull := Scalar.run_append (actual_prefix (inputOracle a b 1 1)) hr
  rw [show 32+(9*layout.count+4) = 54 by decide,show layout.count = 2 by rfl,
    show layout.output = 144 by rfl,List.nil_append] at hfull
  exact hfull

theorem arbitrary_completed_shape (oracle : Scalar.Oracle) {n final events}
    (hr : Scalar.run ScalarMatmulTests.twoContext oracle code n entry = .ok (final,events))
    (hd : final.core.thread.status = .done) :
    n = 22 ∧ events = loopReads layout (replyA oracle) (replyB oracle) 0 0 0 2 ++
      [.write ⟨.global,144⟩ (Symbolic.encode .f32 (prefixProduct (replyA oracle) (replyB oracle) 0 0 2))] := by
  have h := completed_shape layout ScalarMatmulTests.twoContext oracle actual_entry_invariant hr hd
  exact ⟨h.1,h.2.1⟩

theorem integer_reply_cannot_complete (oracle : Scalar.Oracle) (hq : oracle 0 = .integer 0) :
    ¬ ∃ n final events, Scalar.run ScalarMatmulTests.twoContext oracle code n entry = .ok (final,events) ∧
      final.core.thread.status = .done := by
  rintro ⟨n,final,events,hr,hd⟩
  exact completed_wrong_type_rejected layout ScalarMatmulTests.twoContext oracle actual_entry_invariant
    (by decide) hq hr hd

theorem empty_loop_all_oracles (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hz : l.count = 0) {s : Scalar.State} (hi : Inv l 0 0 s) :
    ∃ final, Scalar.run ctx oracle code 4 s =
      .ok (final,[.write ⟨.global,l.output⟩ (Symbolic.encode .f32 0)]) ∧
      final.core.thread.status = .done ∧ final.core.queries = 0 := by
  have hi' : Inv l l.count 0 s := hz ▸ hi
  obtain ⟨final,hr,hf⟩ := finish l ctx oracle hi'
  exact ⟨final,hr,hf.done,by simpa only [hz,Nat.mul_zero] using hf.queries⟩

theorem wrong_late_format_cannot_complete (oracle : Scalar.Oracle) (hq : oracle 3 = .real .f16 0) :
    ¬ ∃ n final events, Scalar.run ScalarMatmulTests.twoContext oracle code n entry = .ok (final,events) ∧
      final.core.thread.status = .done := by
  rintro ⟨n,final,events,hr,hd⟩
  have h := completed_replies layout ScalarMatmulTests.twoContext oracle 2 rfl actual_entry_invariant hr hd
    1 (by decide) (by decide)
  have hh := h.2
  norm_num only [hq] at hh
  cases hh

def nearEndLayout : Layout := {
  count := 1, aBase := 2^64-4, bBase := 0, stride := 0, output := 32
  count32 := by decide
  output64 := by decide
  aRead64 := by
    intro k hk
    have hz : k = 0 := by omega
    subst k
    decide
  bRead64 := by intro k _; simp
}
def nearEndEntry : Scalar.State := {
  core := {thread := {pc := 32,regs := [
    ("%k",0),("%kmax",1),("%ap",wrap 64 (2^64-4)),("%bp",0),("%stride",0),("%cp",32)]}}
  floats := [("%acc",(.f32,0))]
}

theorem near_end_invariant : Inv nearEndLayout 0 0 nearEndEntry := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_,rfl,rfl,rfl,rfl,?_⟩
  · simp [nearEndEntry,nearEndLayout,lookup]
  · intro name
    by_cases h : name = "%acc"
    · subst name
      left
      simp [nearEndEntry,lookup]
    · right
      simp [nearEndEntry,declarationLookup,Ne.symm h]

/-- Final pointer arithmetic may wrap after the last valid read. The local loop
proof does not reject a trace merely because the unused one-past pointer wraps. -/
theorem one_past_pointer_wrap (ctx : Scalar.Context) :
    ∃ next, Scalar.run ctx (fun _ => .real .f32 0) code 9 nearEndEntry =
      .ok (next,reads nearEndLayout 0 0 0) ∧ lookup "%ap" next.core.thread.regs = some 0 := by
  obtain ⟨next,hr,hi⟩ := iteration nearEndLayout ctx (fun _ => .real .f32 0) near_end_invariant
    (by decide) rfl rfl
  refine ⟨next,hr,?_⟩
  have hp := hi.aPointer
  norm_num [nearEndLayout,wrap] at hp
  exact hp

end
end Ptx.ScalarMatmulLoopTests
