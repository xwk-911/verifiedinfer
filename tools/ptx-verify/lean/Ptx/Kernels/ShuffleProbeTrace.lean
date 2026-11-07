import Ptx.Kernels.ShuffleProbePrefix

/-! Complete actual source runs for all four exported probes. Shuffle values
and predicates remain arbitrary local oracle replies. Their global agreement,
launch-wide participation and memory observation are separate obligations. -/
namespace Ptx.Kernels.ShuffleProbe
open Ptx.ISA Ptx.Shuffle
noncomputable section

theorem prefix_registers (input : Inputs) (ctx : Scalar.Context) :
    lookup "%r10" (prefixState input ctx 15).base.core.thread.regs = some (inputWord input ctx) ∧
    lookup "%r0" (prefixState input ctx 15).base.core.thread.regs = some (w32 input.b) ∧
    lookup "%r1" (prefixState input ctx 15).base.core.thread.regs = some (w32 input.c) ∧
    lookup "%r2" (prefixState input ctx 15).base.core.thread.regs = some (w32 input.mask) := by
  simp [prefixState,assignments,Shuffle.intAssign,Scalar.intAssign,Scalar.finishInteger,assign,advance]

theorem shuffle_source_step (mode : Mode) (input : Inputs) (ctx : Scalar.Context) (answers : Shuffle.Oracle) :
    Shuffle.step ctx answers (code mode) (prefixState input ctx 15) =
      .ok (afterShuffle mode input ctx (answers.shuffle 0).1 (answers.shuffle 0).2,
        [.shuffle (record mode input ctx (answers.shuffle 0).1 (answers.shuffle 0).2)]) := by
  obtain ⟨ha,hb,hc,hm⟩ := prefix_registers input ctx
  have hs := Shuffle.shfl_step (ctx := ctx) (oracle := answers) (code := code mode)
    (state := prefixState input ctx 15) (mode := mode) (dst := "%r11") (predicate := some "%p")
    (a := .reg "%r10") (b := .reg "%r0") (c := .reg "%r1") (mask := .reg "%r2")
    (input := inputWord input ctx) (offset := w32 input.b) (clamp := w32 input.c) (participants := w32 input.mask)
    rfl rfl (by simp [Ptx.eval,ha])
    (by simp [Ptx.eval,hb])
    (by simp [Ptx.eval,hc])
    (by simp [Ptx.eval,hm])
  have hq : (prefixState input ctx 15).queries = 0 := rfl
  have hv : (prefixState input ctx 15).visits = [] := rfl
  have hpc : (prefixState input ctx 15).base.core.thread.pc = 15 := rfl
  have ha' : wrap 32 (inputWord input ctx) = inputWord input ctx := w32_idem _
  have hb' : wrap 32 (w32 input.b) = w32 input.b := w32_idem _
  have hc' : wrap 32 (w32 input.c) = w32 input.c := w32_idem _
  have hm' : wrap 32 (w32 input.mask) = w32 input.mask := w32_idem _
  simpa [afterShuffle,record,groupKey,Shuffle.generation,Shuffle.advanceVisits,hq,hv,hpc,ha',hb',hc',hm',w32] using hs


theorem flag_run (mode : Mode) (input : Inputs) (ctx : Scalar.Context) (answers : Shuffle.Oracle)
    (value : Nat) (predicate : Bool) :
    Shuffle.run ctx answers (code mode) 3 (afterShuffle mode input ctx value predicate) =
      .ok (flagged mode input ctx value predicate,[]) := by
  have h0 : Shuffle.step ctx answers (code mode) (afterShuffle mode input ctx value predicate) =
      .ok (Shuffle.intAssign (afterShuffle mode input ctx value predicate) "%r12" 0,[]) := by
    apply Shuffle.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    rfl
  have hpc : (prefixState input ctx 15).base.core.thread.pc = 15 := rfl
  have h1 : Shuffle.step ctx answers (code mode) (Shuffle.intAssign (afterShuffle mode input ctx value predicate) "%r12" 0) =
      .ok (Shuffle.intPC (Shuffle.intAssign (afterShuffle mode input ctx value predicate) "%r12" 0) (if predicate then 19 else 18),[]) := by
    cases predicate
    all_goals
      apply Shuffle.integer_local_step rfl rfl rfl (by intro bid h; cases h)
      simp [localStep,afterShuffle,writeResult,Shuffle.intAssign,Scalar.intAssign,Shuffle.intPC,Scalar.intPC,
        Scalar.finishInteger,assign,advance,lookup,put,hpc,bind,Except.bind,pure,Except.pure]
  cases predicate
  · have h2 : Shuffle.step ctx answers (code mode)
        (Shuffle.intPC (Shuffle.intAssign (afterShuffle mode input ctx value false) "%r12" 0) 18) =
        .ok (flagged mode input ctx value false,[]) := by
      apply Shuffle.integer_local_step rfl rfl rfl (by intro bid h; cases h)
      rfl
    simp [Shuffle.run,h0,h1,h2,Except.bind]
  · have h2 : Shuffle.step ctx answers (code mode)
        (Shuffle.intPC (Shuffle.intAssign (afterShuffle mode input ctx value true) "%r12" 0) 19) =
        .ok (flagged mode input ctx value true,[]) := by
      apply Shuffle.integer_local_step rfl rfl rfl (by intro bid h; cases h)
      rfl
    simp [Shuffle.run,h0,h1,h2,Except.bind]

end
end Ptx.Kernels.ShuffleProbe
