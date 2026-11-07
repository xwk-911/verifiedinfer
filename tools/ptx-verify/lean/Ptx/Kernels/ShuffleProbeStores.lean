import Ptx.Kernels.ShuffleProbeTrace

/-! Actual address arithmetic and both exported stores. Addresses retain u64
wrapping and both outputs retain integer bytes; no float encoding is involved. -/
namespace Ptx.Kernels.ShuffleProbe
open Ptx.ISA Ptx.Shuffle
noncomputable section

theorem address_run (mode : Mode) (input : Inputs) (ctx : Scalar.Context) (answers : Shuffle.Oracle)
    (value : Nat) (predicate : Bool) :
    Shuffle.run ctx answers (code mode) 2 (flagged mode input ctx value predicate) =
      .ok (addressed mode input ctx value predicate,[]) := by
  have h0 : Shuffle.step ctx answers (code mode) (flagged mode input ctx value predicate) =
      .ok (Shuffle.intAssign (flagged mode input ctx value predicate) "%rd1" (w64 (rawIndex ctx*8)),[]) := by
    cases predicate
    all_goals
      apply Shuffle.integer_local_step rfl rfl rfl (by intro bid h; cases h)
      simp [localStep,Ptx.eval,flagged,afterShuffle,writeResult,prefixState,assignments,
        Shuffle.intAssign,Shuffle.intPC,Scalar.intAssign,Scalar.intPC,Scalar.finishInteger,assign,advance,lookup,put,
        rawIndex,xProduct,yzIndex,yzProduct,inputWord,w32,w64,wrap,bind,Except.bind,pure,Except.pure]
  have h1 : Shuffle.step ctx answers (code mode)
      (Shuffle.intAssign (flagged mode input ctx value predicate) "%rd1" (w64 (rawIndex ctx*8))) =
      .ok (addressed mode input ctx value predicate,[]) := by
    cases predicate
    all_goals
      apply Shuffle.integer_local_step rfl rfl rfl (by intro bid h; cases h)
      simp [localStep,Ptx.eval,addressed,address,flagged,afterShuffle,writeResult,prefixState,assignments,
        Shuffle.intAssign,Shuffle.intPC,Scalar.intAssign,Scalar.intPC,Scalar.finishInteger,assign,advance,lookup,put,
        w32,w64,wrap,bind,Except.bind,pure,Except.pure]
  simp [Shuffle.run,h0,h1,Except.bind]

theorem stores_run (mode : Mode) (input : Inputs) (ctx : Scalar.Context) (answers : Shuffle.Oracle)
    (value : Nat) (predicate : Bool) :
    Shuffle.run ctx answers (code mode) 2 (addressed mode input ctx value predicate) =
      .ok (beforeRet mode input ctx value predicate,outputEvents input ctx value predicate) := by
  have h0 : Shuffle.step ctx answers (code mode) (addressed mode input ctx value predicate) =
      .ok (advanceState (addressed mode input ctx value predicate),
        [.ordinary (.write (outputLoc input ctx 0) ((encodeU32 (w32 value)).map Symbolic.Byte.bits))]) := by
    have hs := Shuffle.integer_store_step (ctx := ctx) (oracle := answers) (code := code mode)
      (state := addressed mode input ctx value predicate) (space := .global)
      (address := {base := .reg "%rd2",offset := 0}) (operand := .reg "%r11")
      (addr := w64 (address input ctx+0)) (value := w32 value)
      (by cases predicate <;> rfl) (by cases predicate <;> rfl)
      (by simp [evalAddr,Ptx.eval,addressed,Shuffle.intAssign,Scalar.intAssign,Scalar.finishInteger,assign,advance,
        w64,bind,Except.bind,pure,Except.pure])
      (by cases predicate <;> simp [Ptx.eval,addressed,flagged,afterShuffle,writeResult,Shuffle.intAssign,Shuffle.intPC,
        Scalar.intAssign,Scalar.intPC,Scalar.finishInteger,assign,advance,w32])
    simpa only [advanceState,outputLoc,Location.resolve] using hs
  have h1 : Shuffle.step ctx answers (code mode) (advanceState (addressed mode input ctx value predicate)) =
      .ok (beforeRet mode input ctx value predicate,
        [.ordinary (.write (outputLoc input ctx 4) ((encodeU32 (if predicate then 1 else 0)).map Symbolic.Byte.bits))]) := by
    have hs := Shuffle.integer_store_step (ctx := ctx) (oracle := answers) (code := code mode)
      (state := advanceState (addressed mode input ctx value predicate)) (space := .global)
      (address := {base := .reg "%rd2",offset := 4}) (operand := .reg "%r12")
      (addr := w64 (address input ctx+4)) (value := if predicate then 1 else 0)
      (by cases predicate <;> rfl) (by cases predicate <;> rfl)
      (by simp [evalAddr,Ptx.eval,advanceState,addressed,Shuffle.intAssign,Scalar.intAssign,Scalar.finishInteger,assign,advance,
        w64,bind,Except.bind,pure,Except.pure])
      (by cases predicate <;> simp [Ptx.eval,advanceState,addressed,flagged,Shuffle.intAssign,Shuffle.intPC,
        Scalar.intAssign,Scalar.intPC,Scalar.finishInteger,assign,advance])
    simpa only [beforeRet,advanceState,outputLoc,Location.resolve] using hs
  simp [Shuffle.run,h0,h1,outputEvents,Except.bind]

theorem return_run (mode : Mode) (input : Inputs) (ctx : Scalar.Context) (answers : Shuffle.Oracle)
    (value : Nat) (predicate : Bool) :
    Shuffle.run ctx answers (code mode) 1 (beforeRet mode input ctx value predicate) =
      .ok (finalState mode input ctx value predicate,[]) := by
  have hs : Shuffle.step ctx answers (code mode) (beforeRet mode input ctx value predicate) =
      .ok (finalState mode input ctx value predicate,[]) := by
    cases predicate <;> apply Shuffle.integer_local_step rfl rfl rfl (by intro bid h; cases h) <;> rfl
  simp [Shuffle.run,hs,Except.bind]

theorem complete_source_run (mode : Mode) (input : Inputs) (ctx : Scalar.Context) (answers : Shuffle.Oracle)
    (hp : Params input ctx.params) :
    Shuffle.run ctx answers (code mode) 24 {} =
      .ok (finalState mode input ctx (answers.shuffle 0).1 (answers.shuffle 0).2,
        events mode input ctx (answers.shuffle 0).1 (answers.shuffle 0).2) := by
  have hshuffle : Shuffle.run ctx answers (code mode) 1 (prefixState input ctx 15) =
      .ok (afterShuffle mode input ctx (answers.shuffle 0).1 (answers.shuffle 0).2,
        [.shuffle (record mode input ctx (answers.shuffle 0).1 (answers.shuffle 0).2)]) := by
    simp [Shuffle.run,shuffle_source_step,Except.bind]
  have h := Shuffle.run_join (preamble_run mode input ctx answers hp)
    (Shuffle.run_join hshuffle (Shuffle.run_join (flag_run mode input ctx answers _ _)
      (Shuffle.run_join (address_run mode input ctx answers _ _)
        (Shuffle.run_join (stores_run mode input ctx answers _ _) (return_run mode input ctx answers _ _)))))
  simpa only [events,List.nil_append,List.singleton_append,List.append_nil] using h

theorem completed_source_shape {mode input ctx answers count final actualEvents} (hp : Params input ctx.params)
    (hr : Shuffle.run ctx answers (code mode) count {} = .ok (final,actualEvents))
    (hd : final.base.core.thread.status = .done) :
    count = 24 ∧ final = finalState mode input ctx (answers.shuffle 0).1 (answers.shuffle 0).2 ∧
      actualEvents = events mode input ctx (answers.shuffle 0).1 (answers.shuffle 0).2 :=
  Shuffle.complete_run_unique hr hd (complete_source_run mode input ctx answers hp) rfl

end
end Ptx.Kernels.ShuffleProbe
