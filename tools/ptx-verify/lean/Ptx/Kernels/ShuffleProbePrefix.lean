import Ptx.Kernels.ShuffleProbe

/-! Actual fifteen-step source preamble, including 3-D index arithmetic.
No unwrapped-index or correct-shuffle-answer premise is introduced. -/
namespace Ptx.Kernels.ShuffleProbe
open Ptx.ISA Ptx.Shuffle
noncomputable section

theorem preamble_run (mode : Mode) (input : Inputs) (ctx : Scalar.Context) (answers : Shuffle.Oracle)
    (hp : Params input ctx.params) :
    Shuffle.run ctx answers (code mode) 15 {} = .ok (prefixState input ctx 15,[]) := by
  have h0 : Shuffle.step ctx answers (code mode) (prefixState input ctx 0) = .ok (prefixState input ctx 1,[]) := by
    apply Shuffle.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,prefixState,assignments,Shuffle.intAssign,Scalar.intAssign,Scalar.finishInteger,assign,advance,lookup,put,
      w32,w64,wrap,yzProduct,yzIndex,xProduct,rawIndex,inputWord,hp.out,bind,Except.bind,pure,Except.pure]
  have h1 : Shuffle.step ctx answers (code mode) (prefixState input ctx 1) = .ok (prefixState input ctx 2,[]) := by
    apply Shuffle.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,prefixState,assignments,Shuffle.intAssign,Scalar.intAssign,Scalar.finishInteger,assign,advance,lookup,put,
      w32,w64,wrap,yzProduct,yzIndex,xProduct,rawIndex,inputWord,hp.b,bind,Except.bind,pure,Except.pure]
  have h2 : Shuffle.step ctx answers (code mode) (prefixState input ctx 2) = .ok (prefixState input ctx 3,[]) := by
    apply Shuffle.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,prefixState,assignments,Shuffle.intAssign,Scalar.intAssign,Scalar.finishInteger,assign,advance,lookup,put,
      w32,w64,wrap,yzProduct,yzIndex,xProduct,rawIndex,inputWord,hp.c,bind,Except.bind,pure,Except.pure]
  have h3 : Shuffle.step ctx answers (code mode) (prefixState input ctx 3) = .ok (prefixState input ctx 4,[]) := by
    apply Shuffle.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,prefixState,assignments,Shuffle.intAssign,Scalar.intAssign,Scalar.finishInteger,assign,advance,lookup,put,
      w32,w64,wrap,yzProduct,yzIndex,xProduct,rawIndex,inputWord,hp.mask,bind,Except.bind,pure,Except.pure]
  have h4 : Shuffle.step ctx answers (code mode) (prefixState input ctx 4) = .ok (prefixState input ctx 5,[]) := by
    apply Shuffle.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,prefixState,assignments,Shuffle.intAssign,Scalar.intAssign,Scalar.finishInteger,assign,advance,lookup,put,
      w32,w64,wrap,yzProduct,yzIndex,xProduct,rawIndex,inputWord,hp.base,bind,Except.bind,pure,Except.pure]
  have h5 : Shuffle.step ctx answers (code mode) (prefixState input ctx 5) = .ok (prefixState input ctx 6,[]) := by
    apply Shuffle.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,prefixState,assignments,Shuffle.intAssign,Scalar.intAssign,Scalar.finishInteger,assign,advance,lookup,put,
      w32,w64,wrap,yzProduct,yzIndex,xProduct,rawIndex,inputWord,bind,Except.bind,pure,Except.pure]
  have h6 : Shuffle.step ctx answers (code mode) (prefixState input ctx 6) = .ok (prefixState input ctx 7,[]) := by
    exact Shuffle.read_special_step (ctx := ctx) (oracle := answers) (code := code mode) (state := prefixState input ctx 6) (dst := "%r5") (source := .tid .y) rfl rfl
  have h7 : Shuffle.step ctx answers (code mode) (prefixState input ctx 7) = .ok (prefixState input ctx 8,[]) := by
    exact Shuffle.read_special_step (ctx := ctx) (oracle := answers) (code := code mode) (state := prefixState input ctx 7) (dst := "%r6") (source := .tid .z) rfl rfl
  have h8 : Shuffle.step ctx answers (code mode) (prefixState input ctx 8) = .ok (prefixState input ctx 9,[]) := by
    exact Shuffle.read_special_step (ctx := ctx) (oracle := answers) (code := code mode) (state := prefixState input ctx 8) (dst := "%r7") (source := .ntid .x) rfl rfl
  have h9 : Shuffle.step ctx answers (code mode) (prefixState input ctx 9) = .ok (prefixState input ctx 10,[]) := by
    exact Shuffle.read_special_step (ctx := ctx) (oracle := answers) (code := code mode) (state := prefixState input ctx 9) (dst := "%r8") (source := .ntid .y) rfl rfl
  have h10 : Shuffle.step ctx answers (code mode) (prefixState input ctx 10) = .ok (prefixState input ctx 11,[]) := by
    apply Shuffle.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,prefixState,assignments,Shuffle.intAssign,Scalar.intAssign,Scalar.finishInteger,assign,advance,lookup,put,
      w32,w64,wrap,yzProduct,yzIndex,xProduct,rawIndex,inputWord,bind,Except.bind,pure,Except.pure]
  have h11 : Shuffle.step ctx answers (code mode) (prefixState input ctx 11) = .ok (prefixState input ctx 12,[]) := by
    apply Shuffle.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,prefixState,assignments,Shuffle.intAssign,Scalar.intAssign,Scalar.finishInteger,assign,advance,lookup,put,
      w32,w64,wrap,yzProduct,yzIndex,xProduct,rawIndex,inputWord,bind,Except.bind,pure,Except.pure]
  have h12 : Shuffle.step ctx answers (code mode) (prefixState input ctx 12) = .ok (prefixState input ctx 13,[]) := by
    apply Shuffle.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,prefixState,assignments,Shuffle.intAssign,Scalar.intAssign,Scalar.finishInteger,assign,advance,lookup,put,
      w32,w64,wrap,yzProduct,yzIndex,xProduct,rawIndex,inputWord,bind,Except.bind,pure,Except.pure]
  have h13 : Shuffle.step ctx answers (code mode) (prefixState input ctx 13) = .ok (prefixState input ctx 14,[]) := by
    apply Shuffle.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,prefixState,assignments,Shuffle.intAssign,Scalar.intAssign,Scalar.finishInteger,assign,advance,lookup,put,
      w32,w64,wrap,yzProduct,yzIndex,xProduct,rawIndex,inputWord,bind,Except.bind,pure,Except.pure]
  have h14 : Shuffle.step ctx answers (code mode) (prefixState input ctx 14) = .ok (prefixState input ctx 15,[]) := by
    apply Shuffle.integer_local_step rfl rfl rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,prefixState,assignments,Shuffle.intAssign,Scalar.intAssign,Scalar.finishInteger,assign,advance,lookup,put,
      w32,w64,wrap,yzProduct,yzIndex,xProduct,rawIndex,inputWord,bind,Except.bind,pure,Except.pure]
  change Shuffle.step ctx answers (code mode) {} = .ok (prefixState input ctx 1,[]) at h0
  simp only [Shuffle.run,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,Except.bind,List.nil_append]

end
end Ptx.Kernels.ShuffleProbe
