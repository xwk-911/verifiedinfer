import Ptx.Generated.MoeExperts
import Ptx.Kernels.MoeSpec
import Ptx.Scalar.FmaLoopTrace

/-! Actual expert PCs 46--56, reusing the same checked fragment rules as
matmul. The prior u32 route load occupies oracle query zero. Full parameterized
entry/selection/layout and global input/output proofs are separate obligations. -/
namespace Ptx.MoeExpertsLoop
open Ptx.ISA Ptx.Scalar
noncomputable section
abbrev code := Generated.moe_experts.program
abbrev Layout := FmaLoop.Layout

theorem fragment : FmaLoop.Fragment code 46 := by constructor <;> rfl
def expertMatrix (weights : Moe.Weights) (expert : Nat) : ScalarMatmul.Matrix :=
  fun item col => weights expert item col

theorem linear_prefix (x : Moe.Matrix) (weights : Moe.Weights) (expert row col count : Nat) :
    ScalarMatmul.prefixProduct x (expertMatrix weights expert) row col count = Moe.linear x weights expert row col count := by
  induction count with
  | zero => rfl
  | succ k ih => simp only [ScalarMatmul.prefixProduct,Moe.linear,expertMatrix,ih]

theorem complete (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (x : Moe.Matrix) (weights : Moe.Weights) (expert row col : Nat)
    (hx : ∀ k, k < l.count → oracle (1+2*k) = .real .f32 (x row k))
    (hw : ∀ k, k < l.count → oracle (1+2*k+1) = .real .f32 (weights expert k col))
    {s : Scalar.State} (hi : FmaLoop.Inv 46 1 l 0 0 s) :
    ∃ last, Scalar.run ctx oracle code (9*l.count+4) s = .ok
      (last,FmaLoop.loopReads l x (expertMatrix weights expert) row col 0 l.count ++
        [.write ⟨.global,l.output⟩ (Symbolic.encode .f32 (Moe.linear x weights expert row col l.count))]) ∧
      FmaLoop.Finished 46 1 l (Moe.linear x weights expert row col l.count) last := by
  simpa only [linear_prefix] using FmaLoop.complete_from_entry fragment l ctx oracle x (expertMatrix weights expert)
    row col hx hw hi

theorem reconstruct (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {s last : Scalar.State} {n : Nat} {events : List Scalar.Kind} (hi : FmaLoop.Inv 46 1 l 0 0 s)
    (hr : Scalar.run ctx oracle code n s = .ok (last,events)) (hd : last.core.thread.status = .done) :
    n = 9*l.count+4 ∧
      events = FmaLoop.loopReads l (FmaLoop.replyA 1 oracle) (FmaLoop.replyB 1 oracle) 0 0 0 l.count ++
        [.write ⟨.global,l.output⟩ (Symbolic.encode .f32
          (ScalarMatmul.prefixProduct (FmaLoop.replyA 1 oracle) (FmaLoop.replyB 1 oracle) 0 0 l.count))] ∧
      FmaLoop.Finished 46 1 l
        (ScalarMatmul.prefixProduct (FmaLoop.replyA 1 oracle) (FmaLoop.replyB 1 oracle) 0 0 l.count) last :=
  FmaLoop.completed_shape fragment l ctx oracle hi hr hd

end
end Ptx.MoeExpertsLoop
