import Ptx.Kernels.MoeExpertsThread
import Ptx.Tests.MoeExpertsLoop

/-! Applications of the parameterized source-entry rules. Local source
completion and reconstruction remain distinct from legal global execution. -/
namespace Ptx.MoeExpertsThreadTests
open Ptx.ISA Ptx.Scalar Ptx.MoeExperts Ptx.MoeExpertsLoop
noncomputable section

def input : Inputs := {
  x := 0,w := 64,r := 128,h := 256,m := 3,n := 3,k := 2
  x64 := by decide,w64 := by decide,r64 := by decide,h64 := by decide
  m32 := by decide,n32 := by decide,k32 := by decide
}
abbrev ctx := MoeExpertsLoopTests.ctx
theorem params : Params input ctx.params := by constructor <;> rfl
theorem indices : IndexBounds ctx := by
  constructor <;> norm_num [ctx,MoeExpertsLoopTests.ctx,row,col,Dim3.zero]
theorem addresses (expert : Nat) (he : expert < 2) : AddressBounds input ctx expert := by
  constructor
  · change 256+expert*(4*(3*3))+4*(2*3+2) < 2^64
    omega
  · intro k hk
    change k < 2 at hk
    change 0+4*(2*2)+4*k < 2^64
    omega
  · intro k hk
    change k < 2 at hk
    change 64+expert*(4*(2*3))+4*2+(4*3)*k < 2^64
    omega

theorem arbitrary_completed_expert (oracle : Scalar.Oracle) {n last events}
    (hq : oracle 0 = .integer 1) (hr : Scalar.run ctx oracle code n {} = .ok (last,events))
    (hd : last.core.thread.status = .done) : n = 68 ∧
    events = [routeEvent input ctx 1] ++
      (FmaLoop.loopReads (threadLayout input ctx 1 (addresses 1 (by decide)))
        (FmaLoop.replyA 1 oracle) (FmaLoop.replyB 1 oracle) 0 0 0 2 ++
        [.write ⟨.global,324⟩ (Symbolic.encode .f32
          (ScalarMatmul.prefixProduct (FmaLoop.replyA 1 oracle) (FmaLoop.replyB 1 oracle) 0 0 2))]) := by
  have h := reconstruct_active input ctx oracle 1 params indices (by decide) (by decide) (by decide)
    hq (by decide) (addresses 1 (by decide)) hr hd
  simpa [activeCount,selectSteps,input,threadLayout,wBase,hBase,ctx,MoeExpertsLoopTests.ctx,row,col,Dim3.zero,wrap] using h

theorem invalid_route_has_no_float_accesses (tail : Scalar.Oracle) : ∃ last,
    Scalar.run ctx (MoeExpertsLoopTests.routed 17 tail) code 27 {} =
      .ok (last,[.read ⟨.global,136⟩ (u32Bytes 17)]) ∧
      last.core.thread.status = .done ∧ last.core.queries = 1 := by
  simpa [routeEvent,input,ctx,MoeExpertsLoopTests.ctx,row,col,Dim3.zero,wrap] using
    invalid_route_execution input ctx (MoeExpertsLoopTests.routed 17 tail) 17 params indices
      (by decide) (by decide) (by decide) rfl (by decide)

theorem raw_route_is_normalized : wrap 32 (2^32+1) = 1 := by decide
theorem wrapped_route_reaches_expert_one (tail : Scalar.Oracle) : ∃ entry,
    Scalar.run ctx (MoeExpertsLoopTests.routed (2^32+1) tail) code 46 {} =
      .ok (entry,[.read ⟨.global,136⟩ (u32Bytes 1)]) ∧
      FmaLoop.Inv 46 1 (threadLayout input ctx 1 (addresses 1 (by decide))) 0 0 entry := by
  have h := active_initialization input ctx (MoeExpertsLoopTests.routed (2^32+1) tail) (2^32+1)
    params indices (by decide) (by decide) (by decide) rfl
    (by rw [raw_route_is_normalized]; decide) (raw_route_is_normalized ▸ addresses 1 (by decide))
  simpa [raw_route_is_normalized,selectSteps,routeEvent,input,ctx,MoeExpertsLoopTests.ctx,row,col,Dim3.zero,wrap] using h

def maskedInput (m n : Nat) (hm : m < 2^32) (hn : n < 2^32) : Inputs := {
  x := 1,w := 1,r := 1,h := 1,m := m,n := n,k := 2^32-1
  x64 := by decide,w64 := by decide,r64 := by decide,h64 := by decide
  m32 := hm,n32 := hn,k32 := by decide
}
def maskedCtx (m n : Nat) : Scalar.Context := {ctx with
  params := [("X",1),("W",1),("R",1),("H",1),("M",m),("N",n),("K",2^32-1)]}
theorem masked_params (m n : Nat) (hm hn) : Params (maskedInput m n hm hn) (maskedCtx m n).params := by
  constructor <;> rfl
theorem masked_indices (m n : Nat) : IndexBounds (maskedCtx m n) :=
  ⟨indices.bx,indices.byBound,indices.sx,indices.sy,indices.tx,indices.ty,indices.rowBound,indices.colBound⟩

theorem empty_rows_without_memory (oracle : Scalar.Oracle) : ∃ last,
    Scalar.run (maskedCtx 0 3) oracle code 20 {} = .ok (last,[]) ∧
      last.core.thread.status = .done ∧ last.core.queries = 0 :=
  masked_row (maskedInput 0 3 (by decide) (by decide)) (maskedCtx 0 3) oracle
    (masked_params _ _ _ _) (masked_indices _ _) (by decide)
theorem empty_columns_without_memory (oracle : Scalar.Oracle) : ∃ last,
    Scalar.run (maskedCtx 3 0) oracle code 22 {} = .ok (last,[]) ∧
      last.core.thread.status = .done ∧ last.core.queries = 0 :=
  masked_col (maskedInput 3 0 (by decide) (by decide)) (maskedCtx 3 0) oracle
    (masked_params _ _ _ _) (masked_indices _ _) (by decide) (by decide)

end
end Ptx.MoeExpertsThreadTests
