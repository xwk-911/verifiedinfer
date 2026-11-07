import Ptx.Kernels.HopperDoubleBufferResourceSourceOrder
import Mathlib.Tactic.IntervalCases

/-! Exhaustive local iteration resource slots. These cases classify actual
rich source events rather than using resource-history membership as a premise. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def isResourceEvent : Wgmma.Event → Bool
  | .base (.barrier _) | .base (.tmaIssue _) => true
  | _ => false

inductive DataResourceSource (a : TileA) (b : TileB) (tiles : Nat) : Ptx.Event.EventId → Wgmma.Event → Prop
  | init (slot : Stage) : DataResourceSource a b tiles (dataInitId tiles slot) (.base (.barrier ⟨dataGate slot,.init 1⟩))
  | expect (tile : Nat) (ht : tile < tiles) : DataResourceSource a b tiles (dataExpectId a b tiles tile)
      (.base (.barrier ⟨dataGate (stage tile),.arriveExpectTx 2304⟩))
  | wait (tile : Nat) (lane : Wgmma.Lane) (ht : tile < tiles) : DataResourceSource a b tiles (dataWaitId a b tiles tile lane)
      (waitEvent (ctx tiles lane) (barrierAddress (stage tile)) (expectedParity tile) true)
  | copyA (tile : Nat) (ht : tile < tiles) : DataResourceSource a b tiles (dataCopyAId a b tiles tile).issue (.base (.tmaIssue (dataCopyA a tiles tile)))
  | copyB (tile : Nat) (ht : tile < tiles) : DataResourceSource a b tiles (dataCopyBId a b tiles tile).issue (.base (.tmaIssue (dataCopyB b tiles tile)))
  | inval (slot : Stage) : DataResourceSource a b tiles (dataInvalId a b tiles slot) (.base (.barrier ⟨dataGate slot,.inval⟩))

theorem data_iteration_resource_index (a b tiles tile lane) (index : Nat) (event : Wgmma.Event)
    (he : (dataIterationEvents a b tiles tile lane)[index]? = some event) (hr : isResourceEvent event = true) :
    index = 0 ∨ (needsPrefetch tile tiles (HopperStage.leader lane) ∧ (index = 1 ∨ index = 2 ∨ index = 3)) := by
  have hi := (List.getElem?_eq_some_iff.mp he).1
  rw [data_iteration_length] at hi
  by_cases hn : needsPrefetch tile tiles (HopperStage.leader lane)
  · have hb : index < 10 := by simpa only [dataPreludeLength,ite_eq_left hn] using hi
    interval_cases index
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr ⟨hn,by omega⟩
      | (simp only [dataIterationEvents,iterationEvents,List.replicate_zero,List.nil_append,preludeEvents,ite_eq_left hn,
          prefetchTransferEvents,computeEvents,advanceEvents,List.cons_append,List.nil_append,
          List.getElem?_cons_succ,List.getElem?_cons_zero] at he
         cases he
         cases hr)
  · have hb : index < 7 := by simpa only [dataPreludeLength,ite_eq_right hn] using hi
    interval_cases index
    all_goals first
      | exact Or.inl rfl
      | (simp only [dataIterationEvents,iterationEvents,List.replicate_zero,List.nil_append,preludeEvents,ite_eq_right hn,
          computeEvents,advanceEvents,List.cons_append,List.nil_append,
          List.getElem?_cons_succ,List.getElem?_cons_zero] at he
         cases he
         cases hr)

theorem data_iteration_expect_at (a b tiles tile) (ht : tile+1 < tiles) :
    (dataIterationEvents a b tiles tile 0)[1]? =
      some (.base (.barrier ⟨dataGate (stage (tile+1)),.arriveExpectTx 2304⟩)) := by
  have hn : needsPrefetch tile tiles (HopperStage.leader 0) := ⟨ht,rfl⟩
  simp only [dataIterationEvents,iterationEvents,List.replicate_zero,List.nil_append,preludeEvents,ite_eq_left hn,
    prefetchTransferEvents,List.cons_append,List.nil_append,List.getElem?_cons_succ,List.getElem?_cons_zero]
  rfl

theorem data_iteration_resource_case (a b tiles tile lane) (ht : tile < tiles) (hb : tiles ≤ 2^28)
    (index : Nat) (event : Wgmma.Event)
    (he : (dataIterationEvents a b tiles tile lane)[index]? = some event) (hr : isResourceEvent event = true) :
    DataResourceSource a b tiles ⟨(ctx tiles lane).id,dataTileStart a b tiles tile lane+index⟩ event := by
  rcases data_iteration_resource_index a b tiles tile lane index event he hr with rfl | ⟨hn,hindex⟩
  · have hv := data_iteration_wait_at a b tiles tile lane
    rw [he] at hv
    cases Option.some.inj hv
    simpa only [Nat.add_zero,dataWaitId] using DataResourceSource.wait tile lane ht
  · have hl : lane = 0 := (leader_iff_zero lane).mp hn.2
    subst lane
    have hz : tile+1 ≠ 0 := by omega
    rcases hindex with rfl | rfl | rfl
    · have hv := data_iteration_expect_at a b tiles tile hn.1
      rw [he] at hv
      cases Option.some.inj hv
      simpa only [dataExpectId,hz,ite_false,Nat.add_sub_cancel] using DataResourceSource.expect (a := a) (b := b) (tile+1) hn.1
    · have hv := data_iteration_copy_a_at a b tiles tile hn.1 hb
      rw [he] at hv
      cases Option.some.inj hv
      simpa only [dataCopyAId,hz,ite_false,Nat.add_sub_cancel] using DataResourceSource.copyA (a := a) (b := b) (tile+1) hn.1
    · have hv := data_iteration_copy_b_at a b tiles tile hn.1 hb
      rw [he] at hv
      cases Option.some.inj hv
      simpa only [dataCopyBId,hz,ite_false,Nat.add_sub_cancel] using DataResourceSource.copyB (a := a) (b := b) (tile+1) hn.1

end
end Ptx.Kernels.HopperDoubleBuffer
