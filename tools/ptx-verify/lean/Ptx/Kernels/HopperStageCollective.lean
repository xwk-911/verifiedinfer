import Ptx.Kernels.HopperStageSource
import Ptx.Hopper.UnifiedCollective

/-! All 128 actual MMA events belong to one source-matched collective. Queries
may differ between leader/peers; the operation PC, sequence, warpgroup,
descriptors and group/ordinal match. Resource/memory admission remains separate.
-/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def middleLength (isLeader : Bool) : Nat := if isLeader then 9 else 4
def mmaId (lane : Wgmma.Lane) : Ptx.Event.EventId := ⟨(ctx lane).id,middleLength (leader lane)⟩
def mmaMark (lane : Wgmma.Lane) : Wgmma.Mark := ⟨29,1,Ampere.linearThread (ctx lane)/128⟩
def calls (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) : Wgmma.Call := stageCall a b lane (leader lane)
theorem middle_length (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) :
    (middleEvents a b lane isLeader).length = middleLength isLeader := by cases isLeader <;> rfl
theorem actual_mma_event (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    (candidate a b).eventAt (mmaId lane) = some (.mma (mmaMark lane) (calls a b lane)) := by
  change (candidate a b).eventAt ⟨(trace a b lane).id,middleLength (leader lane)⟩ = _
  rw [Unified.eventAt_of_member (trace_ids_unique a b) (List.mem_ofFn.mpr ⟨lane,rfl⟩)]
  change (middleEvents a b lane (leader lane)++(nativeEvents a b lane (leader lane)++
    (storeResult a b lane (leader lane)).2))[middleLength (leader lane)]? = _
  rw [← middle_length a b lane (leader lane),List.getElem?_append_right (by omega)]
  simp only [Nat.sub_self,nativeEvents,List.cons_append,List.getElem?_cons_zero,mmaMark,calls]
theorem ctx_linear (lane : Wgmma.Lane) : Ampere.linearThread (ctx lane) = lane.val := by
  have := lane.isLt
  dsimp [Ampere.linearThread,ctx,block,tid]
  omega
theorem call_lane (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) : (calls a b lane).lane = lane := by
  apply Fin.ext
  change Ampere.linearThread (ctx lane)%128 = lane.val
  rw [ctx_linear,Nat.mod_eq_of_lt lane.isLt]
theorem mark_same (lane : Wgmma.Lane) : mmaMark lane = mmaMark 0 := by
  have hz : lane.val/128 = 0 := Nat.div_eq_of_lt lane.isLt
  simp only [mmaMark,ctx_linear,hz]
  rfl
theorem calls_cohort (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) : Wgmma.Cohort (calls a b) :=
  ⟨call_lane a b,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩
def collective (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) : Unified.Collective (candidate a b) (mmaId 0) := {
  calls := calls a b
  marks := mmaMark
  sources := mmaId
  representative := rfl
  matched := actual_mma_event a b
  sameCTA := fun _ => rfl
  sameMark := mark_same
  cohort := calls_cohort a b
}
theorem actual_representative (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    (candidate a b).representativeAt (mmaId 0) = some (mmaMark 0,calls a b 0) :=
  Unified.collective_representative (collective a b)
theorem actual_members_distinct (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) : Function.Injective mmaId :=
  Unified.collective_member_ids_unique (collective a b)

end
end Ptx.Kernels.HopperStage
