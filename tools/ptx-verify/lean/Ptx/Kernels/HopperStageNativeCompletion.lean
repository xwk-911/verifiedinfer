import Ptx.Kernels.HopperStageNativePublication
import Ptx.Hopper.UnifiedOrderSafety

namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def nativeWaitId (lane : Wgmma.Lane) : Ptx.Event.EventId := ⟨(ctx lane).id,middleLength (leader lane)+2⟩
def nativeWaitMark (lane : Wgmma.Lane) : Wgmma.Mark := ⟨31,3,Ampere.linearThread (ctx lane)/128⟩
theorem actual_native_wait (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    (candidate a b).eventAt (nativeWaitId lane) = some (.wait (nativeWaitMark lane) 1 0 0 1 (queryAt29 (leader lane)+1)) := by
  change (candidate a b).eventAt ⟨(trace a b lane).id,middleLength (leader lane)+2⟩ = _
  rw [Unified.eventAt_of_member (trace_ids_unique a b) (List.mem_ofFn.mpr ⟨lane,rfl⟩)]
  change (middleEvents a b lane (leader lane)++(nativeEvents a b lane (leader lane)++
    (storeResult a b lane (leader lane)).2))[middleLength (leader lane)+2]? = _
  rw [List.getElem?_append_right (by rw [middle_length]; omega),middle_length]
  have hi : middleLength (leader lane)+2-middleLength (leader lane) = 2 := by omega
  rw [hi,List.getElem?_append_left (by change 2 < 3; decide)]
  rfl
theorem actual_native_completed (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    Unified.WgmmaCompletedAt (candidate a b) (mmaId 0) (nativeWaitId lane) := by
  refine ⟨collective a b,lane,nativeWaitMark lane,1,0,0,1,queryAt29 (leader lane)+1,
    actual_native_wait a b lane,rfl,?_,rfl,(by change (1 : Nat) < 3; decide),?_,by decide,by decide,by decide⟩
  · change middleLength (leader lane) < middleLength (leader lane)+2
    omega
  · change 0 < 1
    decide
theorem actual_native_completed_order (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ)
    (lane : Wgmma.Lane) (operand : Wgmma.OperandByte) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor (candidate a b) histories cluster (nativeLocation a b operand)
      (nativeRead operand) (.base (.tma (.source (nativeWaitId lane)))) :=
  Unified.native_completed_byte_order ⟨actual_native_completed a b lane,mmaMark 0,calls a b 0,actual_representative a b,rfl⟩

end
end Ptx.Kernels.HopperStage
