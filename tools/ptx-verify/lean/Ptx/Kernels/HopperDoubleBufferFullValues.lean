import Ptx.Kernels.HopperDoubleBufferPublicValues
import Ptx.Kernels.HopperDoubleBufferZeroPublicValues

/-! One bounded-K native client contract, including zero K. Zero K uses only
output/barrier reservations; positive K uses the existing ten-region plan.
Both branches execute the same generated PTX source through their checked
source candidates, with the same independent real GEMM specification.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris.ProgramLogic
noncomputable section

def fullValueBufferCount (tiles : Nat) := if tiles = 0 then 2 else 10
def fullValueCandidate (a b tiles schedules) := if tiles = 0 then zeroCandidate else retryDataCandidate a b tiles schedules
def fullValueContext (a b tiles schedules) :=
  if tiles = 0 then zeroValuePreparationContext zeroCandidate else preparationContext (retryDataFamily a b tiles schedules)
def fullValueInitialState (a b tiles schedules frame values) :=
  if tiles = 0 then zeroValueInitialState zeroCandidate frame (Ptx.Async.initial 1 values)
  else retryValueInitialState a b tiles schedules frame (Ptx.Async.initial 1 values)
def fullValueActions (tiles : Nat) (actions : List ByteContentsHeap.Action) :=
  if tiles = 0 then zeroValuePublicActions actions else publicValueActions tiles actions
def fullValueReturned (values : List Nat) (tiles : Nat) :=
  if tiles = 0 then zeroValueReturned values else Whole.returned values tiles

theorem full_value_output_of_run {a b tiles schedules frame values actions final} (hb : tiles ≤ 2^28)
    (hr : IrisExecution.run (ByteContentsPreparation.transition (fullValueContext a b tiles schedules)) actions
      (fullValueInitialState a b tiles schedules frame values) = .ok final)
    (hc : final.coupled.done = Present (fullValueCandidate a b tiles schedules))
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    ByteContents.valueAt final ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      some (.realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val) := by
  by_cases hz : tiles = 0
  · subst tiles
    have hw : Unified.WellFormed code (completeLaunch 0 frame) zeroCandidate :=
      data_source_well_formed (fun _ _ => 0) (fun _ _ => 0) 0 frame (by decide)
    have hs : IrisExecution.run (ByteContentsPreparation.transition (zeroValuePreparationContext zeroCandidate)) actions
        (zeroValueInitialState zeroCandidate frame (Ptx.Async.initial 1 values)) = .ok final := by
      simpa only [fullValueContext,fullValueInitialState,ite_true] using hr
    have hcut : final.coupled.done = Present zeroCandidate := by simpa only [fullValueCandidate,ite_true] using hc
    simpa only [specification,Finset.range_zero,Finset.sum_empty] using
      zero_value_public_output_of_run hw (data_candidate_local _ _ 0 (by decide)) hs hcut lane slot index
  · have hs : IrisExecution.run (ByteContentsPreparation.transition (preparationContext (retryDataFamily a b tiles schedules))) actions
        (retryValueInitialState a b tiles schedules frame (Ptx.Async.initial 1 values)) = .ok final := by
      simpa only [fullValueContext,fullValueInitialState,hz,ite_false] using hr
    have hcut : final.coupled.done = Present (retryDataCandidate a b tiles schedules) := by simpa only [fullValueCandidate,hz,ite_false] using hc
    exact retry_data_public_value_output_of_run (Nat.pos_of_ne_zero hz) hb hs hcut lane slot index

theorem full_value_native_witness (a b tiles schedules frame values)
    (hv : values.length = fullValueBufferCount tiles) (hb : tiles ≤ 2^28) :
    ∃ actions final,
      IrisExecution.run (ByteContentsPreparation.transition (fullValueContext a b tiles schedules)) (fullValueActions tiles actions)
        (fullValueInitialState a b tiles schedules frame values) = .ok final ∧
      final.coupled = ⟨fullValueReturned values tiles,Present (fullValueCandidate a b tiles schedules)⟩ ∧ ByteContentsHeap.Available final ∧
      Ptx.Async.Drain.Returned final.coupled.protocol ∧ Ptx.Async.Preparation.Live final.coupled.protocol ∧
      (∀ (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4), ByteContents.valueAt final ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
        some (.realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val)) ∧
      (∀ bid, bid < fullValueBufferCount tiles → (∃ next, Ptx.Async.reclaim final.coupled.protocol bid = .ok next) ∧
        ∀ value, ∃ next, Ptx.Async.hostWrite final.coupled.protocol bid value = .ok next) ∧
      adequate .NotStuck (ByteContentsPreparation.script (fullValueContext a b tiles schedules) (fullValueActions tiles actions))
        (fullValueInitialState a b tiles schedules frame values) (fun result _ => result = .ok final) := by
  by_cases hz : tiles = 0
  · subst tiles
    have hv' : values.length = 2 := by simpa only [fullValueBufferCount,ite_true] using hv
    have hw : Unified.WellFormed code (completeLaunch 0 frame) zeroCandidate :=
      data_source_well_formed (fun _ _ => 0) (fun _ _ => 0) 0 frame (by decide)
    have hc : Unified.Complete zeroCandidate := data_candidate_local _ _ 0 (by decide)
    obtain ⟨actions,final,hr,hcut,ha,hrtn,hlive,hm,hreuse,_⟩ := zero_value_public_witness values hv' hw hc
    have hrun : IrisExecution.run (ByteContentsPreparation.transition (fullValueContext a b 0 schedules)) (fullValueActions 0 actions)
        (fullValueInitialState a b 0 schedules frame values) = .ok final := by
      simpa only [fullValueContext,fullValueActions,fullValueInitialState,ite_true] using hr
    refine ⟨actions,final,hrun,?_,ha,hrtn,hlive,?_,?_,ByteContentsPreparation.script_adequate _ _ _ _ hrun⟩
    · simpa only [fullValueReturned,fullValueCandidate,ite_true] using hcut
    · intro lane slot index
      simpa only [specification,Finset.range_zero,Finset.sum_empty] using hm lane slot index
    · simpa only [fullValueBufferCount,ite_true] using hreuse
  · have ht : 0 < tiles := Nat.pos_of_ne_zero hz
    have hv' : values.length = 10 := by simpa only [fullValueBufferCount,hz,ite_false] using hv
    obtain ⟨actions,final,hr,hcut,ha,hrtn,hlive,hm,hreuse,_⟩ := retry_data_public_value_witness a b tiles schedules frame values hv' ht hb
    have hrun : IrisExecution.run (ByteContentsPreparation.transition (fullValueContext a b tiles schedules)) (fullValueActions tiles actions)
        (fullValueInitialState a b tiles schedules frame values) = .ok final := by
      simpa only [fullValueContext,fullValueActions,fullValueInitialState,hz,ite_false] using hr
    refine ⟨actions,final,hrun,?_,ha,hrtn,hlive,hm,?_,ByteContentsPreparation.script_adequate _ _ _ _ hrun⟩
    · simpa only [fullValueReturned,fullValueCandidate,hz,ite_false] using hcut
    · simpa only [fullValueBufferCount,hz,ite_false] using hreuse

end
end Ptx.Kernels.HopperDoubleBuffer
