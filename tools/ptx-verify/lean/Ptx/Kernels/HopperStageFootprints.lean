import Ptx.Kernels.HopperStageNativeInputs
import Ptx.Hopper.UnifiedFootprints

namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def eventFootprint (event : Hopper.Event) : Option (Location × Nat) :=
  (match event with | .ampere (.ordinary k) => some k | _ => none).bind Ptx.Event.Kind.footprint
def wordAddress (lane : Wgmma.Lane) (slot : Wgmma.Slot) : Nat := wrap 64 (outFinal lane+storeOffset slot)
theorem trace_source_footprints (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    (trace a b lane).view.events.filterMap eventFootprint =
      List.ofFn (fun slot : Wgmma.Slot => (⟨.global,wordAddress lane slot⟩,4)) := by
  change ((middleEvents a b lane (leader lane)++(nativeEvents a b lane (leader lane)++
    (storeResult a b lane (leader lane)).2)).map Unified.eventView).filterMap eventFootprint = _
  rw [actual_store_events]
  cases leader lane <;> simp [middleEvents,nativeEvents,storedEvents,Unified.eventView,eventFootprint,
    Ptx.Event.Kind.footprint,Symbolic.encode_length,wordAddress,storeOffset]
  all_goals rfl
theorem source_footprint_shape {a b event base size}
    (hf : (Access.kind Tma.localShared Access.globalDescriptor (candidate a b).view (.tma (.source event))).bind Ptx.Event.Kind.footprint = some (base,size)) :
    ∃ lane slot, base = ⟨.global,wordAddress lane slot⟩ ∧ size = 4 := by
  cases he : (candidate a b).view.eventAt event with
  | none => simp [Access.kind,he] at hf
  | some kind =>
    obtain ⟨actual,ht,_,hget⟩ := Hopper.eventAt_trace he
    obtain ⟨rich,hr,rfl⟩ := List.mem_map.mp ht
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp hr
    have hfp : eventFootprint kind = some (base,size) := by
      simp only [Access.kind,he,Option.bind_some] at hf
      cases kind with
      | ampere event => cases event <;> exact hf
      | tmaIssue _ | proxyFenceAsyncShared _ | barrier _ | wgmma _ => exact hf
    have hm := List.mem_filterMap.mpr ⟨kind,List.mem_of_getElem? hget,hfp⟩
    rw [trace_source_footprints] at hm
    obtain ⟨slot,hs⟩ := List.mem_ofFn.mp hm
    have heq := Prod.mk.inj hs
    exact ⟨lane,slot,heq.1.symm,heq.2.symm⟩
theorem word_address_bounds (lane : Wgmma.Lane) (slot : Wgmma.Slot) :
    8192 ≤ wordAddress lane slot ∧ wordAddress lane slot+4 ≤ 10240 ∧ wordAddress lane slot%4 = 0 := by
  have hb := actual_output_bounds lane slot
  refine ⟨hb.1,hb.2,?_⟩
  rw [wordAddress,actual_output_address]
  omega

end
end Ptx.Kernels.HopperStage
