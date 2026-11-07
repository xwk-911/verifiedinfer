import Ptx.Kernels.HopperStageCausalWitness

/-! Source-indexed store footprints. Keeping the serial is necessary to prove
global writer uniqueness; an unindexed multiset of addresses is insufficient. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def indexedFootprint (entry : Hopper.Event × Nat) : Option (Nat × (Location × Nat)) :=
  (eventFootprint entry.1).map (fun footprint => (entry.2,footprint))
theorem trace_indexed_footprints (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    ((trace a b lane).view.events.zipIdx).filterMap indexedFootprint =
      List.ofFn (fun slot : Wgmma.Slot => ((storeId lane slot).serial,(⟨.global,wordAddress lane slot⟩,4))) := by
  change (((middleEvents a b lane (leader lane)++(nativeEvents a b lane (leader lane)++
    (storeResult a b lane (leader lane)).2)).map Unified.eventView).zipIdx).filterMap indexedFootprint = _
  rw [actual_store_events]
  cases hh : leader lane <;> simp [hh,middleEvents,nativeEvents,storedEvents,Unified.eventView,indexedFootprint,
    eventFootprint,List.zipIdx,Ptx.Event.Kind.footprint,Symbolic.encode_length,wordAddress,storeOffset,storeId,middleLength]
  all_goals rfl
theorem source_indexed_footprint_shape {a b event base size}
    (hf : (Access.kind Tma.localShared Access.globalDescriptor (candidate a b).view (.tma (.source event))).bind Ptx.Event.Kind.footprint = some (base,size)) :
    ∃ lane slot, event = storeId lane slot ∧ base = ⟨.global,wordAddress lane slot⟩ ∧ size = 4 := by
  cases he : (candidate a b).view.eventAt event with
  | none => simp [Access.kind,he] at hf
  | some kind =>
    obtain ⟨actual,ht,hid,hget⟩ := Hopper.eventAt_trace he
    obtain ⟨rich,hr,rfl⟩ := List.mem_map.mp ht
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp hr
    have hfp : eventFootprint kind = some (base,size) := by
      simp only [Access.kind,he,Option.bind_some] at hf
      cases kind with
      | ampere event => cases event <;> exact hf
      | tmaIssue _ | proxyFenceAsyncShared _ | barrier _ | wgmma _ => exact hf
    have hm := List.mem_filterMap.mpr ⟨(kind,event.serial),List.mk_mem_zipIdx_iff_getElem?.mpr hget,
      show indexedFootprint (kind,event.serial) = some (event.serial,(base,size)) by simp only [indexedFootprint,hfp,Option.map_some]⟩
    rw [trace_indexed_footprints] at hm
    obtain ⟨slot,hs⟩ := List.mem_ofFn.mp hm
    have hserial := congrArg Prod.fst hs
    have hfoot := Prod.mk.inj (congrArg Prod.snd hs)
    refine ⟨lane,slot,?_,hfoot.1.symm,hfoot.2.symm⟩
    rcases event with ⟨thread,serial⟩
    exact congrArg₂ Ptx.Event.EventId.mk hid.symm hserial.symm

end
end Ptx.Kernels.HopperStage
