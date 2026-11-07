import Ptx.Kernels.HopperStageResourceMetadata

namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

theorem resource_inventory_outside {location : Location} (hn : location ≠ gate) :
    Tma.inventory Tma.localShared resourceCandidate location = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro entry he
  have hh := Tma.inventory_iff.mp he
  have hg := resource_locations entry.origin (Tma.origin_mem hh)
  rw [hh] at hg
  exact hn (Option.some.inj hg)
theorem stage_all_histories_valid (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (location : Location) :
    Tma.HistoryValid Tma.localShared (candidate a b).view location (histories location) := by
  by_cases hl : location = gate
  · subst location
    simpa only [histories,ite_true] using stage_history_valid a b
  · refine ⟨by simp only [histories,if_neg hl,List.map_nil,List.nodup_nil],?_,?_,?_⟩
    · rw [← Tma.ResourceErasure.inventory_preserved,candidate_resource_erasure,resource_inventory_outside hl]
      simp only [histories,if_neg hl]
      exact List.Perm.refl []
    · simp only [histories,if_neg hl,Tma.SourceOrder,List.not_mem_nil,false_implies,implies_true]
    · exact ⟨none,by simp only [histories,if_neg hl,List.map_nil]; rfl⟩
theorem trace_events_length (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    (trace a b lane).events.length = if leader lane then 19 else 13 := by
  change (middleEvents a b lane (leader lane)++(nativeEvents a b lane (leader lane)++
    (storeResult a b lane (leader lane)).2)).length = _
  rw [actual_store_events]
  cases leader lane <;> rfl
theorem resource_present_has_lane {id} (hp : resourceCandidate.Present id) :
    ∃ lane : Wgmma.Lane, id.thread = (ctx lane).id ∧ id.serial < (if leader lane then 19 else 13) := by
  obtain ⟨kind,hk⟩ := Option.isSome_iff_exists.mp hp
  obtain ⟨actual,ht,hid,hget⟩ := Hopper.eventAt_trace hk
  obtain ⟨base,hb,rfl⟩ := List.mem_map.mp ht
  obtain ⟨rich,hr,rfl⟩ := List.mem_map.mp hb
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp hr
  refine ⟨lane,hid.symm,?_⟩
  have hs := (List.getElem?_eq_some_iff.mp hget).1
  simpa only [Tma.ResourceErasure.trace,Unified.ThreadTrace.view,List.length_map,trace_events_length] using hs

end
end Ptx.Kernels.HopperStage
