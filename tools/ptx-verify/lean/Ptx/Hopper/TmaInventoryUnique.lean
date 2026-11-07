import Ptx.Hopper.TmaResources

/-! Resource inventories preserve unique actual event origins. The lemmas
make no assertion of protocol, control, memory or source production admission. -/
namespace Ptx.Hopper.Tma
open Ptx.ISA
noncomputable section

theorem event_ids_unique {c : Candidate} (hu : (c.traces.map ThreadTrace.id).Nodup) : c.eventIds.Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro trace _
    exact List.nodup_range.map (fun _ _ he => congrArg Ptx.Event.EventId.serial he)
  · have hp : c.traces.Pairwise (fun left right => left.id ≠ right.id) := List.pairwise_map.mp hu
    apply hp.imp
    intro left right hne
    apply List.disjoint_left.mpr
    intro event hl hr
    obtain ⟨i,_,hi⟩ := List.mem_map.mp hl
    obtain ⟨j,_,hj⟩ := List.mem_map.mp hr
    exact hne (congrArg Ptx.Event.EventId.thread (hi.trans hj.symm))

theorem barrier_source_origins_unique {c : Candidate} (hu : c.eventIds.Nodup) :
    (c.barrierRecords.map (fun record => Origin.source record.id)).Nodup := by
  simp only [Candidate.barrierRecords,List.map_filterMap,Option.map_map,Function.comp_def]
  apply hu.filterMap
  intro left right origin hl hr
  cases ha : c.barrierAt left with
  | none => simp [ha] at hl
  | some a =>
    cases hb : c.barrierAt right with
    | none => simp [hb] at hr
    | some b =>
      simp only [ha,hb,Option.map_some,Option.mem_some_iff] at hl hr
      exact Origin.source.inj (hl.trans hr.symm)

theorem copy_notification_origins_unique {c : Candidate} (hu : c.eventIds.Nodup) :
    ((copies c).map Origin.notification).Nodup := by
  simp only [copies,List.map_filterMap]
  apply hu.filterMap
  intro left right origin hl hr
  cases ha : c.eventAt left <;> cases hb : c.eventAt right <;> simp only [ha,hb] at hl hr
  all_goals try {simp at hl; done}
  all_goals try {simp at hr; done}
  all_goals
    rename_i a b
    cases a <;> cases b <;> simp_all only [Option.map_some,Option.map_none,Option.mem_some_iff,Option.not_mem_none]
    have he := Origin.notification.inj (hl.trans hr.symm)
    exact congrArg (fun id : CopyId => id.issue) he

theorem origins_unique {c : Candidate} (hu : c.eventIds.Nodup) : (origins c).Nodup := by
  rw [origins,List.nodup_append]
  refine ⟨barrier_source_origins_unique hu,copy_notification_origins_unique hu,?_⟩
  intro left hl right hr
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp hl
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp hr
  simp

theorem inventory_origins_unique {resolve c loc} (hu : (origins c).Nodup) :
    ((inventory resolve c loc).map Entry.origin).Nodup := by
  simp only [inventory,List.map_filterMap]
  apply hu.filterMap
  intro left right origin hl hr
  cases ha : resourceAt resolve c left with
  | none => simp [ha] at hl
  | some a =>
    cases hb : resourceAt resolve c right with
    | none => simp [hb] at hr
    | some b =>
      simp only [ha,hb,Option.bind_some] at hl hr
      split at hl <;> split at hr <;> simp_all only [Option.map_some,Option.map_none,Option.mem_some_iff,Option.not_mem_none]

theorem inventory_unique {resolve c loc} (hu : (c.traces.map ThreadTrace.id).Nodup) :
    (inventory resolve c loc).Nodup :=
  List.Nodup.of_map Entry.origin (inventory_origins_unique (origins_unique (event_ids_unique hu)))

end
end Ptx.Hopper.Tma
