import Ptx.Kernels.HopperStageNativePublication
import Ptx.Hopper.AccessInversion

/-! Exhaustive write inventory, not a chosen RF map. Source stores are global;
there are no non-bulk operations. All shared writers are the two actual TMA
transfers, whose identities follow the source-preserving resource inventory. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def ordinaryWrite (event : Hopper.Event) (loc : Location) : Option Symbolic.Byte :=
  (match event with | .ampere (.ordinary k) => some k | _ => none).bind (fun k => k.writeByte loc)
theorem source_shared_writes_absent (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane)
    (loc : Location) (hl : loc.space = .shared .zero) :
    ∀ event ∈ (trace a b lane).view.events, ordinaryWrite event loc = none := by
  change ∀ event ∈ (middleEvents a b lane (leader lane)++(nativeEvents a b lane (leader lane)++
    (storeResult a b lane (leader lane)).2)).map Unified.eventView, ordinaryWrite event loc = none
  rw [actual_store_events]
  cases hh : leader lane <;> simp [hh,middleEvents,nativeEvents,storedEvents,Unified.eventView,
    ordinaryWrite,Ptx.Event.Kind.writeByte,Ptx.Event.payloadByte,hl]
theorem no_nonbulk (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (event : Ptx.Event.EventId) :
    Access.copyAt (candidate a b).view event = none := by
  cases hc : Access.copyAt (candidate a b).view event with
  | none => rfl
  | some op =>
    obtain ⟨ordinal,he⟩ := Access.nonbulk_has_actual_issue hc
    obtain ⟨actual,ht,_,hget⟩ := Hopper.eventAt_trace he
    obtain ⟨rich,hr,rfl⟩ := List.mem_map.mp ht
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp hr
    have hm := List.mem_of_getElem? hget
    change .ampere (.issue ordinal op) ∈ (middleEvents a b lane (leader lane)++(nativeEvents a b lane (leader lane)++
      (storeResult a b lane (leader lane)).2)).map Unified.eventView at hm
    rw [actual_store_events] at hm
    cases hh : leader lane <;> simp [hh,middleEvents,nativeEvents,storedEvents,Unified.eventView] at hm
theorem ordinary_shared_write_none (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (event : Ptx.Event.EventId)
    (loc : Location) (hl : loc.space = .shared .zero) :
    Access.writeByte Tma.localShared Access.globalDescriptor (candidate a b).view (.tma (.source event)) loc = none := by
  cases he : (candidate a b).view.eventAt event with
  | none => simp [Access.writeByte,Access.kind,he]
  | some kind =>
    obtain ⟨actual,ht,_,hget⟩ := Hopper.eventAt_trace he
    obtain ⟨rich,hr,rfl⟩ := List.mem_map.mp ht
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp hr
    have hn := source_shared_writes_absent a b lane loc hl kind (List.mem_of_getElem? hget)
    simp only [Access.writeByte,Access.kind,he,Option.bind_some]
    cases kind with
    | ampere event => cases event <;> exact hn
    | tmaIssue _ | proxyFenceAsyncShared _ | barrier _ | wgmma _ => exact hn
theorem source_copy_ids {a b id op} (hc : Tma.copyAt (candidate a b).view id = some op) : id = copyId 5 ∨ id = copyId 6 := by
  have hm := Tma.copy_present_mem hc
  rw [← Tma.ResourceErasure.copies_preserved,candidate_resource_erasure,resource_copies] at hm
  simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using hm
theorem shared_writer_is_tensor {a b writer loc value} (hl : loc.space = .shared .zero)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (candidate a b) writer loc = some value) :
    ∃ id offset, writer = .base (.tma (.write id offset)) ∧
      Tma.writeLocation Tma.localShared (candidate a b).view id offset = some loc := by
  cases writer with
  | wgmmaRead issue operand => rw [Unified.native_write_none] at hw; cases hw
  | base node =>
    cases node with
    | copyRead issue | copyWrite issue => simp [Unified.writeByte,Unified.kind,Access.kind,no_nonbulk] at hw
    | tma node =>
      cases node with
      | source event => rw [Unified.base_write_preserved,ordinary_shared_write_none a b event loc hl] at hw; cases hw
      | descriptor id => rw [Unified.base_write_preserved,Access.descriptor_no_write] at hw; cases hw
      | read id offset => rw [Unified.base_write_preserved,Access.tensor_read_no_write] at hw; cases hw
      | notify id => cases hw
      | write id offset =>
        exact ⟨id,offset,rfl,Access.tensor_write_access (.inr (by rw [← Unified.base_write_preserved,hw]; rfl))⟩
theorem tensor_write_id_cases {a b id offset loc}
    (hw : Tma.writeLocation Tma.localShared (candidate a b).view id offset = some loc) : id = copyId 5 ∨ id = copyId 6 := by
  cases hc : Tma.copyAt (candidate a b).view id with
  | none => simp [Tma.writeLocation,hc] at hw
  | some op => exact source_copy_ids hc

end
end Ptx.Kernels.HopperStage
