import Ptx.Kernels.HopperStageFootprints

/-! Exhaustive access regions of the actual mixed source. This derives
mixed-size compatibility from byte footprints and disjoint initial/output
regions; it does not assume race freedom or any RF value. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def SharedByte (base : Location) (size : Nat) : Prop := base.space = .shared .zero ∧ size = 1
def OutputWord (base : Location) (size : Nat) : Prop :=
  base.space = .global ∧ size = 4 ∧ 8192 ≤ base.address ∧ base.address+4 ≤ 10240 ∧ base.address%4 = 0
def Region (base : Location) (size : Nat) : Prop :=
  SharedByte base size ∨ OutputWord base size ∨
    (base.space = .global ∧ size = 1 ∧ 65536 ≤ base.address) ∨
    (base.space = .global ∧ size = 128 ∧ base.address+128 ≤ 4352)

theorem source_word_region {a b event base size}
    (hf : (Access.kind Tma.localShared Access.globalDescriptor (candidate a b).view (.tma (.source event))).bind Ptx.Event.Kind.footprint = some (base,size)) :
    OutputWord base size := by
  obtain ⟨lane,slot,rfl,rfl⟩ := source_footprint_shape hf
  exact ⟨rfl,rfl,word_address_bounds lane slot⟩
theorem candidate_event_cta_zero {a b id event} (he : (candidate a b).eventAt id = some event) : id.thread.cta = .zero := by
  obtain ⟨actual,ht,hid,_⟩ := Unified.eventAt_trace he
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
  rw [← hid]
  rfl
theorem tensor_write_shared_space {a b id offset loc}
    (hw : Tma.writeLocation Tma.localShared (candidate a b).view id offset = some loc) : loc.space = .shared .zero := by
  rcases tensor_write_id_cases hw with rfl | rfl
  · simp only [Tma.writeLocation,actual_copy_a,Option.bind_some] at hw
    split at hw
    · exact (congrArg Location.space (Option.some.inj hw)).symm
    · cases hw
  · simp only [Tma.writeLocation,actual_copy_b,Option.bind_some] at hw
    split at hw
    · exact (congrArg Location.space (Option.some.inj hw)).symm
    · cases hw
theorem tensor_write_footprint {a b id offset base size}
    (hf : (Access.kind Tma.localShared Access.globalDescriptor (candidate a b).view (.tma (.write id offset))).bind Ptx.Event.Kind.footprint = some (base,size)) :
    SharedByte base size := by
  cases hk : Access.kind Tma.localShared Access.globalDescriptor (candidate a b).view (.tma (.write id offset)) with
  | none => simp [hk] at hf
  | some k =>
    obtain ⟨loc,value,hl,_,rfl⟩ := Access.tensor_write_shape hk
    have he : loc = base ∧ 1 = size := by simpa only [hk,Option.bind_some,Ptx.Event.Kind.footprint,List.length_singleton,Option.some.injEq,Prod.mk.injEq] using hf
    exact ⟨he.1 ▸ tensor_write_shared_space hl,he.2.symm⟩
theorem all_footprint_regions {a b node base size}
    (hf : (Unified.kind Tma.localShared Access.globalDescriptor (candidate a b) node).bind Ptx.Event.Kind.footprint = some (base,size)) : Region base size := by
  cases node with
  | wgmmaRead issue operand =>
    cases he : (candidate a b).representativeAt issue with
    | none => simp [Unified.kind,he] at hf
    | some pair =>
      have hc := candidate_event_cta_zero (Unified.representative_at he).1
      have hh : Wgmma.operandLocation issue.thread.cta pair.2 operand = base ∧ 1 = size := by
        simpa only [Unified.kind,he,Option.map_some,Option.bind_some,Wgmma.operandKind,Ptx.Event.Kind.footprint,List.length_singleton,Option.some.injEq,Prod.mk.injEq] using hf
      apply Or.inl
      refine ⟨?_,hh.2.symm⟩
      rw [← hh.1]
      cases operand <;> simpa only [Wgmma.operandLocation,hc]
  | base node =>
    cases node with
    | copyRead issue | copyWrite issue => simp [Unified.kind,Access.kind,no_nonbulk] at hf
    | tma node =>
      cases node with
      | source event => exact .inr (.inl (source_word_region hf))
      | notify id => cases hf
      | write id offset => exact .inl (tensor_write_footprint hf)
      | descriptor id =>
        cases hc : Tma.copyAt (candidate a b).view id with
        | none => simp [Unified.kind,Access.kind,hc] at hf
        | some op =>
          rcases source_copy_ids hc with rfl | rfl
          · have he : (⟨.global,4096⟩ : Location) = base ∧ 128 = size := by
              simpa only [Unified.kind,Access.kind,actual_copy_a,Option.map_some,Option.bind_some,Ptx.Event.Kind.footprint,TensorMap.encode_length,Access.globalDescriptor,copyA,Prod.mk.injEq] using (Option.some.inj hf)
            rcases he with ⟨rfl,rfl⟩
            exact .inr (.inr (.inr ⟨rfl,rfl,by decide⟩))
          · have he : (⟨.global,4224⟩ : Location) = base ∧ 128 = size := by
              simpa only [Unified.kind,Access.kind,actual_copy_b,Option.map_some,Option.bind_some,Ptx.Event.Kind.footprint,TensorMap.encode_length,Access.globalDescriptor,copyB,Prod.mk.injEq] using (Option.some.inj hf)
            rcases he with ⟨rfl,rfl⟩
            exact .inr (.inr (.inr ⟨rfl,rfl,by decide⟩))
      | read id offset =>
        cases hk : Access.kind Tma.localShared Access.globalDescriptor (candidate a b).view (.tma (.read id offset)) with
        | none => simp [Unified.kind,hk] at hf
        | some k =>
          obtain ⟨loc,value,hl,_,rfl⟩ := Access.tensor_read_shape hk
          have he : loc = base ∧ 1 = size := by
            simpa only [Unified.kind,hk,Option.bind_some,Ptx.Event.Kind.footprint,List.length_singleton,Option.some.injEq,Prod.mk.injEq] using hf
          rcases he with ⟨rfl,rfl⟩
          cases hc : Tma.copyAt (candidate a b).view id with
          | none => simp [Tma.readLocation,hc] at hl
          | some op =>
            have hs : Tma.sourceByte op.descriptor op.coordinates offset = some loc := by simpa only [Tma.readLocation,hc,Option.bind_some] using hl
            obtain ⟨_,_,hg,ha⟩ := Tma.source_byte_some hs
            apply Or.inr; apply Or.inr; apply Or.inl
            refine ⟨hg,rfl,?_⟩
            rcases source_copy_ids hc with rfl | rfl
            · have hop : op = copyA a := Option.some.inj (hc.symm.trans (actual_copy_a a b))
              rw [hop] at ha
              dsimp only [copyA,aView] at ha
              omega
            · have hop : op = copyB b := Option.some.inj (hc.symm.trans (actual_copy_b a b))
              rw [hop] at ha
              dsimp only [copyB,bView] at ha
              omega
theorem write_footprint_regions {a b node loc value}
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (candidate a b) node loc = some value) :
    ∃ base size, (Unified.kind Tma.localShared Access.globalDescriptor (candidate a b) node).bind Ptx.Event.Kind.footprint = some (base,size) ∧
      (SharedByte base size ∨ OutputWord base size) := by
  obtain ⟨base,size,hf⟩ := Unified.access_footprint_exists (.inr (by rw [hw]; rfl))
  refine ⟨base,size,hf,?_⟩
  cases node with
  | wgmmaRead issue operand => rw [Unified.native_write_none] at hw; cases hw
  | base node =>
    cases node with
    | copyRead issue | copyWrite issue => simp [Unified.kind,Access.kind,no_nonbulk] at hf
    | tma node =>
      cases node with
      | source event => exact .inr (source_word_region hf)
      | write id offset => exact .inl (tensor_write_footprint hf)
      | descriptor id => rw [Unified.base_write_preserved,Access.descriptor_no_write] at hw; cases hw
      | read id offset => rw [Unified.base_write_preserved,Access.tensor_read_no_write] at hw; cases hw
      | notify id => cases hw

end
end Ptx.Kernels.HopperStage
