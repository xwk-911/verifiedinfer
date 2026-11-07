import Ptx.Kernels.HopperDoubleBufferWholeCoverage

/-! Exhaustive actual-byte to joint-use correspondence. Non-bulk copies are
excluded by the source program, not silently omitted from the inventory.
-/
namespace Ptx.Kernels.HopperDoubleBuffer.Whole
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

theorem actual_read_use {tiles initial candidate node loc value} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hr : Unified.readByte Tma.localShared Access.globalDescriptor candidate node loc = some value) :
    ∃ work, Use candidate work (Unified.memoryControlNode node) loc .read := by
  cases node with
  | wgmmaRead issue operand =>
    cases he : candidate.representativeAt issue with
    | none => simp [Unified.readByte,Unified.kind,he] at hr
    | some pair =>
      have hp : Ptx.Event.payloadByte (Wgmma.operandLocation issue.thread.cta pair.2 operand) [pair.2.operandBytes operand.index] loc = some value := by
        simpa [Unified.readByte,Unified.kind,he,Wgmma.operandKind,Ptx.Event.Kind.readByte] using hr
      obtain ⟨rfl,_⟩ := Access.singleton_payload hp
      exact ⟨.native issue,.async (.nativeRead he)⟩
  | base node =>
    cases node with
    | copyRead issue | copyWrite issue =>
      simp [Unified.readByte,Unified.kind,Access.kind,candidate_no_nonbulk hb hw hc] at hr
    | tma node =>
      cases node with
      | source id => exact ⟨.kernel,.kernel (ordinary_read_use hr)⟩
      | descriptor id =>
        cases he : Tma.copyAt candidate.view id with
        | none => simp [Unified.readByte,Unified.kind,Access.kind,he] at hr
        | some op =>
          have hp : Ptx.Event.payloadByte (Access.globalDescriptor id.issue.thread op.descriptorAddress) (TensorMap.encode op.descriptor) loc = some value := by
            simpa [Unified.readByte,Unified.kind,Access.kind,he,Ptx.Event.Kind.readByte] using hr
          obtain ⟨hspace,hlo,hhi⟩ := Ptx.Event.payloadByte_bounds hp
          rw [TensorMap.encode_length] at hhi
          let offset := loc.address-op.descriptorAddress
          have hbound : offset < 128 := by dsimp [offset] at *; simp only [Access.globalDescriptor] at hlo hhi; omega
          have hloc : (Access.globalDescriptor id.issue.thread op.descriptorAddress).add offset = loc := by
            cases loc with
            | mk space address =>
              simp only [Access.globalDescriptor,Location.add,Location.mk.injEq] at *
              exact ⟨hspace,by dsimp [offset]; omega⟩
          exact ⟨.tma id,by rw [← hloc]; exact .async (.descriptor he hbound)⟩
      | read id offset =>
        cases hl : Tma.readLocation candidate.view id offset with
        | none => simp [Unified.readByte,Unified.kind,Access.kind,hl] at hr
        | some actual =>
          cases hv : Tma.transferByte candidate.view id offset with
          | none => simp [Unified.readByte,Unified.kind,Access.kind,hl,hv] at hr
          | some byte =>
            have hp : Ptx.Event.payloadByte actual [byte] loc = some value := by
              simpa [Unified.readByte,Unified.kind,Access.kind,hl,hv,Ptx.Event.Kind.readByte] using hr
            obtain ⟨rfl,_⟩ := Access.singleton_payload hp
            exact ⟨.tma id,.async (.tmaRead hl hv)⟩
      | write id offset =>
        cases hl : Tma.writeLocation Tma.localShared candidate.view id offset <;>
          cases hv : Tma.transferByte candidate.view id offset <;>
          simp [Unified.readByte,Unified.kind,Access.kind,hl,hv,Ptx.Event.Kind.readByte] at hr
      | notify id => simp [Unified.readByte,Unified.kind,Access.kind] at hr

theorem actual_write_use {tiles initial candidate node loc value} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hr : Unified.writeByte Tma.localShared Access.globalDescriptor candidate node loc = some value) :
    ∃ work, Use candidate work (Unified.memoryControlNode node) loc .write := by
  cases node with
  | wgmmaRead issue operand => rw [Unified.native_write_none] at hr; cases hr
  | base node =>
    cases node with
    | copyRead issue | copyWrite issue =>
      simp [Unified.writeByte,Unified.kind,Access.kind,candidate_no_nonbulk hb hw hc] at hr
    | tma node =>
      cases node with
      | source id => exact ⟨.kernel,.kernel (ordinary_write_use hr)⟩
      | descriptor id => rw [Unified.base_write_preserved,Access.descriptor_no_write] at hr; cases hr
      | read id offset => rw [Unified.base_write_preserved,Access.tensor_read_no_write] at hr; cases hr
      | write id offset =>
        cases hl : Tma.writeLocation Tma.localShared candidate.view id offset with
        | none => simp [Unified.writeByte,Unified.kind,Access.kind,hl] at hr
        | some actual =>
          cases hv : Tma.transferByte candidate.view id offset with
          | none => simp [Unified.writeByte,Unified.kind,Access.kind,hl,hv] at hr
          | some byte =>
            have hp : Ptx.Event.payloadByte actual [byte] loc = some value := by
              simpa [Unified.writeByte,Unified.kind,Access.kind,hl,hv,Ptx.Event.Kind.writeByte] using hr
            obtain ⟨rfl,_⟩ := Access.singleton_payload hp
            exact ⟨.tma id,.async (.tmaWrite hl hv)⟩
      | notify id => simp [Unified.writeByte,Unified.kind,Access.kind] at hr

theorem actual_access_covered {tiles initial candidate node loc} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hc : Unified.Complete candidate) (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (ha : Unified.Accesses Tma.localShared Access.globalDescriptor candidate node loc) :
    ∃ binding ∈ bindings family, binding.region.Contains loc := by
  rcases ha with hr | hw'
  · obtain ⟨value,hvalue⟩ := Option.isSome_iff_exists.mp hr
    obtain ⟨work,hu⟩ := actual_read_use hb hw hc hvalue
    obtain ⟨binding,hm,_,_,hregion⟩ := all_uses_covered family ht hb hw hc hd _ _ _ _ hu
    exact ⟨binding,hm,hregion⟩
  · obtain ⟨value,hvalue⟩ := Option.isSome_iff_exists.mp hw'
    obtain ⟨work,hu⟩ := actual_write_use hb hw hc hvalue
    obtain ⟨binding,hm,_,_,hregion⟩ := all_uses_covered family ht hb hw hc hd _ _ _ _ hu
    exact ⟨binding,hm,hregion⟩

theorem actual_resource_storage_covered {tiles initial candidate origin event offset} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hc : Unified.Complete candidate) (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (he : Tma.resourceAt Tma.localShared candidate.view origin = some event) (ho : offset < 8) :
    ∃ binding ∈ bindings family, binding.work = .kernel ∧ binding.mode = .write ∧ binding.region.Contains (event.location.add offset) :=
  all_uses_covered family ht hb hw hc hd _ _ _ _ (.kernel (.resource he ho))

theorem public_pending_actual_access_rejected {tiles initial candidate node loc} (family : ReplySourceFamily tiles candidate)
    (values : List Nat) (hv : values.length = 10) (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) {histories state target region}
    (hs : Bridge.Steps HopperStage.block Tma.localShared candidate histories dataCluster (plan family)
      ⟨prepared values tiles,fun _ => False⟩ state)
    (ha : Unified.Accesses Tma.localShared Access.globalDescriptor candidate node loc)
    (hp : ¬state.done (Unified.memoryControlNode node))
    (hl : layout tiles target = some region) (hcontains : region.Contains loc) :
    Ptx.Async.reclaim state.protocol target = .error .outstandingLoan ∧
      ∀ value, Ptx.Async.hostWrite state.protocol target value = .error .outstandingLoan := by
  rcases ha with hr | hw'
  · obtain ⟨value,hvalue⟩ := Option.isSome_iff_exists.mp hr
    obtain ⟨work,hu⟩ := actual_read_use hb hw hc hvalue
    exact public_pending_reclaim_write_rejected family values hv ht hb hw hc hd hs hu hp hl hcontains
  · obtain ⟨value,hvalue⟩ := Option.isSome_iff_exists.mp hw'
    obtain ⟨work,hu⟩ := actual_write_use hb hw hc hvalue
    exact public_pending_reclaim_write_rejected family values hv ht hb hw hc hd hs hu hp hl hcontains

end
end Ptx.Kernels.HopperDoubleBuffer.Whole
