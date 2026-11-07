import Ptx.Hopper.ByteContentsControl

/-! A checked memory representative for each unified source control. Actual
nonbulk effects must be absent: two nonbulk ports share their source control
and cannot be silently compressed into one value event.
-/
namespace Ptx.Hopper.ByteContents
open Ptx.ISA Ptx.Hopper.Progress
noncomputable section

def memoryOfControl : Unified.ControlNode → Option Unified.Node
  | .base node => some (.base (.tma node))
  | .arrival _ => none
  | .operand issue operand => some (.wgmmaRead issue operand)

theorem memoryOfControl_actual {control memory} (he : memoryOfControl control = some memory) : Unified.memoryControlNode memory = control := by
  cases control <;> cases he <;> rfl

theorem memoryOfControl_effect {candidate memory}
    (hn : ∀ id, Access.copyAt candidate.view id = none)
    (he : ∃ loc value, readByte candidate memory loc = some value ∨ writeByte candidate memory loc = some value) :
    memoryOfControl (Unified.memoryControlNode memory) = some memory := by
  cases memory with
  | wgmmaRead issue operand => rfl
  | base node =>
    cases node with
    | tma node => rfl
    | copyRead id | copyWrite id =>
      simp [readByte,writeByte,Unified.readByte,Unified.writeByte,Unified.kind,Access.kind,hn] at he

theorem memoryOfControl_complete {candidate control memory}
    (hn : ∀ id, Access.copyAt candidate.view id = none) (hm : memoryOfControl control = some memory) : CompleteAt candidate memory := by
  intro other hc he
  have ho := memoryOfControl_effect hn he
  rw [hc,memoryOfControl_actual hm,hm] at ho
  exact (Option.some.inj ho).symm

theorem actual_read_use {candidate memory loc value}
    (hn : ∀ id, Access.copyAt candidate.view id = none)
    (hr : readByte candidate memory loc = some value) : ByteAuthority.Uses candidate (Unified.memoryControlNode memory) loc .read := by
  cases memory with
  | wgmmaRead issue operand =>
    obtain ⟨mark,call,he,rfl,_⟩ := Unified.native_read_location hr
    exact ⟨.native issue,.async (.nativeRead he)⟩
  | base node =>
    cases node with
    | copyRead id | copyWrite id => simp [readByte,Unified.readByte,Unified.kind,Access.kind,hn] at hr
    | tma node =>
      cases node with
      | source id => exact ⟨.kernel,.kernel (ordinary_read_use hr)⟩
      | notify id => cases hr
      | write id offset =>
        cases hl : Tma.writeLocation Tma.localShared candidate.view id offset <;>
          cases hv : Tma.transferByte candidate.view id offset <;>
          simp [readByte,Unified.readByte,Unified.kind,Access.kind,hl,hv,Ptx.Event.Kind.readByte] at hr
      | read id offset =>
        cases hl : Tma.readLocation candidate.view id offset with
        | none => simp [readByte,Unified.readByte,Unified.kind,Access.kind,hl] at hr
        | some source =>
          cases hv : Tma.transferByte candidate.view id offset with
          | none => simp [readByte,Unified.readByte,Unified.kind,Access.kind,hl,hv] at hr
          | some actual =>
            have hp : Ptx.Event.payloadByte source [actual] loc = some value := by
              simpa only [readByte,Unified.readByte,Unified.kind,Access.kind,hl,hv,bind,pure,Option.bind,Option.bind_some,Ptx.Event.Kind.readByte] using hr
            obtain ⟨rfl,_⟩ := Access.singleton_payload hp
            exact ⟨.tma id,.async (.tmaRead hl hv)⟩
      | descriptor id =>
        cases hc : Tma.copyAt candidate.view id with
        | none => simp [readByte,Unified.readByte,Unified.kind,Access.kind,hc] at hr
        | some op =>
          have hp : Ptx.Event.payloadByte (Access.globalDescriptor id.issue.thread op.descriptorAddress) (TensorMap.encode op.descriptor) loc = some value := by
            simpa only [readByte,Unified.readByte,Unified.kind,Access.kind,hc,Option.map_some,Option.bind_some,Ptx.Event.Kind.readByte] using hr
          have hb := Ptx.Event.payloadByte_bounds hp
          rw [TensorMap.encode_length] at hb
          let offset := loc.address-(Access.globalDescriptor id.issue.thread op.descriptorAddress).address
          have ho : offset < 128 := by dsimp [offset]; omega
          have he : (Access.globalDescriptor id.issue.thread op.descriptorAddress).add offset = loc := by
            cases loc with
            | mk space address =>
              simp only [Location.add,Location.mk.injEq]
              refine ⟨hb.1,?_⟩
              have hlo : (Access.globalDescriptor id.issue.thread op.descriptorAddress).address ≤ address := hb.2.1
              change (Access.globalDescriptor id.issue.thread op.descriptorAddress).address+(address-(Access.globalDescriptor id.issue.thread op.descriptorAddress).address) = address
              omega
          rw [← he]
          exact ⟨.tma id,.async (.descriptor hc ho)⟩

theorem actual_write_use {candidate memory loc value}
    (hn : ∀ id, Access.copyAt candidate.view id = none)
    (hw : writeByte candidate memory loc = some value) : ByteAuthority.Uses candidate (Unified.memoryControlNode memory) loc .write := by
  cases memory with
  | wgmmaRead issue operand => simp [writeByte,Unified.native_write_none] at hw
  | base node =>
    cases node with
    | copyRead id | copyWrite id => simp [writeByte,Unified.writeByte,Unified.kind,Access.kind,hn] at hw
    | tma node =>
      cases node with
      | source id => exact ⟨.kernel,.kernel (ordinary_write_use hw)⟩
      | notify id => cases hw
      | descriptor id =>
        change Access.writeByte Tma.localShared Access.globalDescriptor candidate.view (.tma (.descriptor id)) loc = some value at hw
        rw [Access.descriptor_no_write] at hw
        cases hw
      | read id offset =>
        change Access.writeByte Tma.localShared Access.globalDescriptor candidate.view (.tma (.read id offset)) loc = some value at hw
        rw [Access.tensor_read_no_write] at hw
        cases hw
      | write id offset =>
        cases hl : Tma.writeLocation Tma.localShared candidate.view id offset with
        | none => simp [writeByte,Unified.writeByte,Unified.kind,Access.kind,hl] at hw
        | some target =>
          cases hv : Tma.transferByte candidate.view id offset with
          | none => simp [writeByte,Unified.writeByte,Unified.kind,Access.kind,hl,hv] at hw
          | some actual =>
            have hp : Ptx.Event.payloadByte target [actual] loc = some value := by
              simpa only [writeByte,Unified.writeByte,Unified.kind,Access.kind,hl,hv,bind,pure,Option.bind,Option.bind_some,Ptx.Event.Kind.writeByte] using hw
            obtain ⟨rfl,_⟩ := Access.singleton_payload hp
            exact ⟨.tma id,.async (.tmaWrite hl hv)⟩

theorem memoryOfControl_linked {candidate control memory}
    (hn : ∀ id, Access.copyAt candidate.view id = none) (hm : memoryOfControl control = some memory) : Linked candidate memory :=
  ⟨⟨fun _ _ hr => actual_read_use hn hr,fun _ _ hw => actual_write_use hn hw⟩,memoryOfControl_complete hn hm⟩

end
end Ptx.Hopper.ByteContents
