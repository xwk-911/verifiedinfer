import Ptx.Hopper.ByteFootprint

/-! Exhaustive ordinary/resource footprints at an actual source-event identity.
No selected ordinary/resource role is accepted without its source lookup.
-/
namespace Ptx.Hopper.ByteAuthority.Footprint
open Ptx.ISA Ptx.Hopper.Progress
noncomputable section

theorem ordinary_source_uses {candidate id kind loc mode}
    (he : candidate.view.eventAt id = some (.ampere (.ordinary kind)))
    (hu : Uses candidate (.base (.source id)) loc mode) :
    match mode with
    | .read => ∃ value, kind.readByte loc = some value
    | .write => ∃ value, kind.writeByte loc = some value := by
  have hx : ∀ control loc mode, KernelUse Tma.localShared candidate control loc mode → control = .base (.source id) →
      match mode with
      | .read => ∃ value, kind.readByte loc = some value
      | .write => ∃ value, kind.writeByte loc = some value := by
    intro control loc mode huse hctrl
    cases huse with
    | read hlookup hbyte =>
      have hid := Tma.Node.source.inj (Unified.ControlNode.base.inj hctrl)
      subst_vars
      rw [he] at hlookup
      cases hlookup
      exact ⟨_,hbyte⟩
    | write hlookup hbyte =>
      have hid := Tma.Node.source.inj (Unified.ControlNode.base.inj hctrl)
      subst_vars
      rw [he] at hlookup
      cases hlookup
      exact ⟨_,hbyte⟩
    | @resource origin event offset hres ho =>
      cases origin with
      | source actual =>
        have hid := Tma.Node.source.inj (Unified.ControlNode.base.inj hctrl)
        subst actual
        have hbar := Hopper.barrierAt_iff.mp hres
        rw [he] at hbar
        cases hbar
      | notification copy => cases hctrl
  obtain ⟨work,hu⟩ := hu
  cases hu with
  | async hu => cases hu
  | kernel hu => cases mode <;> exact hx _ _ _ hu rfl

theorem resource_source_uses {candidate id event loc mode}
    (he : candidate.view.eventAt id = some (.barrier event))
    (hu : Uses candidate (.base (.source id)) loc mode) :
    ∃ offset, offset < 8 ∧ loc = event.location.add offset ∧ mode = .write := by
  have hx : ∀ control loc mode, KernelUse Tma.localShared candidate control loc mode → control = .base (.source id) →
      ∃ offset, offset < 8 ∧ loc = event.location.add offset ∧ mode = .write := by
    intro control loc mode huse hctrl
    cases huse with
    | read hlookup hbyte =>
      have hid := Tma.Node.source.inj (Unified.ControlNode.base.inj hctrl)
      subst_vars
      rw [he] at hlookup
      cases hlookup
    | write hlookup hbyte =>
      have hid := Tma.Node.source.inj (Unified.ControlNode.base.inj hctrl)
      subst_vars
      rw [he] at hlookup
      cases hlookup
    | @resource origin actual offset hres ho =>
      cases origin with
      | source eid =>
        have hid := Tma.Node.source.inj (Unified.ControlNode.base.inj hctrl)
        subst eid
        have hlookup := Hopper.barrierAt_iff.mpr he
        change candidate.view.barrierAt id = some actual at hres
        have heq : actual = event := Option.some.inj (hres.symm.trans hlookup)
        subst actual
        exact ⟨offset,ho,rfl,rfl⟩
      | notification copy => cases hctrl
  obtain ⟨work,hu⟩ := hu
  cases hu with
  | async hu => cases hu
  | kernel hu => exact hx _ _ _ hu rfl

end
end Ptx.Hopper.ByteAuthority.Footprint
