import Ptx.Hopper.UnifiedVisibility
import Ptx.Hopper.UnifiedComponents

/-! Immutable-byte input rules for the full ordinary/TMA/native inventory.
Eligibility retains the model's global mixed-size-race exclusion. Neither
publication nor race freedom of other locations is inferred from immutability.
-/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

theorem immutable_not_tainted {resolve descriptor c histories cluster rf read loc}
    (hi : ∀ writer, writeByte resolve descriptor c writer loc = none) :
    ¬ Tainted resolve descriptor c histories cluster rf read loc := by
  rintro (⟨writer,hw,_⟩ | ⟨writer,_,hw,_,_⟩) <;>
    simp only [WritesAt,hi,Option.isSome_none,Bool.false_eq_true] at hw

theorem immutable_eligible {resolve descriptor c histories cluster rf read loc}
    (hm : ¬ MixedSizeRace resolve descriptor c histories cluster rf)
    (hi : ∀ writer, writeByte resolve descriptor c writer loc = none) :
    Eligible resolve descriptor c histories cluster rf read loc :=
  ⟨hm,immutable_not_tainted hi⟩

theorem immutable_read_source {resolve descriptor c initial eligible rf read loc value}
    (ha : ReadAgreement resolve descriptor c initial eligible rf) (he : eligible read loc)
    (hr : readByte resolve descriptor c read loc = some value)
    (hi : ∀ writer, writeByte resolve descriptor c writer loc = none) :
    rf read loc = none ∧ value = initial read.proxy loc := by
  refine ⟨?_,immutable_read_value ha he hr hi⟩
  cases hs : rf read loc with
  | none => rfl
  | some writer => have hw := write_read_value ha he hr hs; rw [hi writer] at hw; cases hw

theorem immutable_descriptor_from_memory {resolve descriptor c initial rf co histories cluster id op expected}
    (hc : CausalConstraints resolve descriptor c initial rf co histories cluster)
    (hm : ¬ MixedSizeRace resolve descriptor c histories cluster rf)
    (hop : Tma.copyAt c.view id = some op)
    (hs : TensorMap.Stored (initial .tensormap) (descriptor id.issue.thread op.descriptorAddress) expected)
    (hi : ∀ writer, writeByte resolve descriptor c writer ((descriptor id.issue.thread op.descriptorAddress).add 0) = none) :
    op.descriptor = expected := by
  have hr := Access.descriptor_read (resolve := resolve) (descriptor := descriptor) hop (show 0 < 128 by decide)
  have hv := immutable_read_value (read := .base (.tma (.descriptor id)))
    hc.agreement (immutable_eligible hm hi) hr hi
  have hh : Symbolic.Byte.tensorMapPart op.descriptor 0 = .tensorMapPart expected 0 := hv.trans (hs 0 (by decide))
  exact (Symbolic.Byte.tensorMapPart.inj hh).1

end
end Ptx.Hopper.Unified
