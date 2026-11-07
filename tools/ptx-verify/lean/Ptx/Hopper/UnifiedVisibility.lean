import Ptx.Hopper.UnifiedMemory

/-! Values follow from proxy-aware memory admission and derived eligibility,
not an input-reply oracle. These rules quantify over every compatible RF/co;
the rank constructor in UnifiedCausal is used only for separate witnesses. -/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

theorem write_read_value {resolve descriptor c initial eligible rf read loc value writer}
    (ha : ReadAgreement resolve descriptor c initial eligible rf) (he : eligible read loc)
    (hr : readByte resolve descriptor c read loc = some value) (hs : rf read loc = some writer) :
    writeByte resolve descriptor c writer loc = some value := by
  have h := ha read loc value he hr
  simpa only [sourceValue,hs] using h
theorem immutable_read_value {resolve descriptor c initial eligible rf read loc value}
    (ha : ReadAgreement resolve descriptor c initial eligible rf) (he : eligible read loc)
    (hr : readByte resolve descriptor c read loc = some value)
    (hi : ∀ writer, writeByte resolve descriptor c writer loc = none) : value = initial read.proxy loc := by
  cases hs : rf read loc with
  | none => exact (Option.some.inj (by simpa only [sourceValue,hs] using ha read loc value he hr)).symm
  | some writer => have hh := write_read_value ha he hr hs; rw [hi writer] at hh; cases hh
theorem unique_writer_source {resolve descriptor c initial rf co histories cluster writer read loc vw vr}
    (hc : CausalConstraints resolve descriptor c initial rf co histories cluster)
    (he : Eligible resolve descriptor c histories cluster rf read loc)
    (hw : writeByte resolve descriptor c writer loc = some vw) (hr : readByte resolve descriptor c read loc = some vr)
    (hb : ByteOrder resolve descriptor c histories cluster loc writer read)
    (hu : ∀ other value, writeByte resolve descriptor c other loc = some value → other = writer) :
    rf read loc = some writer := by
  cases hs : rf read loc with
  | none =>
    have hp := byte_order_causal (rf := rf) (.inr (by rw [hw]; rfl)) (.inl (by rw [hr]; rfl)) hb
    exact (hc.noStale he.1 writer read loc vw vr hw hr hp (by simpa only [hs] using hc.initialization he.1 writer loc vw hw)).elim
  | some other => have hh := write_read_value hc.agreement he hr hs; exact congrArg some (hu other vr hh)
theorem unique_writer_visible {resolve descriptor c initial rf co histories cluster writer read loc vw vr}
    (hc : CausalConstraints resolve descriptor c initial rf co histories cluster)
    (he : Eligible resolve descriptor c histories cluster rf read loc)
    (hw : writeByte resolve descriptor c writer loc = some vw) (hr : readByte resolve descriptor c read loc = some vr)
    (hb : ByteOrder resolve descriptor c histories cluster loc writer read)
    (hu : ∀ other value, writeByte resolve descriptor c other loc = some value → other = writer) : vr = vw := by
  have hs := unique_writer_source hc he hw hr hb hu
  exact Option.some.inj ((write_read_value hc.agreement he hr hs).symm.trans hw)
theorem phase_writer_source {resolve descriptor c initial rf co histories cluster writer read loc vw vr}
    (hc : MemoryConditions resolve descriptor c initial rf co histories cluster)
    (he : Eligible resolve descriptor c histories cluster rf read loc)
    (hw : writeByte resolve descriptor c writer loc = some vw) (hr : readByte resolve descriptor c read loc = some vr)
    (hb : ByteOrder resolve descriptor c histories cluster loc writer read)
    (hphase : ∀ other value, writeByte resolve descriptor c other loc = some value →
      other = writer ∨ CausalityAt resolve descriptor c histories cluster rf loc other writer ∨ CausalityAt resolve descriptor c histories cluster rf loc read other) :
    rf read loc = some writer := by
  have hcausal := byte_order_causal (rf := rf) (.inr (by rw [hw]; rfl)) (.inl (by rw [hr]; rfl)) hb
  cases hs : rf read loc with
  | none => exact (hc.noStale he.1 writer read loc vw vr hw hr hcausal (by simpa only [hs] using hc.initialization he.1 writer loc vw hw)).elim
  | some other =>
    have hv := write_read_value hc.agreement he hr hs
    rcases hphase other vr hv with hid | hbefore | hafter
    · exact congrArg some hid
    · have hco := (hc.coherence he.1).causality loc other writer vr vw hv hw hbefore
      exact (hc.noStale he.1 writer read loc vw vr hw hr hcausal (hs ▸ hco)).elim
    · exact (hc.noFuture he.1 read other loc vr vr hr hv hafter hs).elim

end
end Ptx.Hopper.Unified
