import Ptx.ISA.TypedSemantics

/-! Unsigned logical shifts. Clamping avoids evaluating enormous powers for
oversized u32 counts; the result equals the usual unbounded division model.
Source/destination use the same 32/64-bit width; shift counts always use u32.
-/
namespace Ptx.ISA

theorem shift_clamp_equivalent (width value count : Nat) :
    wrap width value / 2^(min count width) = wrap width value / 2^count := by
  by_cases hc : count ≤ width
  · rw [Nat.min_eq_left hc]
  · have hw : width ≤ count := by omega
    have hx := wrap_bound width value
    have hy := Nat.pow_le_pow_right (by decide : 0 < 2) hw
    rw [Nat.min_eq_right hw,Nat.div_eq_of_lt hx,Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hx hy)]
theorem shift_count_wrap_preserved {width : Nat} (hw : width = 32 ∨ width = 64) (count : Nat) :
    wrap 32 (wrap width count) = wrap 32 count := by
  rcases hw with rfl | rfl
  · exact Nat.mod_mod _ _
  · exact Nat.mod_mod_of_dvd count (by decide : 2^32 ∣ 2^64)
theorem unsigned_shift_local (width value count : Nat) (hw : width = 32 ∨ width = 64)
    (params tid thread dst) :
    localStep params tid thread (.bin .shr width width dst (.imm value) (.imm count)) =
      .ok (assign thread dst (wrap width (wrap width value / 2^(wrap 32 count)))) := by
  simp only [localStep,eval,Except.pure,Except.bind,bind,pure]
  rw [shift_count_wrap_preserved hw]
  rw [shift_clamp_equivalent]

end Ptx.ISA
