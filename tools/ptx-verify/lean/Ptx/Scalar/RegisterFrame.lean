import Ptx.Scalar.Updates

/-! Local register frames for symbolic execution. Cross-bank invalidation is
included: both integer and real slots are framed outside the changed names.
These are register facts, not memory permissions or memory-frame theorems. -/
namespace Ptx.Scalar
open Ptx.ISA
noncomputable section

def RegisterFrame (changed : List String) (before after : State) : Prop :=
  ∀ name, name ∉ changed →
    lookup name after.core.thread.regs = lookup name before.core.thread.regs ∧
    declarationLookup name after.floats = declarationLookup name before.floats

theorem register_frame_refl (changed : List String) (s : State) : RegisterFrame changed s s := by
  intro _ _; exact ⟨rfl,rfl⟩

theorem register_frame_trans {changed before middle after}
    (first : RegisterFrame changed before middle) (second : RegisterFrame changed middle after) :
    RegisterFrame changed before after := by
  intro name hn
  exact ⟨(second name hn).1.trans (first name hn).1,(second name hn).2.trans (first name hn).2⟩

theorem register_frame_mono {small large : List String} {before after : State}
    (hf : RegisterFrame small before after) (hs : List.Subset small large) : RegisterFrame large before after := by
  intro name hn
  exact hf name (fun hm => hn (hs hm))

theorem intAssign_banks (s : State) (dst : String) (value : Nat) : BanksDisjoint (intAssign s dst value) :=
  finish_integer_disjoint _ _
theorem intPC_banks (s : State) (pc : Nat) : BanksDisjoint (intPC s pc) := finish_integer_disjoint _ _
theorem loadedFloat_banks {s : State} (hi : BanksDisjoint s) (dst : String) (value : ℝ) :
    BanksDisjoint (loadedFloat s dst value) := write_float_disjoint hi dst .f32 value

theorem intAssign_register_frame {changed : List String} {s : State} (hi : BanksDisjoint s)
    (dst : String) (value : Nat) (hd : dst ∈ changed) : RegisterFrame changed s (intAssign s dst value) := by
  intro name hn
  have hne : name ≠ dst := by intro he; exact hn (he ▸ hd)
  constructor
  · simp [hne]
  · rw [intAssign_float]
    rcases hi name with hnat | hfloat
    · simp [hne,hnat]
    · simp [hne,hfloat]

theorem intPC_register_frame {changed : List String} {s : State} (hi : BanksDisjoint s)
    (pc : Nat) : RegisterFrame changed s (intPC s pc) := by
  intro name _
  constructor
  · rfl
  · rw [intPC_float]
    rcases hi name with hnat | hfloat
    · simp [hnat]
    · simp [hfloat]

theorem writeFloat_register_frame {changed : List String} (s : State) (dst : String)
    (format : Symbolic.Format) (value : ℝ) (hd : dst ∈ changed) :
    RegisterFrame changed s (writeFloat s dst format value) := by
  intro name hn
  have hne : name ≠ dst := by intro he; exact hn (he ▸ hd)
  obtain ⟨hf,hnat⟩ := float_write_frame s dst name format value hne
  exact ⟨hnat,hf⟩

theorem loadedFloat_register_frame {changed : List String} (s : State) (dst : String)
    (value : ℝ) (hd : dst ∈ changed) : RegisterFrame changed s (loadedFloat s dst value) :=
  writeFloat_register_frame s dst .f32 value hd

end
end Ptx.Scalar
