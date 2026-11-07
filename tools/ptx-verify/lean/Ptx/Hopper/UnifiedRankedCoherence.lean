import Ptx.Hopper.UnifiedMemory

/-! Coherence construction for a checked memory rank and ordered actual
writers. This derives all Coherent fields, including the race guard; it does
not assume full coherence or add a rank to execution admission. -/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

theorem ranked_coherent_of_write_order {resolve descriptor c histories cluster rf} (rank : Node → Nat)
    (hbyte : ∀ loc a b, ByteOrder resolve descriptor c histories cluster loc a b → rank a < rank b)
    (hcausal : ∀ loc a b va vb, writeByte resolve descriptor c a loc = some va → writeByte resolve descriptor c b loc = some vb →
      CausalityAt resolve descriptor c histories cluster rf loc a b → rank a < rank b)
    (horder : ∀ loc a b va vb, writeByte resolve descriptor c a loc = some va → writeByte resolve descriptor c b loc = some vb →
      a = b ∨ ByteOrder resolve descriptor c histories cluster loc a b ∨ ByteOrder resolve descriptor c histories cluster loc b a) :
    Coherent resolve descriptor c histories cluster rf (RankedCo resolve descriptor c rank) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro loc a h
    exact Nat.lt_irrefl _ h.2.2
  · intro loc a b d hab hbd
    exact ⟨hab.1,hbd.2.1,hab.2.2.trans hbd.2.2⟩
  · intro loc a b h
    exact ⟨h.1,h.2.1⟩
  · intro loc writer value hw
    exact ⟨True.intro,by rw [sourcePresent,WritesAt,hw]; rfl,by simp [sourceRank]⟩
  · intro loc a b va vb hne ha hb _
    rcases horder loc a b va vb ha hb with he | hbefore | hafter
    · exact (hne he).elim
    · exact Or.inl ⟨by rw [sourcePresent,WritesAt,ha]; rfl,by rw [sourcePresent,WritesAt,hb]; rfl,
        by simpa only [sourceRank,Nat.add_lt_add_iff_right] using hbyte loc a b hbefore⟩
    · exact Or.inr ⟨by rw [sourcePresent,WritesAt,hb]; rfl,by rw [sourcePresent,WritesAt,ha]; rfl,
        by simpa only [sourceRank,Nat.add_lt_add_iff_right] using hbyte loc b a hafter⟩
  · intro loc a b hrace hco
    obtain ⟨va,ha⟩ := Option.isSome_iff_exists.mp hco.1
    obtain ⟨vb,hb⟩ := Option.isSome_iff_exists.mp hco.2.1
    rcases horder loc a b va vb ha hb with rfl | hbefore | hafter
    · exact hrace.notStrong (write_self_strong ha)
    · exact hrace.notForward (byte_order_causal hrace.left hrace.right hbefore)
    · exact hrace.notBackward (byte_order_causal hrace.right hrace.left hafter)
  · intro loc a b va vb ha hb hc
    exact ⟨by rw [sourcePresent,WritesAt,ha]; rfl,by rw [sourcePresent,WritesAt,hb]; rfl,
      by simpa only [sourceRank,Nat.add_lt_add_iff_right] using hcausal loc a b va vb ha hb hc⟩

end
end Ptx.Hopper.Unified
