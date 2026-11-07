import Ptx.Hopper.ByteOrder

/-! Project byte-specific causality and derived race eligibility into the
previous directional visibility fragment. These constraints are a component
of memory admission; full coherence/atomicity/observer and ISA rules are still
separate obligations. No read-eligibility oracle or desired reply is a field. -/
namespace Ptx.Hopper.Access
open Ptx.ISA
noncomputable section

structure CausalConstraints (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (initial : ProxyMemory) (rf : ReadsFrom) (co : Location → Option Node → Option Node → Prop)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) : Prop where
  agreement : ReadAgreement resolve descriptor c initial (Eligible resolve descriptor c histories cluster rf) rf
  initialization : ¬ MixedSizeRace resolve descriptor c histories cluster rf →
    ∀ writer loc value, writeByte resolve descriptor c writer loc = some value → co loc none (some writer)
  noStale : ¬ MixedSizeRace resolve descriptor c histories cluster rf →
    ∀ writer read loc vw vr, writeByte resolve descriptor c writer loc = some vw → readByte resolve descriptor c read loc = some vr →
    CausalityAt resolve descriptor c histories cluster rf loc writer read → ¬ co loc (rf read loc) (some writer)
  noFuture : ¬ MixedSizeRace resolve descriptor c histories cluster rf →
    ∀ read writer loc vr vw, readByte resolve descriptor c read loc = some vr → writeByte resolve descriptor c writer loc = some vw →
    CausalityAt resolve descriptor c histories cluster rf loc read writer → rf read loc ≠ some writer

theorem causality_visibility {resolve descriptor c initial rf co histories cluster}
    (hc : CausalConstraints resolve descriptor c initial rf co histories cluster)
    (hm : ¬ MixedSizeRace resolve descriptor c histories cluster rf) :
    VisibilityConditions resolve descriptor c initial (Eligible resolve descriptor c histories cluster rf) rf co histories cluster := by
  refine ⟨hc.agreement,hc.initialization hm,?_,?_⟩
  · intro writer read loc vw vr _ hw hr hp
    exact hc.noStale hm writer read loc vw vr hw hr (byte_order_causal
      (.inr (by rw [hw]; rfl)) (.inl (by rw [hr]; rfl)) (published_byte_order hp))
  · intro read writer loc vr vw _ hr hw hp
    exact hc.noFuture hm read writer loc vr vw hr hw (byte_order_causal
      (.inl (by rw [hr]; rfl)) (.inr (by rw [hw]; rfl)) (protected_byte_order hp))

theorem eligible_no_mixed_size {resolve descriptor c histories cluster rf read loc}
    (he : Eligible resolve descriptor c histories cluster rf read loc) : ¬ MixedSizeRace resolve descriptor c histories cluster rf := he.1

end
end Ptx.Hopper.Access
