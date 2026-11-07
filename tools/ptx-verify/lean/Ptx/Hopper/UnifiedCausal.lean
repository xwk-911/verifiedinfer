import Ptx.Hopper.UnifiedOrder

/-! Unified causal memory constraints. Agreement applies only to eligibility
derived from the complete proxy-aware race model. No arbitrary eligible=True
premise or desired tensor reply is used. -/
namespace Ptx.Hopper.Unified
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

def sourceRank (rank : Node → Nat) : Option Node → Nat
  | none => 0
  | some writer => rank writer+1
def sourcePresent (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (loc : Location) : Option Node → Prop
  | none => True
  | some writer => WritesAt resolve descriptor c writer loc
def RankedCo (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (rank : Node → Nat) (loc : Location) (a b : Option Node) : Prop :=
  sourcePresent resolve descriptor c loc a ∧ sourcePresent resolve descriptor c loc b ∧ sourceRank rank a < sourceRank rank b

theorem ranked_causal_constraints {resolve descriptor c initial rf histories cluster} (rank : Node → Nat)
    (hvalue : ∀ read loc value, readByte resolve descriptor c read loc = some value →
      sourceValue resolve descriptor c initial read loc (rf read loc) = some value)
    (hcausal : ∀ loc a b, Accesses resolve descriptor c a loc → Accesses resolve descriptor c b loc →
      CausalityAt resolve descriptor c histories cluster rf loc a b → rank a < rank b)
    (hselected : ∀ read loc value, readByte resolve descriptor c read loc = some value →
      sourceRank rank (rf read loc) < rank read+1)
    (hlatest : ∀ writer read loc vw vr, writeByte resolve descriptor c writer loc = some vw →
      readByte resolve descriptor c read loc = some vr → rank writer < rank read → rank writer+1 ≤ sourceRank rank (rf read loc)) :
    CausalConstraints resolve descriptor c initial rf (RankedCo resolve descriptor c rank) histories cluster := by
  refine ⟨fun read loc value _ hr => hvalue read loc value hr,?_,?_,?_⟩
  · intro _ writer loc value hw
    exact ⟨trivial,by rw [sourcePresent,WritesAt,hw]; rfl,by simp [sourceRank]⟩
  · intro _ writer read loc vw vr hw hr hc hco
    have hb := hcausal loc writer read (.inr (by rw [hw]; rfl)) (.inl (by rw [hr]; rfl)) hc
    have hl := hlatest writer read loc vw vr hw hr hb
    have hh : sourceRank rank (rf read loc) < rank writer+1 := hco.2.2
    omega
  · intro _ read writer loc vr vw hr hw hc hs
    have hb := hcausal loc read writer (.inl (by rw [hr]; rfl)) (.inr (by rw [hw]; rfl)) hc
    have hh := hselected read loc vr hr
    rw [hs] at hh
    simp only [sourceRank] at hh
    omega

end
end Ptx.Hopper.Unified
