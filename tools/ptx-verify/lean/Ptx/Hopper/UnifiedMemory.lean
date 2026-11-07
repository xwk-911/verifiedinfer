import Ptx.Hopper.UnifiedCausal

/-! Full causal/coherence/atomicity/SC-per-location component over ordinary,
non-bulk, TMA and native WGMMA accesses. This is model-relative memory
admission, separate from source/collective/control, allocation/lifetime and
observer/runtime obligations. The old TMA memory interface is unchanged. -/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

structure Coherent (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) (rf : ReadsFrom)
    (co : Location → Option Node → Option Node → Prop) : Prop where
  irrefl : ∀ loc a, ¬ co loc a a
  transitive : ∀ loc a b d, co loc a b → co loc b d → co loc a d
  domain : ∀ loc a b, co loc a b → sourcePresent resolve descriptor c loc a ∧ sourcePresent resolve descriptor c loc b
  initialization : ∀ loc writer value, writeByte resolve descriptor c writer loc = some value → co loc none (some writer)
  comparable : ∀ loc a b va vb, a ≠ b → writeByte resolve descriptor c a loc = some va → writeByte resolve descriptor c b loc = some vb →
    (MorallyStrong resolve descriptor c a b ∨ CausalityAt resolve descriptor c histories cluster rf loc a b ∨ CausalityAt resolve descriptor c histories cluster rf loc b a) →
    co loc (some a) (some b) ∨ co loc (some b) (some a)
  raceUnordered : ∀ loc a b, DataRaceAt resolve descriptor c histories cluster rf loc a b → ¬ co loc (some a) (some b)
  causality : ∀ loc a b va vb, writeByte resolve descriptor c a loc = some va → writeByte resolve descriptor c b loc = some vb →
    CausalityAt resolve descriptor c histories cluster rf loc a b → co loc (some a) (some b)

def InitialCo (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (loc : Location) (a b : Option Node) : Prop :=
  a = none ∧ ∃ writer, b = some writer ∧ WritesAt resolve descriptor c writer loc

theorem unique_initial_coherent {resolve descriptor c histories cluster rf}
    (hu : ∀ loc a b va vb, writeByte resolve descriptor c a loc = some va → writeByte resolve descriptor c b loc = some vb → a = b)
    (hn : ∀ loc writer value, writeByte resolve descriptor c writer loc = some value →
      ¬ CausalityAt resolve descriptor c histories cluster rf loc writer writer) :
    Coherent resolve descriptor c histories cluster rf (InitialCo resolve descriptor c) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rintro loc a ⟨hl,writer,hr,_⟩
    have he : (none : Option Node) = some writer := hl.symm.trans hr
    cases he
  · rintro loc a b d ⟨_,writer,hb,_⟩ ⟨hn,_⟩
    have he : (none : Option Node) = some writer := hn.symm.trans hb
    cases he
  · rintro loc a b ⟨rfl,writer,rfl,hw⟩
    exact ⟨trivial,hw⟩
  · intro loc writer value hw
    exact ⟨rfl,writer,rfl,by rw [WritesAt,hw]; rfl⟩
  · intro loc a b va vb hne ha hb _
    exact (hne (hu loc a b va vb ha hb)).elim
  · rintro loc a b _ ⟨he,_⟩; cases he
  · intro loc a b va vb ha hb hc
    have he := hu loc a b va vb ha hb
    subst b
    exact (hn loc a va ha hc).elim

def SingleCopyAtomicity (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (rf : ReadsFrom) (co : Location → Option Node → Option Node → Prop) : Prop :=
  ∀ read writer, MorallyStrong resolve descriptor c read writer →
    ∀ loc vr vw, readByte resolve descriptor c read loc = some vr → writeByte resolve descriptor c writer loc = some vw →
      rf read loc = some writer → ∀ other vr' vw', readByte resolve descriptor c read other = some vr' →
        writeByte resolve descriptor c writer other = some vw' → ¬ co other (rf read other) (some writer)

def RMWAtomicity (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (rf : ReadsFrom) (co : Location → Option Node → Option Node → Prop) : Prop :=
  ∀ atomic writer, (inventoryGraph resolve descriptor c).IsRMW atomic → MorallyStrong resolve descriptor c atomic writer →
    ∀ loc vr vw, readByte resolve descriptor c atomic loc = some vr → writeByte resolve descriptor c writer loc = some vw →
      co loc (rf atomic loc) (some writer) → ∀ other va vb, writeByte resolve descriptor c atomic other = some va →
        writeByte resolve descriptor c writer other = some vb → ¬ co other (some writer) (some atomic)

def Communication (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (rf : ReadsFrom) (co : Location → Option Node → Option Node → Prop) (a b : Node) : Prop :=
  (∃ loc value, readByte resolve descriptor c b loc = some value ∧ rf b loc = some a ∧ WritesAt resolve descriptor c a loc) ∨
  (∃ loc, co loc (some a) (some b)) ∨
  (a ≠ b ∧ ∃ loc value, readByte resolve descriptor c a loc = some value ∧ co loc (rf a loc) (some b))

def SCPerLocation (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (rf : ReadsFrom) (co : Location → Option Node → Option Node → Prop) : Prop :=
  ∀ members : Node → Prop, (∀ a, members a → Present c a) →
    (∀ a b, members a → members b → MorallyStrong resolve descriptor c a b ∧
      ∃ loc, Accesses resolve descriptor c a loc ∧ Accesses resolve descriptor c b loc) →
    ∀ a, members a → ¬ Ptx.Event.Path (fun x y => members x ∧ members y ∧
      (ProgramOrder c x y ∨ Communication resolve descriptor c rf co x y)) a a

structure MemoryConditions (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (initial : ProxyMemory) (rf : ReadsFrom) (co : Location → Option Node → Option Node → Prop)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) : Prop extends
    CausalConstraints resolve descriptor c initial rf co histories cluster where
  baseAcyclic : ∀ loc a, ¬ ByteOrder resolve descriptor c histories cluster loc a a
  coherence : ¬ MixedSizeRace resolve descriptor c histories cluster rf → Coherent resolve descriptor c histories cluster rf co
  atomicity : ¬ MixedSizeRace resolve descriptor c histories cluster rf → SingleCopyAtomicity resolve descriptor c rf co
  rmwAtomicity : ¬ MixedSizeRace resolve descriptor c histories cluster rf → RMWAtomicity resolve descriptor c rf co
  scPerLocation : ¬ MixedSizeRace resolve descriptor c histories cluster rf → SCPerLocation resolve descriptor c rf co

end
end Ptx.Hopper.Unified
