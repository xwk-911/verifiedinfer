import Ptx.Hopper.UnifiedBytes

/-! Proxy- and byte-preserving memory order for the unified inventory. Native
reads enter only through checked publication and leave only through actual
completion. Source launch/control is deliberately not a byte-memory edge. -/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section
abbrev DescriptorResolver := Access.DescriptorResolver
abbrev ClusterScope := Access.ClusterScope

def ByteEdge (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) (loc : Location) (a b : Node) : Prop :=
  (match a,b with | .base left,.base right => Access.ByteEdge resolve descriptor c.view histories cluster loc left right | _,_ => False) ∨
  NativePublished resolve c histories cluster loc a b ∨ NativeCompleted c loc a b ∨ NativeReuse resolve c loc a b

def ByteOrder (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) (loc : Location) :=
  Ptx.Event.Path (ByteEdge resolve descriptor c histories cluster loc)

def Observed (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate) (rf : ReadsFrom) (writer read : Node) : Prop :=
  MorallyStrong resolve descriptor c writer read ∧ ∃ loc value,
    readByte resolve descriptor c read loc = some value ∧ rf read loc = some writer ∧ WritesAt resolve descriptor c writer loc
inductive ObservationOrder (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate) (rf : ReadsFrom) : Node → Node → Prop
  | direct {a b} : Observed resolve descriptor c rf a b → ObservationOrder resolve descriptor c rf a b
  | viaRMW {a middle b} : (inventoryGraph resolve descriptor c).IsRMW middle →
      ObservationOrder resolve descriptor c rf a middle → ObservationOrder resolve descriptor c rf middle b →
      ObservationOrder resolve descriptor c rf a b

/-- Observation may prefix byte-preserved order. This is not its arbitrary
transitive closure through reads/writes or through other byte locations. -/
def CausalityAt (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) (rf : ReadsFrom) (loc : Location) (a b : Node) : Prop :=
  (Accesses resolve descriptor c a loc ∧ Accesses resolve descriptor c b loc ∧ ByteOrder resolve descriptor c histories cluster loc a b) ∨
  ∃ middle, ObservationOrder resolve descriptor c rf a middle ∧
    Accesses resolve descriptor c middle loc ∧ Accesses resolve descriptor c b loc ∧ ByteOrder resolve descriptor c histories cluster loc middle b

structure DataRaceAt (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) (rf : ReadsFrom) (loc : Location) (a b : Node) : Prop where
  left : Accesses resolve descriptor c a loc
  right : Accesses resolve descriptor c b loc
  conflict : WritesAt resolve descriptor c a loc ∨ WritesAt resolve descriptor c b loc
  notForward : ¬ CausalityAt resolve descriptor c histories cluster rf loc a b
  notBackward : ¬ CausalityAt resolve descriptor c histories cluster rf loc b a
  notStrong : ¬ MorallyStrong resolve descriptor c a b

def MixedSizeRace (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) (rf : ReadsFrom) : Prop :=
  ∃ loc a b, DataRaceAt resolve descriptor c histories cluster rf loc a b ∧ ¬ SameFootprint resolve descriptor c a b
def Tainted (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) (rf : ReadsFrom) (read : Node) (loc : Location) : Prop :=
  (∃ writer, WritesAt resolve descriptor c writer loc ∧ DataRaceAt resolve descriptor c histories cluster rf loc read writer) ∨
  (∃ a b, WritesAt resolve descriptor c a loc ∧ WritesAt resolve descriptor c b loc ∧
    DataRaceAt resolve descriptor c histories cluster rf loc a b)
def Eligible (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) (rf : ReadsFrom) (read : Node) (loc : Location) : Prop :=
  ¬ MixedSizeRace resolve descriptor c histories cluster rf ∧ ¬ Tainted resolve descriptor c histories cluster rf read loc


theorem base_byte_edge {resolve descriptor c histories cluster loc a b}
    (h : Access.ByteEdge resolve descriptor c.view histories cluster loc a b) :
    ByteEdge resolve descriptor c histories cluster loc (.base a) (.base b) := .inl h

theorem base_byte_order {resolve descriptor c histories cluster loc a b}
    (h : Access.ByteOrder resolve descriptor c.view histories cluster loc a b) :
    ByteOrder resolve descriptor c histories cluster loc (.base a) (.base b) := by
  induction h with
  | single he => exact .single (base_byte_edge he)
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem native_published_byte_order {resolve descriptor c histories cluster loc a b}
    (h : NativePublished resolve c histories cluster loc a b) : ByteOrder resolve descriptor c histories cluster loc a b :=
  .single (.inr (.inl h))
theorem native_completed_byte_order {resolve descriptor c histories cluster loc a b}
    (h : NativeCompleted c loc a b) : ByteOrder resolve descriptor c histories cluster loc a b :=
  .single (.inr (.inr (.inl h)))
theorem native_reuse_byte_order {resolve descriptor c histories cluster loc a b}
    (h : NativeReuse resolve c loc a b) : ByteOrder resolve descriptor c histories cluster loc a b :=
  .single (.inr (.inr (.inr h)))
theorem byte_order_causal {resolve descriptor c histories cluster rf a b loc}
    (ha : Accesses resolve descriptor c a loc) (hb : Accesses resolve descriptor c b loc)
    (ho : ByteOrder resolve descriptor c histories cluster loc a b) : CausalityAt resolve descriptor c histories cluster rf loc a b :=
  .inl ⟨ha,hb,ho⟩

theorem ordered_conflicts_no_races {resolve descriptor c histories cluster rf}
    (ho : ∀ writer other loc, WritesAt resolve descriptor c writer loc → Accesses resolve descriptor c other loc →
      writer = other ∨ ByteOrder resolve descriptor c histories cluster loc writer other ∨ ByteOrder resolve descriptor c histories cluster loc other writer) :
    ∀ loc a b, ¬ DataRaceAt resolve descriptor c histories cluster rf loc a b := by
  intro loc a b hr
  rcases hr.conflict with hw | hw
  · rcases ho a b loc hw hr.right with he | hf | hb
    · subst b
      obtain ⟨value,hvalue⟩ := Option.isSome_iff_exists.mp hw
      exact hr.notStrong (write_self_strong hvalue)
    · exact hr.notForward (byte_order_causal hr.left hr.right hf)
    · exact hr.notBackward (byte_order_causal hr.right hr.left hb)
  · rcases ho b a loc hw hr.left with he | hf | hb
    · subst a
      obtain ⟨value,hvalue⟩ := Option.isSome_iff_exists.mp hw
      exact hr.notStrong (write_self_strong hvalue)
    · exact hr.notBackward (byte_order_causal hr.right hr.left hf)
    · exact hr.notForward (byte_order_causal hr.left hr.right hb)

theorem race_free_eligible {resolve descriptor c histories cluster rf}
    (hn : ∀ loc a b, ¬ DataRaceAt resolve descriptor c histories cluster rf loc a b) (read loc) :
    Eligible resolve descriptor c histories cluster rf read loc := by
  constructor
  · rintro ⟨loc,a,b,hr,_⟩; exact hn loc a b hr
  · rintro (⟨_,_,hr⟩ | ⟨_,_,_,_,hr⟩) <;> exact hn _ _ _ hr


end
end Ptx.Hopper.Unified
