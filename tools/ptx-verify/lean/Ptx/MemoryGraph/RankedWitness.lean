import Ptx.MemoryGraph.Core

/-! Sufficient constructive witnesses for repeated writes, including independent
async operation agents. A rank certifies a chosen graph/rf/co witness only; it
is never added to the definition of allowed executions or kernel preconditions.
Read values, every order edge, race freedom and from-read bounds are obligations
against the actual graph. Full source/construct legality remains separate. -/
namespace Ptx.MemoryGraph
open Ptx.ISA
variable {Node ByteValue Source : Type} [Sources Node Source]

def sourceRank (rank : Node → Nat) (source : Source) : Nat :=
  match Sources.decode source with | none => 0 | some node => rank node+1

@[simp] theorem sourceRank_initial (rank : Node → Nat) :
    sourceRank rank (initialSource (Source := Source)) = 0 := by simp [sourceRank]
@[simp] theorem sourceRank_write (rank : Node → Nat) (node : Node) :
    sourceRank rank (writeSource (Source := Source) node) = rank node+1 := by simp [sourceRank]

def RankedCo (c : Graph Node ByteValue) (initial : Ptx.Event.ByteMap ByteValue) (rank : Node → Nat)
    (loc : Location) (a b : Source) : Prop :=
  (sourceByte c initial loc a).isSome = true ∧ (sourceByte c initial loc b).isSome = true ∧ sourceRank rank a < sourceRank rank b

theorem ranked_co_write_lt {c : Graph Node ByteValue} {initial rank loc a b}
    (hc : RankedCo c initial rank loc (writeSource (Source := Source) a) (writeSource b)) : rank a < rank b := by
  have h := hc.2.2
  simpa only [sourceRank_write,Nat.add_lt_add_iff_right] using h

theorem ranked_co_conditions {c : Graph Node ByteValue} {initial : Ptx.Event.ByteMap ByteValue} {rf : ReadsFrom Node Source} (rank : Node → Nat)
    (hpo : ∀ a b, c.po a b → rank a < rank b)
    (hbase : ∀ a b, c.base a b → rank a < rank b)
    (hn : ∀ a b, ¬ DataRace c rf a b)
    (hinj : ∀ loc a b va vb, c.writeByte a loc = some va → c.writeByte b loc = some vb → rank a = rank b → a = b)
    (hvalue : ∀ read loc value, c.readByte read loc = some value → sourceByte c initial loc (rf read loc) = some value)
    (hrf : ∀ read writer loc vr vw, c.readByte read loc = some vr → c.writeByte writer loc = some vw →
      rf read loc = writeSource writer → rank writer < rank read)
    (hfr : ∀ read writer loc vr vw, read ≠ writer → c.readByte read loc = some vr → c.writeByte writer loc = some vw →
      RankedCo c initial rank loc (rf read loc) (writeSource writer) → rank read < rank writer) :
    MemoryConditions c initial rf (RankedCo c initial rank) := by
  have hobservation : ∀ a b, ObservationOrder c rf a b → rank a < rank b := by
    intro a b ho
    induction ho with
    | direct h =>
      obtain ⟨_,loc,vr,hr,hs,hw⟩ := h
      obtain ⟨vw,hv⟩ := Option.isSome_iff_exists.mp hw
      exact hrf _ _ loc vr vw hr hv hs
    | viaRMW _ _ _ ih₁ ih₂ => exact Nat.lt_trans ih₁ ih₂
  have hcause : ∀ a b, Causality c rf a b → rank a < rank b := by
    intro a b hc
    rcases hc with ⟨_,hb⟩ | ⟨middle,ho,_,hb⟩
    · exact hbase a b hb
    · exact Nat.lt_trans (hobservation a middle ho) (hbase middle b hb)
  have hcomm : ∀ a b, Communication c rf (RankedCo c initial rank) a b → rank a < rank b := by
    intro a b hc
    rcases hc with ⟨loc,vr,hr,hs,hw⟩ | ⟨loc,hco⟩ | ⟨hne,loc,vr,hr,hco⟩
    · obtain ⟨vw,hv⟩ := Option.isSome_iff_exists.mp hw
      exact hrf b a loc vr vw hr hv hs
    · exact ranked_co_write_lt hco
    · obtain ⟨vw,hv⟩ := Option.isSome_iff_exists.mp hco.2.1
      exact hfr a b loc vr vw hne hr (by simpa only [sourceByte_write] using hv) hco
  have hwriteco : ∀ loc a b va vb, c.writeByte a loc = some va → c.writeByte b loc = some vb →
      rank a < rank b → RankedCo c initial rank loc (writeSource (Source := Source) a) (writeSource b) := by
    intro loc a b va vb ha hb hrank
    exact ⟨by simp [sourceByte_write,ha],by simp [sourceByte_write,hb],by simpa only [sourceRank,decode_write,Nat.add_lt_add_iff_right] using hrank⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro a hp
    exact Nat.lt_irrefl _ (hbase a a hp)
  · intro read loc value _ hr
    exact hvalue read loc value hr
  · intro _
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · intro loc a hc
      exact Nat.lt_irrefl _ hc.2.2
    · intro loc a b d hab hbd
      exact ⟨hab.1,hbd.2.1,Nat.lt_trans hab.2.2 hbd.2.2⟩
    · intro loc a b hc
      exact ⟨hc.1,hc.2.1⟩
    · intro loc writer value hw
      exact ⟨by simp,by simp [sourceByte_write,hw],by simp [sourceRank]⟩
    · intro loc a b va vb hne ha hb _
      have hneq : rank a ≠ rank b := fun he => hne (hinj loc a b va vb ha hb he)
      rcases Nat.lt_or_gt_of_ne hneq with hlt | hlt
      · exact Or.inl (hwriteco loc a b va vb ha hb hlt)
      · exact Or.inr (hwriteco loc b a vb va hb ha hlt)
    · intro loc a b hr
      exact (hn a b hr).elim
    · intro loc a b va vb ha hb hc
      exact hwriteco loc a b va vb ha hb (hcause a b hc)
  · intro _
    constructor
    · intro read writer loc vr vw hr hw hc hs
      have h₁ := hcause read writer hc
      have h₂ := hrf read writer loc vr vw hr hw hs
      omega
    · intro writer read loc vw vr hw hr hc hco
      have h₁ := hcause writer read hc
      have hne : read ≠ writer := by intro he; subst read; omega
      have h₂ := hfr read writer loc vr vw hne hr hw hco
      omega
  · intro _ read writer _ loc vr vw hr hw hs other vr' vw' hr' hw' hco
    have h₁ := hrf read writer loc vr vw hr hw hs
    have hne : read ≠ writer := by intro he; subst read; omega
    have h₂ := hfr read writer other vr' vw' hne hr' hw' hco
    omega
  · intro _ members _ _ a _ hp
    have hlt := hp.rank_lt rank (by intro x y he; exact he.2.2.elim (hpo x y) (hcomm x y))
    exact Nat.lt_irrefl _ hlt
  · intro _ atomic writer _ _ loc vr vw hr hw hco other va vb hwa hwb hafter
    have h₁ := ranked_co_write_lt hafter
    have hne : atomic ≠ writer := by intro he; subst writer; omega
    have h₂ := hfr atomic writer loc vr vw hne hr hw hco
    omega

end Ptx.MemoryGraph
