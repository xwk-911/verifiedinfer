import Ptx.Event.Consistency

/-! A sufficient construction of consistent witnesses with repeated writes and
RMWs. The ranking certifies one chosen candidate/witness; it is NOT a restriction
on allowed executions or a kernel precondition. Read values and edges still
have to be justified against the actual candidate. -/
namespace Ptx.Event
open Ptx.ISA
variable {ByteValue Answers : Type}

def sourceRank (rank : EventId → Nat) : Source → Nat
  | .initial => 0
  | .write event => rank event+1

def RankedCo (c : Candidate ByteValue Answers) (initial : ByteMap ByteValue) (rank : EventId → Nat)
    (loc : Location) (a b : Source) : Prop :=
  (sourceByte c initial loc a).isSome = true ∧ (sourceByte c initial loc b).isSome = true ∧ sourceRank rank a < sourceRank rank b

theorem ranked_co_write_lt {c : Candidate ByteValue Answers} {initial rank loc a b}
    (hc : RankedCo c initial rank loc (.write a) (.write b)) : rank a < rank b := by
  have h := hc.2.2
  simpa only [sourceRank,Nat.add_lt_add_iff_right] using h

theorem ranked_co_conditions {c : Candidate ByteValue Answers} {initial rf} (rank : EventId → Nat)
    (hpo : ∀ a b, ProgramOrder c a b → rank a < rank b)
    (hsw : ∀ a b, BarrierSync c a b → rank a < rank b)
    (hexit : ∀ a b, ExitBeforeReturn c a b → rank a < rank b)
    (hbar : BarrierParticipation c)
    (hn : ∀ a b, ¬ DataRace c rf a b)
    (hinj : ∀ loc a b va vb, c.writeByte a loc = some va → c.writeByte b loc = some vb → rank a = rank b → a = b)
    (hvalue : ∀ read loc value, c.readByte read loc = some value → sourceByte c initial loc (rf read loc) = some value)
    (hrf : ∀ read writer loc vr vw, c.readByte read loc = some vr → c.writeByte writer loc = some vw →
      rf read loc = .write writer → rank writer < rank read)
    (hfr : ∀ read writer loc vr vw, read ≠ writer → c.readByte read loc = some vr → c.writeByte writer loc = some vw →
      RankedCo c initial rank loc (rf read loc) (.write writer) → rank read < rank writer) :
    GenericMemoryConditions c initial rf (RankedCo c initial rank) := by
  have hbase : ∀ a b, BaseCausality c a b → rank a < rank b := by
    intro a b hp
    exact hp.rank_lt rank (by intro x y he; exact he.elim (hpo x y) (hsw x y))
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
      exact hfr a b loc vr vw hne hr hv hco
  have hwriteco : ∀ loc a b va vb, c.writeByte a loc = some va → c.writeByte b loc = some vb →
      rank a < rank b → RankedCo c initial rank loc (.write a) (.write b) := by
    intro loc a b va vb ha hb hrank
    exact ⟨by simp [sourceByte,ha],by simp [sourceByte,hb],by simpa only [sourceRank,Nat.add_lt_add_iff_right] using hrank⟩
  refine ⟨?_,hbar,?_,?_,?_,?_,?_,?_,?_⟩
  · intro a hp
    exact Nat.lt_irrefl _ (hbase a a hp)
  · intro a hp
    have hlt := hp.rank_lt rank (by
      intro x y he
      rcases he with he | he | he
      · exact hpo x y he
      · exact hsw x y he
      · exact hexit x y he)
    exact Nat.lt_irrefl _ hlt
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
      exact ⟨rfl,by simp [sourceByte,hw],Nat.zero_lt_succ _⟩
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

end Ptx.Event
