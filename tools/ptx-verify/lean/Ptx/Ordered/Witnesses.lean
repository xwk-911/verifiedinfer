import Ptx.Ordered.Memory

/-! Construct a particular scoped-memory witness from actual byte sources and
an acyclic rank. Ranks are proof aids for this construction, not restrictions
added to the allowed-execution predicate or universal correctness statements.
The rule accounts for release/acquire in base causality and scoped observation;
it does not reuse the old weak consistency predicate for ordered operations. -/
namespace Ptx.Ordered
open Ptx.ISA Ptx.Event
noncomputable section

theorem initial_co_conditions {c : Candidate} {initial rf} (rank : EventId → Nat)
    (hpo : ∀ a b, ProgramOrder c.view a b → rank a < rank b)
    (hsw : ∀ a b, BarrierSync c.view a b → rank a < rank b)
    (hsra : ∀ a b, ReleaseAcquireSync c rf a b → rank a < rank b)
    (hexit : ∀ a b, ExitBeforeReturn c.view a b → rank a < rank b)
    (hbar : BarrierParticipation c.view)
    (hunique : ∀ loc a b va vb, c.view.writeByte a loc = some va →
      c.view.writeByte b loc = some vb → a = b)
    (hvalue : ∀ read loc value, c.view.readByte read loc = some value →
      sourceByte c.view initial loc (rf read loc) = some value)
    (hrf : ∀ read writer loc vr vw, c.view.readByte read loc = some vr →
      c.view.writeByte writer loc = some vw → rf read loc = .write writer → rank writer < rank read)
    (hfr : ∀ read writer loc vr vw, c.view.readByte read loc = some vr →
      c.view.writeByte writer loc = some vw → rf read loc = .initial → rank read < rank writer) :
    MemoryConditions c initial rf (InitialCo c.view) := by
  have hbase : ∀ a b, BaseCausality c rf a b → rank a < rank b := by
    intro a b hp
    apply hp.rank_lt rank
    intro x y he
    rcases he with h | h | h
    · exact hpo x y h
    · exact hsw x y h
    · exact hsra x y h
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
    rcases hc with ⟨_, hb⟩ | ⟨middle,ho,_,hb⟩
    · exact hbase a b hb
    · exact Nat.lt_trans (hobservation a middle ho) (hbase middle b hb)
  have hcomm : ∀ a b, Communication c.view rf (InitialCo c.view) a b → rank a < rank b := by
    intro a b hc
    rcases hc with ⟨loc, vr, hr, hs, hw⟩ | ⟨loc, hi, _⟩ | ⟨_,loc, vr, hr, hi, writer, vw, heq, hw⟩
    · cases hv : c.view.writeByte a loc with
      | none => simp [hv] at hw
      | some vw => exact hrf b a loc vr vw hr hv hs
    · cases hi
    · have hid : writer = b := Source.write.inj heq.symm
      subst writer
      exact hfr a b loc vr vw hr hw hi
  refine ⟨?_, hbar, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a hp
    exact Nat.lt_irrefl _ (hbase a a hp)
  · intro a hp
    have hlt := hp.rank_lt rank (by
      intro x y he
      rcases he with h | h | h
      · exact hpo x y h
      · exact hsw x y h
      · exact hexit x y h)
    exact Nat.lt_irrefl _ hlt
  · intro read loc value _ hr
    exact hvalue read loc value hr
  · intro _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro loc a ⟨hi, writer, value, hs, _⟩
      cases hi.symm.trans hs
    · rintro loc a b d ⟨_, writer, value, hs, _⟩ ⟨hi, _⟩
      cases hi.symm.trans hs
    · rintro loc a b ⟨rfl, writer, value, rfl, hw⟩
      simp [sourceByte, hw]
    · intro loc writer value hw
      exact ⟨rfl, writer, value, rfl, hw⟩
    · intro loc a b va vb hn ha hb
      exact (hn (hunique loc a b va vb ha hb)).elim
    · intro loc a b _ hi
      cases hi.1
    · intro loc a b va vb ha hb hc
      have heq := hunique loc a b va vb ha hb
      subst b
      have := hcause a a hc
      omega
  · intro _
    constructor
    · intro read writer loc vr vw hr hw hc hs
      have := hcause read writer hc
      have := hrf read writer loc vr vw hr hw hs
      omega
    · rintro writer read loc vw vr hw hr hc ⟨hi, _⟩
      have := hcause writer read hc
      have := hfr read writer loc vr vw hr hw hi
      omega
  · intro _ read writer _ loc vr vw hr hw hs other vr' vw' hr' hw' hco
    have := hrf read writer loc vr vw hr hw hs
    have := hfr read writer other vr' vw' hr' hw' hco.1
    omega
  · intro _ members _ _ a _ hp
    have hlt := hp.rank_lt rank (by
      intro x y he
      exact he.2.2.elim (hpo x y) (hcomm x y))
    exact Nat.lt_irrefl _ hlt
  · intro _ atomic writer _ _ loc vr vw _ _ _ other va vb ha hb hc
    have he := hunique other atomic writer va vb ha hb
    subst writer
    cases hc.1


end
end Ptx.Ordered
