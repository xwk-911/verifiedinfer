import Ptx.MemoryGraph.Rules

/-! Constructive memory witnesses for arbitrary access graphs with at most one writer per byte.
A ranking certifies this PARTICULAR witness; it is not added to the definition
of allowed executions. Universal correctness still quantifies over all memory
witnesses. No conclusion about launch safety or GPU/runtime behavior is made.
-/
namespace Ptx.MemoryGraph
open Ptx.ISA

variable {Node ByteValue Source : Type} [Sources Node Source]

def InitialCo (c : Graph Node ByteValue) (loc : Location) (a b : Source) : Prop :=
  a = initialSource ∧ ∃ writer value, b = writeSource writer ∧ c.writeByte writer loc = some value

theorem initial_co_conditions {c : Graph Node ByteValue} {initial} {rf : ReadsFrom Node Source} (rank : Node → Nat)
    (hpo : ∀ a b, c.po a b → rank a < rank b)
    (hbase : ∀ a b, c.base a b → rank a < rank b)
    (hunique : ∀ loc a b va vb, c.writeByte a loc = some va →
      c.writeByte b loc = some vb → a = b)
    (hvalue : ∀ read loc value, c.readByte read loc = some value →
      sourceByte c initial loc (rf read loc) = some value)
    (hrf : ∀ read writer loc vr vw, c.readByte read loc = some vr →
      c.writeByte writer loc = some vw → rf read loc = writeSource writer → rank writer < rank read)
    (hfr : ∀ read writer loc vr vw, c.readByte read loc = some vr →
      c.writeByte writer loc = some vw → rf read loc = initialSource → rank read < rank writer) :
    MemoryConditions c initial rf (InitialCo c) := by
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
  have hcomm : ∀ a b, Communication c rf (InitialCo c) a b → rank a < rank b := by
    intro a b hc
    rcases hc with ⟨loc, vr, hr, hs, hw⟩ | ⟨loc, hi, _⟩ | ⟨_,loc, vr, hr, hi, writer, vw, heq, hw⟩
    · cases hv : c.writeByte a loc with
      | none => simp [hv] at hw
      | some vw => exact hrf b a loc vr vw hr hv hs
    · exact (initial_ne_write a hi.symm).elim
    · have hid : writer = b := write_injective heq.symm
      subst writer
      exact hfr a b loc vr vw hr hw hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a hp
    exact Nat.lt_irrefl _ (hbase a a hp)
  · intro read loc value _ hr
    exact hvalue read loc value hr
  · intro _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro loc a ⟨hi, writer, value, hs, _⟩
      exact initial_ne_write _ (hi.symm.trans hs)
    · rintro loc a b d ⟨_, writer, value, hs, _⟩ ⟨hi, _⟩
      exact (initial_ne_write _ (hi.symm.trans hs)).elim
    · rintro loc a b ⟨rfl, writer, value, rfl, hw⟩
      simp only [sourceByte_initial,sourceByte_write,hw,Option.isSome_some,and_self]
    · intro loc writer value hw
      exact ⟨rfl, writer, value, rfl, hw⟩
    · intro loc a b va vb hn ha hb
      exact (hn (hunique loc a b va vb ha hb)).elim
    · intro loc a b _ hi
      exact initial_ne_write _ hi.1.symm
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
    exact initial_ne_write _ hc.1.symm

end Ptx.MemoryGraph
