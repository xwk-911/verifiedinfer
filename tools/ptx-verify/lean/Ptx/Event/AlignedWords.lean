import Ptx.Event.AtomicRules
import Lean.Elab.Tactic.Omega

/-! Four-byte aligned footprints cannot create a mixed-footprint overlap.
This permits equal-footprint races; it does not assume race freedom or prove
unique writers. The stored payload and oracle types remain polymorphic. -/
namespace Ptx.Event
open Ptx.ISA
variable {ByteValue Answers : Type}

theorem overlapping_aligned_words_same_base {candidate : Candidate ByteValue Answers} {a b base other}
    (ha : (candidate.eventAt a).bind Kind.footprint = some (base,4))
    (hb : (candidate.eventAt b).bind Kind.footprint = some (other,4))
    (halign : base.address % 4 = 0) (hbalign : other.address % 4 = 0)
    (ho : candidate.Overlap a b) : base = other := by
  obtain ⟨loc,hla,hlb⟩ := ho
  have h1 := access_footprint_bounds hla ha
  have h2 := access_footprint_bounds hlb hb
  have hspace : base.space = other.space := h1.1.trans h2.1.symm
  have haddr : base.address = other.address := by omega
  cases base; cases other
  cases hspace; cases haddr
  rfl

theorem aligned_word_footprints_no_mixed_races {candidate : Candidate ByteValue Answers} {rf}
    (hf : ∀ actual, candidate.Present actual → ∃ base,
      (candidate.eventAt actual).bind Kind.footprint = some (base,4) ∧ base.address % 4 = 0) :
    ¬MixedSizeRace candidate rf := by
  rintro ⟨a,b,hr,hn⟩
  obtain ⟨loc,ha,hb⟩ := hr.overlap
  obtain ⟨base,hbase,halign⟩ := hf a (accesses_present ha)
  obtain ⟨other,hother,hbalign⟩ := hf b (accesses_present hb)
  have he := overlapping_aligned_words_same_base hbase hother halign hbalign hr.overlap
  exact hn ⟨(base,4),hbase,he ▸ hother⟩

end Ptx.Event
