import Ptx.Event.Observation

/-! Race freedom for ordinary kernels whose reads are immutable and whose
written bytes have unique writers. Independent of payload representation and
of any chosen reads-from witness. Clients derive these premises from source. -/
namespace Ptx.Event
variable {ByteValue Answers : Type}

theorem disjoint_reads_unique_writes_no_races {c : Candidate ByteValue Answers}
    (hn : ∀ event, ¬ c.IsRMW event)
    (hr : ∀ read loc value, c.readByte read loc = some value → ∀ writer, c.writeByte writer loc = none)
    (hw : ∀ loc a b va vb, c.writeByte a loc = some va → c.writeByte b loc = some vb → a = b)
    (rf : ReadsFrom) (a b : EventId) : ¬ DataRace c rf a b := by
  intro h
  obtain ⟨loc,ha,hb⟩ := h.overlap
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · obtain ⟨va,hra⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨vb,hrb⟩ := Option.isSome_iff_exists.mp hb
    rcases h.conflict with ⟨other,value,hwrite⟩ | ⟨other,value,hwrite⟩
    · exact read_write_exclusive (hn a) hra hwrite
    · exact read_write_exclusive (hn b) hrb hwrite
  · obtain ⟨va,hra⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨vb,hwb⟩ := Option.isSome_iff_exists.mp hb
    rw [hr a loc va hra b] at hwb
    cases hwb
  · obtain ⟨va,hwa⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨vb,hrb⟩ := Option.isSome_iff_exists.mp hb
    rw [hr b loc vb hrb a] at hwa
    cases hwa
  · obtain ⟨va,hwa⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨vb,hwb⟩ := Option.isSome_iff_exists.mp hb
    have he := hw loc a b va vb hwa hwb
    subst b
    exact h.notStrong (write_self_strong hwa)

end Ptx.Event
