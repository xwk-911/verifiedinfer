import Ptx.Event.RankedWitness
import Ptx.Event.Observation
import Mathlib.Data.List.MinMax

/-! Observations computed from actual emitted writes, choosing a rank-maximal
writer per byte. The finite inventory must cover ALL actual writers. Neither
the observed values nor the writer inventory is assumed from a postcondition. -/
namespace Ptx.Event
open Ptx.ISA
variable {ByteValue Answers : Type}

def rankedWriterSelector (c : Candidate ByteValue Answers) (rank : EventId → Nat)
    (writers : List EventId) (loc : Location) : Option EventId :=
  (writers.filter (fun writer => (c.writeByte writer loc).isSome)).argmax rank

theorem ranked_writer_valid {c : Candidate ByteValue Answers} {rank writers loc writer}
    (hs : rankedWriterSelector c rank writers loc = some writer) : ∃ value, c.writeByte writer loc = some value := by
  have hm := List.argmax_mem (show writer ∈ (writers.filter (fun w => (c.writeByte w loc).isSome)).argmax rank from hs)
  exact Option.isSome_iff_exists.mp (List.mem_filter.mp hm).2

theorem ranked_writer_max {c : Candidate ByteValue Answers} {rank writers loc writer value}
    (hm : writer ∈ writers) (hw : c.writeByte writer loc = some value) :
    ∃ selected, rankedWriterSelector c rank writers loc = some selected ∧ rank writer ≤ rank selected := by
  have hmem : writer ∈ writers.filter (fun w => (c.writeByte w loc).isSome) := List.mem_filter.mpr ⟨hm,by rw [hw]; rfl⟩
  cases hs : rankedWriterSelector c rank writers loc with
  | none =>
    have he := List.argmax_eq_none.mp hs
    rw [he] at hmem
    cases hmem
  | some selected => exact ⟨selected,rfl,List.le_of_mem_argmax hmem hs⟩

theorem ranked_observation {c : Candidate ByteValue Answers} {initial rf rank writers domain}
    (hd : c.Complete) (hg : ∀ loc ∈ domain, loc.space = .global)
    (hcover : ∀ writer loc value, c.writeByte writer loc = some value → writer ∈ writers) :
    ObserverConditions c initial rf (RankedCo c initial rank)
      (selectedObservation c initial (rankedWriterSelector c rank writers) domain) := by
  refine ⟨hd,hg,?_,?_⟩
  · intro loc _ _
    cases hs : rankedWriterSelector c rank writers loc with
    | none => simp [selectedObservation,sourceByte,hs]
    | some writer =>
      obtain ⟨value,hv⟩ := ranked_writer_valid hs
      simp [selectedObservation,sourceByte,hs,hv]
  · intro loc _ _ writer value hw hc
    obtain ⟨selected,hs,hmax⟩ := ranked_writer_max (rank := rank) (hcover writer loc value hw) hw
    obtain ⟨selectedValue,hselected⟩ := ranked_writer_valid hs
    have hsource : (selectedObservation c initial (rankedWriterSelector c rank writers) domain).source loc = .write selected := by
      simp [selectedObservation,hs,hselected]
    rw [hsource] at hc
    have hlt := ranked_co_write_lt hc
    omega

end Ptx.Event
