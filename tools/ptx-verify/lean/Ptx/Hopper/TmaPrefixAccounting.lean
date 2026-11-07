import Ptx.Hopper.MbarrierPrefixAccounting
import Ptx.Hopper.TmaObservation

/-! Actual history prefixes inherit operational conservation laws. Unique
initialization and fixed transaction budgets are explicit inventory obligations;
these rules do not identify a tile's completion phase or create visibility. -/
namespace Ptx.Hopper.Tma
open Ptx.ISA
noncomputable section

theorem history_entry_at_origin_index {resolve candidate loc entries origin op}
    (hh : HistoryValid resolve candidate loc entries)
    (he : resourceAt resolve candidate origin = some ⟨loc,op⟩) :
    entries[(entries.map Entry.origin).idxOf origin]? = some ⟨origin,op⟩ := by
  obtain ⟨index,hi⟩ := List.mem_iff_getElem?.mp (history_complete hh he)
  have hindex := origin_index hh.unique hi
  rw [hindex]
  exact hi

theorem history_prefix_accounting {resolve candidate loc entries}
    (hh : HistoryValid resolve candidate loc entries) (cut : Nat) :
    ∃ before, Mbarrier.run none ((entries.map Entry.operation).take cut) = some before ∧
      Mbarrier.ObjectWellFormed before ∧ (Mbarrier.account ((entries.map Entry.operation).take cut)).Agrees before := by
  obtain ⟨last,hr⟩ := hh.protocol
  exact Mbarrier.run_take_accounting hr cut

theorem stamp_accounting {entries index stamp} (hs : stampBefore entries index = some stamp) :
    ∃ state, Mbarrier.run none ((entries.map Entry.operation).take index) = some (some state) ∧
      state.expected = (Mbarrier.account ((entries.map Entry.operation).take index)).expected ∧
      state.tx = ((Mbarrier.account ((entries.map Entry.operation).take index)).added : Int)-
        ((Mbarrier.account ((entries.map Entry.operation).take index)).completed : Int) ∧
      Mbarrier.arrivalPotential state = (Mbarrier.account ((entries.map Entry.operation).take index)).arrivals ∧
      stamp.lifetime = lifetimeBefore entries index ∧ stamp.phase = state.phase := by
  obtain ⟨state,hr,hl,hp⟩ := stamp_before_sound hs
  obtain ⟨he,ht,ha⟩ := Mbarrier.run_accounting hr
  exact ⟨state,hr,he,ht,ha,hl,hp⟩

theorem history_live_prefix_balance {resolve candidate loc entries state}
    (hh : HistoryValid resolve candidate loc entries)
    (hi : ((entries.map Entry.operation).filter Mbarrier.isInitialization).length = 1)
    (hu : ∀ op ∈ entries.map Entry.operation, Mbarrier.UnitInitialization op) (cut : Nat)
    (hp : Mbarrier.run none ((entries.map Entry.operation).take cut) = some (some state)) :
    state.expected = 1 ∧ state.pending ≤ 1 ∧
      state.phase+1 = Mbarrier.arrivalCount ((entries.map Entry.operation).take cut)+state.pending ∧
      state.tx = (Mbarrier.addedBytes ((entries.map Entry.operation).take cut) : Int)-
        (Mbarrier.completedBytes ((entries.map Entry.operation).take cut) : Int) := by
  obtain ⟨last,hr⟩ := hh.protocol
  exact Mbarrier.single_initialization_prefix_balance hi hu hr cut hp

theorem history_wait_counted_phase {resolve candidate loc entries index event parity}
    (hh : HistoryValid resolve candidate loc entries)
    (hi : ((entries.map Entry.operation).filter Mbarrier.isInitialization).length = 1)
    (hu : ∀ op ∈ entries.map Entry.operation, Mbarrier.UnitInitialization op)
    (he : entries[index]? = some ⟨.source event,.tryWaitParity parity true⟩) :
    ∃ state, Mbarrier.run none ((entries.map Entry.operation).take index) = some (some state) ∧
      state.expected = 1 ∧ state.pending ≤ 1 ∧
      state.phase+1 = Mbarrier.arrivalCount ((entries.map Entry.operation).take index)+state.pending ∧
      state.tx = (Mbarrier.addedBytes ((entries.map Entry.operation).take index) : Int)-
        (Mbarrier.completedBytes ((entries.map Entry.operation).take index) : Int) ∧
      0 < state.phase ∧ parity%2 ≠ state.phase%2 := by
  obtain ⟨state,_,_,hp,hpositive,hparity⟩ := history_successful_wait_phase hh he
  obtain ⟨hex,hpending,hphase,htx⟩ := history_live_prefix_balance hh hi hu index hp
  exact ⟨state,hp,hex,hpending,hphase,htx,hpositive,hparity⟩

theorem history_notification_counted_phase {resolve candidate loc entries index copy bytes}
    (hh : HistoryValid resolve candidate loc entries)
    (hi : ((entries.map Entry.operation).filter Mbarrier.isInitialization).length = 1)
    (hu : ∀ op ∈ entries.map Entry.operation, Mbarrier.UnitInitialization op)
    (he : entries[index]? = some ⟨.notification copy,.completeTx bytes⟩) :
    ∃ state, Mbarrier.run none ((entries.map Entry.operation).take index) = some (some state) ∧
      state.expected = 1 ∧ state.pending ≤ 1 ∧
      state.phase+1 = Mbarrier.arrivalCount ((entries.map Entry.operation).take index)+state.pending ∧
      state.tx = (Mbarrier.addedBytes ((entries.map Entry.operation).take index) : Int)-
        (Mbarrier.completedBytes ((entries.map Entry.operation).take index) : Int) := by
  obtain ⟨last,hr⟩ := hh.protocol
  have hop : (entries.map Entry.operation)[index]? = some (.completeTx bytes) := by simp [List.getElem?_map,he]
  obtain ⟨before,after,hp,hstep⟩ := Hopper.protocol_prefix_step hr hop
  cases before with
  | none => simp [Mbarrier.step] at hstep
  | some state => exact ⟨state,hp,history_live_prefix_balance hh hi hu index hp⟩

theorem history_fixed_prefix_transactions {resolve candidate loc entries state bytes}
    (hh : HistoryValid resolve candidate loc entries)
    (hi : ((entries.map Entry.operation).filter Mbarrier.isInitialization).length = 1)
    (hu : ∀ op ∈ entries.map Entry.operation, Mbarrier.UnitInitialization op)
    (hf : ∀ op ∈ entries.map Entry.operation, Mbarrier.FixedArrival bytes op) (cut : Nat)
    (hp : Mbarrier.run none ((entries.map Entry.operation).take cut) = some (some state)) :
    state.tx = (bytes : Int)*(Mbarrier.arrivalCount ((entries.map Entry.operation).take cut) : Int)-
      (Mbarrier.completedBytes ((entries.map Entry.operation).take cut) : Int) := by
  have ht := (history_live_prefix_balance hh hi hu cut hp).2.2.2
  have hb := Mbarrier.fixed_arrival_added_bytes (ops := (entries.map Entry.operation).take cut)
    bytes (fun op hop => hf op (List.mem_of_mem_take hop))
  rw [hb,Nat.cast_mul] at ht
  exact ht

theorem lifetime_before_initialization_count (entries : List Entry) (cut : Nat) :
    lifetimeBefore entries cut = (((entries.map Entry.operation).take cut).filter Mbarrier.isInitialization).length := by
  rw [← List.map_take,List.filter_map,List.length_map]
  rfl

theorem history_live_prefix_lifetime {resolve candidate loc entries state}
    (hh : HistoryValid resolve candidate loc entries)
    (hi : ((entries.map Entry.operation).filter Mbarrier.isInitialization).length = 1)
    (hu : ∀ op ∈ entries.map Entry.operation, Mbarrier.UnitInitialization op) (cut : Nat)
    (hp : Mbarrier.run none ((entries.map Entry.operation).take cut) = some (some state)) :
    lifetimeBefore entries cut = 1 := by
  obtain ⟨last,hr⟩ := hh.protocol
  rw [lifetime_before_initialization_count]
  exact Mbarrier.single_initialization_live_prefix_lifetime hi hu hr cut hp

theorem history_live_prefix_stamp {resolve candidate loc entries state}
    (hh : HistoryValid resolve candidate loc entries)
    (hi : ((entries.map Entry.operation).filter Mbarrier.isInitialization).length = 1)
    (hu : ∀ op ∈ entries.map Entry.operation, Mbarrier.UnitInitialization op) (cut : Nat)
    (hp : Mbarrier.run none ((entries.map Entry.operation).take cut) = some (some state)) :
    stampBefore entries cut = some ⟨1,state.phase⟩ := by
  rw [stampBefore,hp,history_live_prefix_lifetime hh hi hu cut hp]

end
end Ptx.Hopper.Tma
