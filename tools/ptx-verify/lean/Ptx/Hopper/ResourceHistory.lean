import Ptx.Hopper.Inventory
import Ptx.Hopper.Mbarrier

/-! Match finite resource histories to ALL actual candidate mbarrier events.
Each resource has its own order; this does not serialize ordinary memory or
establish proxy visibility. Future implicit TMA notifications need their own
source/operation identities and cannot be invented as explicit instructions. -/
namespace Ptx.Hopper
open Ptx.ISA
noncomputable section

def ThreadOrder (entries : List ResourceEntry) : Prop :=
  ∀ a ∈ entries, ∀ b ∈ entries, a.id.thread = b.id.thread → a.id.serial < b.id.serial →
    (entries.map ResourceEntry.id).idxOf a.id < (entries.map ResourceEntry.id).idxOf b.id
instance (entries) : Decidable (ThreadOrder entries) := by unfold ThreadOrder; infer_instance

structure HistoryValid (c : Candidate) (loc : Location) (entries : List ResourceEntry) : Prop where
  unique : (entries.map ResourceEntry.id).Nodup
  exhaustive : entries.Perm (c.barrierInventory loc)
  ordered : ThreadOrder entries
  protocol : Mbarrier.Admitted (entries.map ResourceEntry.operation)

def HistoryBefore (entries : List ResourceEntry) (a b : Ptx.Event.EventId) : Prop :=
  a ∈ entries.map ResourceEntry.id ∧ b ∈ entries.map ResourceEntry.id ∧
    (entries.map ResourceEntry.id).idxOf a < (entries.map ResourceEntry.id).idxOf b
instance (entries a b) : Decidable (HistoryBefore entries a b) := by unfold HistoryBefore; infer_instance

theorem history_sound {c loc entries} (h : HistoryValid c loc entries) {entry} (he : entry ∈ entries) :
    c.barrierAt entry.id = some ⟨loc,entry.operation⟩ :=
  barrier_inventory_iff.mp (h.exhaustive.mem_iff.mp he)

theorem history_complete {c loc entries} (h : HistoryValid c loc entries) {id op}
    (he : c.barrierAt id = some ⟨loc,op⟩) : ResourceEntry.mk id op ∈ entries :=
  h.exhaustive.mem_iff.mpr (barrier_inventory_iff.mpr he)

theorem same_event_same_resource {c locA locB left right}
    (ha : HistoryValid c locA left) (hb : HistoryValid c locB right) {a b}
    (hma : a ∈ left) (hmb : b ∈ right) (hid : a.id = b.id) :
    locA = locB ∧ a.operation = b.operation := by
  have hleft := history_sound ha hma
  have hright := history_sound hb hmb
  rw [hid] at hleft
  have he := Option.some.inj (hleft.symm.trans hright)
  exact ⟨congrArg BarrierEvent.location he,congrArg BarrierEvent.operation he⟩

theorem entry_unique {entries : List ResourceEntry} (hn : (entries.map ResourceEntry.id).Nodup)
    {a b} (ha : a ∈ entries) (hb : b ∈ entries) (hid : a.id = b.id) : a = b := by
  induction entries with
  | nil => simp at ha
  | cons first rest ih =>
    simp only [List.map_cons,List.nodup_cons] at hn
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact (hn.1 (List.mem_map.mpr ⟨b,hb,hid.symm⟩)).elim
    · exact (hn.1 (List.mem_map.mpr ⟨a,ha,hid⟩)).elim
    · exact ih hn.2 ha hb

theorem no_ghost_entry {c loc entries} (h : HistoryValid c loc entries) {id}
    (hn : c.barrierAt id = none) : ∀ entry ∈ entries, entry.id ≠ id := by
  intro entry he hid
  have hh := history_sound h he
  rw [hid,hn] at hh
  cases hh

theorem history_before_present {c loc entries a b} (h : HistoryValid c loc entries) (he : HistoryBefore entries a b) :
    c.Present a ∧ c.Present b := by
  obtain ⟨x,hx,hxa⟩ := List.mem_map.mp he.1
  obtain ⟨y,hy,hyb⟩ := List.mem_map.mp he.2.1
  exact ⟨hxa ▸ barrier_present (history_sound h hx),hyb ▸ barrier_present (history_sound h hy)⟩

theorem empty_history {c : Candidate} {loc} (he : c.barrierInventory loc = []) : HistoryValid c loc [] := by
  refine ⟨by simp,?_,?_,⟨none,rfl⟩⟩
  · rw [he]
  · simp [ThreadOrder]

theorem history_well_formed {c loc entries last} (h : HistoryValid c loc entries)
    (hr : Mbarrier.run none (entries.map ResourceEntry.operation) = some last) : Mbarrier.ObjectWellFormed last :=
  Mbarrier.run_wf (s := none) trivial hr

theorem protocol_prefix_step {ops : List BarrierOp} {initial last index op}
    (hr : Mbarrier.run initial ops = some last) (he : ops[index]? = some op) :
    ∃ before after, Mbarrier.run initial (ops.take index) = some before ∧ Mbarrier.step before op = some after := by
  induction index generalizing ops initial with
  | zero =>
    cases ops with
    | nil => simp at he
    | cons first rest =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at he
      subst first
      cases hs : Mbarrier.step initial op with
      | none => simp [Mbarrier.run,hs] at hr
      | some after => exact ⟨initial,after,rfl,hs⟩
  | succ index ih =>
    cases ops with
    | nil => simp at he
    | cons first rest =>
      simp only [List.getElem?_cons_succ] at he
      cases hs : Mbarrier.step initial first with
      | none => simp [Mbarrier.run,hs] at hr
      | some mid =>
        have ht : Mbarrier.run mid rest = some last := by simpa [Mbarrier.run,hs] using hr
        obtain ⟨before,after,hprefix,hstep⟩ := ih ht he
        refine ⟨before,after,?_,hstep⟩
        simpa [Mbarrier.run,hs] using hprefix

theorem successful_wait_has_actual_phase {c loc entries index id parity}
    (h : HistoryValid c loc entries)
    (he : entries[index]? = some ⟨id,.tryWaitParity parity true⟩) :
    ∃ state, c.barrierAt id = some ⟨loc,.tryWaitParity parity true⟩ ∧ Mbarrier.WellFormed state ∧
      Mbarrier.run none ((entries.map ResourceEntry.operation).take index) = some (some state) ∧
      0 < state.phase ∧ parity%2 ≠ state.phase%2 := by
  obtain ⟨last,hr⟩ := h.protocol
  have hop : (entries.map ResourceEntry.operation)[index]? = some (.tryWaitParity parity true) := by simp [List.getElem?_map,he]
  obtain ⟨before,after,hprefix,hstep⟩ := protocol_prefix_step hr hop
  cases before with
  | none => simp [Mbarrier.step] at hstep
  | some state =>
    have hw := Mbarrier.run_wf (s := none) trivial hprefix
    have hc := Mbarrier.successful_wait_completed hstep
    exact ⟨state,history_sound h (List.mem_of_getElem? he),hw,hprefix,hc.1,hc.2.1⟩

theorem arrive_has_actual_phase {c loc entries index id count}
    (h : HistoryValid c loc entries)
    (he : entries[index]? = some ⟨id,.arriveExpectTx count⟩) :
    ∃ state, c.barrierAt id = some ⟨loc,.arriveExpectTx count⟩ ∧ Mbarrier.WellFormed state ∧
      Mbarrier.run none ((entries.map ResourceEntry.operation).take index) = some (some state) ∧
      state.observed = true ∧ 0 < state.pending := by
  obtain ⟨last,hr⟩ := h.protocol
  have hop : (entries.map ResourceEntry.operation)[index]? = some (.arriveExpectTx count) := by simp [List.getElem?_map,he]
  obtain ⟨before,after,hprefix,hstep⟩ := protocol_prefix_step hr hop
  cases before with
  | none => simp [Mbarrier.step] at hstep
  | some state =>
    have hw := Mbarrier.run_wf (s := none) trivial hprefix
    have hc := Mbarrier.arrive_requires_observation hstep
    exact ⟨state,history_sound h (List.mem_of_getElem? he),hw,hprefix,hc.1,hc.2⟩

end
end Ptx.Hopper
