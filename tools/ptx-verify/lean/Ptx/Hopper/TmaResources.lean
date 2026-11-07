import Ptx.Hopper.TmaSource

/-! Resource histories with distinct source-operation and implicit-transfer
notification identities. Notifications are generated from actual TMA issues;
counts and barrier addresses are not supplied by a matching oracle. -/
namespace Ptx.Hopper.Tma
open Ptx.ISA
noncomputable section

inductive Origin
  | source (event : Ptx.Event.EventId)
  | notification (copy : CopyId)
  deriving Repr, DecidableEq
structure Entry where
  origin : Origin
  operation : BarrierOp
  deriving Repr, DecidableEq

def Origin.node : Origin → Node
  | .source event => .source event
  | .notification id => .notify id

def resourceAt (resolve : SharedResolver) (c : Candidate) : Origin → Option BarrierEvent
  | .source event => c.barrierAt event
  | .notification id => notification resolve c id

def origins (c : Candidate) : List Origin :=
  c.barrierRecords.map (fun r => .source r.id) ++ (copies c).map Origin.notification

def inventory (resolve : SharedResolver) (c : Candidate) (loc : Location) : List Entry :=
  (origins c).filterMap (fun origin => (resourceAt resolve c origin).bind (fun event =>
    if loc = event.location then some ⟨origin,event.operation⟩ else none))

def SourceBefore : Origin → Origin → Prop
  | .source a,.source b => a.thread = b.thread ∧ a.serial < b.serial
  | _,_ => False
instance (a b) : Decidable (SourceBefore a b) := by cases a <;> cases b <;> simp only [SourceBefore] <;> infer_instance

def SourceOrder (entries : List Entry) : Prop :=
  ∀ a ∈ entries, ∀ b ∈ entries, SourceBefore a.origin b.origin →
    (entries.map Entry.origin).idxOf a.origin < (entries.map Entry.origin).idxOf b.origin
instance (entries) : Decidable (SourceOrder entries) := by unfold SourceOrder; infer_instance

structure HistoryValid (resolve : SharedResolver) (c : Candidate) (loc : Location) (entries : List Entry) : Prop where
  unique : (entries.map Entry.origin).Nodup
  exhaustive : entries.Perm (inventory resolve c loc)
  ordered : SourceOrder entries
  protocol : Mbarrier.Admitted (entries.map Entry.operation)

def Before (entries : List Entry) (a b : Origin) : Prop :=
  a ∈ entries.map Entry.origin ∧ b ∈ entries.map Entry.origin ∧
    (entries.map Entry.origin).idxOf a < (entries.map Entry.origin).idxOf b
instance (entries a b) : Decidable (Before entries a b) := by unfold Before; infer_instance

theorem source_resource_mem {c : Candidate} {event data} (he : c.barrierAt event = some data) : Origin.source event ∈ origins c := by
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨⟨event,data⟩,barrier_record_iff.mpr he,rfl⟩

theorem origin_mem {resolve c origin data} (he : resourceAt resolve c origin = some data) : origin ∈ origins c := by
  cases origin with
  | source event => exact source_resource_mem he
  | notification id =>
    obtain ⟨op,hcopy,_,_⟩ := notification_has_actual_copy he
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨id,copy_present_mem hcopy,rfl⟩

theorem inventory_iff {resolve c loc origin op} :
    Entry.mk origin op ∈ inventory resolve c loc ↔ resourceAt resolve c origin = some ⟨loc,op⟩ := by
  constructor
  · intro h
    obtain ⟨actual,_,hget⟩ := List.mem_filterMap.mp h
    cases he : resourceAt resolve c actual with
    | none => simp [he] at hget
    | some data =>
      simp only [he,Option.bind_some] at hget
      split at hget
      · rename_i hl
        simp only [Option.some.injEq,Entry.mk.injEq] at hget
        rcases actual with event | id <;> rcases data with ⟨where_,what⟩ <;>
          cases hget.1 <;> cases hget.2 <;> cases hl <;> exact he
      · cases hget
  · intro he
    exact List.mem_filterMap.mpr ⟨origin,origin_mem he,by simp [he]⟩

theorem history_sound {resolve c loc entries} (h : HistoryValid resolve c loc entries) {entry} (he : entry ∈ entries) :
    resourceAt resolve c entry.origin = some ⟨loc,entry.operation⟩ :=
  inventory_iff.mp (h.exhaustive.mem_iff.mp he)

theorem history_complete {resolve c loc entries origin op} (h : HistoryValid resolve c loc entries)
    (he : resourceAt resolve c origin = some ⟨loc,op⟩) : Entry.mk origin op ∈ entries :=
  h.exhaustive.mem_iff.mpr (inventory_iff.mpr he)

theorem notification_history_has_actual_copy {resolve c loc entries id op}
    (h : HistoryValid resolve c loc entries) (he : Entry.mk (.notification id) op ∈ entries) :
    ∃ copy, copyAt c id = some copy ∧ loc = resolve id.issue.thread copy.barrier ∧ op = .completeTx copy.descriptor.bytes :=
  notification_has_actual_copy (history_sound h he)

theorem notification_matches_payload {resolve c code launch id event}
    (hw : WellFormed code launch c) (he : notification resolve c id = some event) :
    ∃ copy, copyAt c id = some copy ∧ event.operation = .completeTx copy.payload.length := by
  obtain ⟨copy,hcopy,_,hop⟩ := notification_has_actual_copy he
  refine ⟨copy,hcopy,?_⟩
  simpa only [tma_copy_payload_length hw hcopy] using hop

theorem no_ghost_notification {resolve c loc entries id} (h : HistoryValid resolve c loc entries)
    (hn : copyAt c id = none) : ∀ op, Entry.mk (.notification id) op ∉ entries := by
  intro op he
  obtain ⟨copy,hcopy,_,_⟩ := notification_history_has_actual_copy h he
  rw [hn] at hcopy
  cases hcopy

theorem notification_not_source_order (id : CopyId) (event : Ptx.Event.EventId) :
    ¬ SourceBefore (.notification id) (.source event) ∧ ¬ SourceBefore (.source event) (.notification id) := by simp [SourceBefore]

theorem history_successful_wait_phase {resolve c loc entries index event parity}
    (h : HistoryValid resolve c loc entries)
    (he : entries[index]? = some ⟨.source event,.tryWaitParity parity true⟩) :
    ∃ state, c.barrierAt event = some ⟨loc,.tryWaitParity parity true⟩ ∧ Mbarrier.WellFormed state ∧
      Mbarrier.run none ((entries.map Entry.operation).take index) = some (some state) ∧
      0 < state.phase ∧ parity%2 ≠ state.phase%2 := by
  obtain ⟨last,hr⟩ := h.protocol
  have hop : (entries.map Entry.operation)[index]? = some (.tryWaitParity parity true) := by simp [List.getElem?_map,he]
  obtain ⟨before,after,hprefix,hstep⟩ := protocol_prefix_step hr hop
  cases before with
  | none => simp [Mbarrier.step] at hstep
  | some state =>
    have hw := Mbarrier.run_wf (s := none) trivial hprefix
    have hc := Mbarrier.successful_wait_completed hstep
    exact ⟨state,history_sound h (List.mem_of_getElem? he),hw,hprefix,hc.1,hc.2.1⟩

end
end Ptx.Hopper.Tma
