import Ptx.Ampere.Thread
import Ptx.Event.Relations

/-! Non-bulk asynchronous accesses have distinct nodes, outside issuer program
order. This file defines source candidates and the augmented base graph; it does
not yet transfer the ordinary graph's rf/co/observer predicates to that graph.
Consequently graph publication alone is not a memory-value correctness theorem.
-/
namespace Ptx.Ampere
open Ptx.ISA
noncomputable section

structure CopyId where
  thread : ThreadId
  ordinal : Nat
  deriving Repr, DecidableEq
inductive Node
  | thread (event : Ptx.Event.EventId)
  | copyRead (operation : CopyId)
  | copyWrite (operation : CopyId)
  deriving Repr, DecidableEq
structure ThreadTrace where
  id : ThreadId
  oracle : Oracle
  count : Nat
  final : State
  events : List Event
structure Candidate where
  traces : List ThreadTrace

def Produced (code : List Instr) (params : Bindings) (block : Dim3) (t : ThreadTrace) : Prop :=
  run {id := t.id,params := params,block := block} t.oracle code t.count {} = .ok (t.final,t.events)
def WellFormed (code : List Instr) (launch : Scalar.Launch) (c : Candidate) : Prop :=
  launch.geometry.Valid ∧ (c.traces.map ThreadTrace.id).Nodup ∧
  (∀ t ∈ c.traces, t.id.Valid launch.geometry ∧ Produced code launch.params launch.geometry.block t) ∧
  ∀ id, id.Valid launch.geometry → ∃ t ∈ c.traces, t.id = id
def Complete (c : Candidate) : Prop := ∀ t ∈ c.traces, t.final.scalar.core.thread.status = .done
def Candidate.traceAt (c : Candidate) (id : ThreadId) : Option ThreadTrace :=
  c.traces.find? (fun t => t.id == id)
def Candidate.eventAt (c : Candidate) (id : Ptx.Event.EventId) : Option Event :=
  (c.traceAt id.thread).bind (fun t => t.events[id.serial]?)
def Candidate.copyAt (c : Candidate) (id : CopyId) : Option Copy :=
  (c.traceAt id.thread).bind (fun t => t.final.copies[id.ordinal]?)
def Candidate.Present (c : Candidate) : Node → Prop
  | .thread event => (c.eventAt event).isSome = true
  | .copyRead operation | .copyWrite operation => (c.copyAt operation).isSome = true

def Candidate.memoryKind (c : Candidate) : Node → Option Scalar.Kind
  | .thread event => (c.eventAt event).bind (fun e => match e with | .ordinary kind => some kind | _ => none)
  | .copyRead operation => (c.copyAt operation).map (fun op => .read op.src op.bytes)
  | .copyWrite operation => (c.copyAt operation).map (fun op => .write op.dst op.bytes)
def Candidate.readByte (c : Candidate) (node : Node) (loc : Location) : Option Symbolic.Byte :=
  (c.memoryKind node).bind (fun k => k.readByte loc)
def Candidate.writeByte (c : Candidate) (node : Node) (loc : Location) : Option Symbolic.Byte :=
  (c.memoryKind node).bind (fun k => k.writeByte loc)

def ProgramOrder (c : Candidate) : Node → Node → Prop
  | .thread a,.thread b => c.Present (.thread a) ∧ c.Present (.thread b) ∧ a.thread = b.thread ∧ a.serial < b.serial
  | _,_ => False
def BarrierSync (c : Candidate) : Node → Node → Prop
  | .thread a,.thread b => a.thread.cta = b.thread.cta ∧ ∃ id generation,
      c.eventAt a = some (.ordinary (.barrierArrival id generation)) ∧
      c.eventAt b = some (.ordinary (.barrierReturn id generation))
  | _,_ => False
def IssueBefore (c : Candidate) : Node → Node → Prop
  | .thread a,.copyRead operation => c.Present (.thread a) ∧ a.thread = operation.thread ∧
      ∃ serial op, c.eventAt ⟨operation.thread,serial⟩ = some (.issue operation.ordinal op) ∧
        c.copyAt operation = some op ∧ a.serial ≤ serial
  | _,_ => False
def CopyInternal (c : Candidate) : Node → Node → Prop
  | .copyRead a,.copyWrite b => a = b ∧ c.Present (.copyRead a)
  | _,_ => False
def WaitCovers (c : Candidate) (operation : CopyId) (event : Ptx.Event.EventId) : Prop :=
  event.thread = operation.thread ∧ ∃ op groups keep, c.copyAt operation = some op ∧
    c.eventAt event = some (.wait groups keep) ∧ op.group < groups-keep
def Completion (c : Candidate) : Node → Node → Prop
  | .copyWrite operation,.thread event => WaitCovers c operation event
  | _,_ => False
def BaseEdge (c : Candidate) (a b : Node) : Prop :=
  ProgramOrder c a b ∨ BarrierSync c a b ∨ IssueBefore c a b ∨ CopyInternal c a b ∨ Completion c a b
def BaseOrder (c : Candidate) : Node → Node → Prop := Ptx.Event.Path (BaseEdge c)

theorem copy_read_outside_program_order (c : Candidate) (id : CopyId) (other : Node) :
    ¬ ProgramOrder c (.copyRead id) other ∧ ¬ ProgramOrder c other (.copyRead id) := by
  cases other <;> simp [ProgramOrder]
theorem copy_write_outside_program_order (c : Candidate) (id : CopyId) (other : Node) :
    ¬ ProgramOrder c (.copyWrite id) other ∧ ¬ ProgramOrder c other (.copyWrite id) := by
  cases other <;> simp [ProgramOrder]
theorem issue_causal {c a operation} (h : IssueBefore c (.thread a) (.copyRead operation)) :
    BaseOrder c (.thread a) (.copyRead operation) := .single (.inr (.inr (.inl h)))
theorem copy_internal_causal {c operation} (h : c.Present (.copyRead operation)) :
    BaseOrder c (.copyRead operation) (.copyWrite operation) :=
  .single (.inr (.inr (.inr (.inl ⟨rfl,h⟩))))
theorem completed_before_wait {c operation event} (h : WaitCovers c operation event) :
    BaseOrder c (.copyWrite operation) (.thread event) := .single (.inr (.inr (.inr (.inr h))))
theorem thread_program_causal {c a b} (h : ProgramOrder c (.thread a) (.thread b)) :
    BaseOrder c (.thread a) (.thread b) := .single (.inl h)
theorem barrier_causal {c a b} (h : BarrierSync c (.thread a) (.thread b)) :
    BaseOrder c (.thread a) (.thread b) := .single (.inr (.inl h))

theorem publish_after_wait_and_barrier {c operation wait arrive leave read}
    (hw : WaitCovers c operation wait) (ha : ProgramOrder c (.thread wait) (.thread arrive))
    (hb : BarrierSync c (.thread arrive) (.thread leave)) (hr : ProgramOrder c (.thread leave) (.thread read)) :
    BaseOrder c (.copyWrite operation) (.thread read) :=
  .trans (completed_before_wait hw) (.trans (thread_program_causal ha)
    (.trans (barrier_causal hb) (thread_program_causal hr)))

theorem edge_from_copy_write {c operation node} (he : BaseEdge c (.copyWrite operation) node) :
    ∃ event, node = .thread event ∧ WaitCovers c operation event := by
  cases node with
  | thread event => exact ⟨event,rfl,by simpa only [BaseEdge,ProgramOrder,BarrierSync,IssueBefore,CopyInternal,
      Completion,false_or] using he⟩
  | copyRead id => simp [BaseEdge,ProgramOrder,BarrierSync,IssueBefore,CopyInternal,Completion] at he
  | copyWrite id => simp [BaseEdge,ProgramOrder,BarrierSync,IssueBefore,CopyInternal,Completion] at he

theorem path_no_outgoing {α : Type} {edge : α → α → Prop} {a b : α}
    (hp : Ptx.Event.Path edge a b) (hn : ∀ node, ¬ edge a node) : False := by
  revert hn
  induction hp with
  | single he => intro hn; exact hn _ he
  | trans _ _ ih _ => intro hn; exact ih hn

theorem no_wait_no_copy_order {c operation node} (hn : ∀ event, ¬ WaitCovers c operation event) :
    ¬ BaseOrder c (.copyWrite operation) node := by
  intro hp
  apply path_no_outgoing hp
  intro next he
  obtain ⟨event,_,hw⟩ := edge_from_copy_write he
  exact hn event hw

theorem open_group_not_covered {c operation event op groups keep}
    (hc : c.copyAt operation = some op) (he : c.eventAt event = some (.wait groups keep)) (hg : groups ≤ op.group) :
    ¬ WaitCovers c operation event := by
  rintro ⟨_,actual,g,k,hcopy,hwait,hlt⟩
  have hop : actual = op := Option.some.inj (hcopy.symm.trans hc)
  have hh : g = groups ∧ k = keep := by cases Option.some.inj (hwait.symm.trans he); exact ⟨rfl,rfl⟩
  rw [hop,hh.1,hh.2] at hlt
  omega

theorem recent_group_not_covered {c operation event op groups keep}
    (hc : c.copyAt operation = some op) (he : c.eventAt event = some (.wait groups keep))
    (hg : groups-keep ≤ op.group) : ¬ WaitCovers c operation event := by
  rintro ⟨_,actual,g,k,hcopy,hwait,hlt⟩
  have hop : actual = op := Option.some.inj (hcopy.symm.trans hc)
  have hh : g = groups ∧ k = keep := by cases Option.some.inj (hwait.symm.trans he); exact ⟨rfl,rfl⟩
  rw [hop,hh.1,hh.2] at hlt
  omega

theorem other_thread_wait_not_cover {c : Candidate} {operation : CopyId} {event : Ptx.Event.EventId}
    (hn : event.thread ≠ operation.thread) : ¬ WaitCovers c operation event := fun h => hn h.1

theorem commit_not_completion {c operation event group}
    (he : c.eventAt event = some (.commit group)) : ¬ WaitCovers c operation event := by
  rintro ⟨_,_,_,_,_,hwait,_⟩
  cases he.symm.trans hwait

theorem barrier_return_not_completion {c operation event bid generation}
    (he : c.eventAt event = some (.ordinary (.barrierReturn bid generation))) : ¬ WaitCovers c operation event := by
  rintro ⟨_,_,_,_,_,hwait,_⟩
  cases he.symm.trans hwait

end
end Ptx.Ampere
