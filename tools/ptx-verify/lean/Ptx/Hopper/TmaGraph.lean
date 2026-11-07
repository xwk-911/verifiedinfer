import Ptx.Hopper.ResourceControl

/-! TMA-only byte/access graph, derived from actual source issue events. Raw
cluster destination/barrier addresses are resolved by an explicit layout map;
no assumption that every cluster address belongs to the issuer is hidden here.
This is not yet the combined ordinary/TMA memory-consistency adapter. -/
namespace Ptx.Hopper.Tma
open Ptx.ISA
noncomputable section

structure CopyId where
  issue : Ptx.Event.EventId
  deriving Repr, DecidableEq
inductive Node
  | source (id : Ptx.Event.EventId)
  | descriptor (id : CopyId)
  | read (id : CopyId) (offset : Nat)
  | write (id : CopyId) (offset : Nat)
  | notify (id : CopyId)
  deriving Repr, DecidableEq
inductive Agent
  | thread (id : ThreadId)
  | transfer (id : CopyId)
  deriving Repr, DecidableEq

def Node.agent : Node → Agent
  | .source event => .thread event.thread
  | .descriptor id | .read id _ | .write id _ | .notify id => .transfer id
def Node.proxy : Node → Proxy
  | .descriptor _ => .tensormap
  | .read _ _ | .write _ _ => .async
  | .source _ | .notify _ => .generic

def copyAt (c : Candidate) (id : CopyId) : Option TmaCopy :=
  (c.eventAt id.issue).bind (fun event => match event with | .tmaIssue copy => some copy | _ => none)
def copies (c : Candidate) : List CopyId := c.eventIds.filterMap (fun event =>
  match c.eventAt event with | some (.tmaIssue _) => some ⟨event⟩ | _ => none)
abbrev SharedResolver := ThreadId → Nat → Location

def localShared : SharedResolver := fun id address => ⟨.shared id.cta,address⟩

def readLocation (c : Candidate) (id : CopyId) (offset : Nat) : Option Location :=
  (copyAt c id).bind (fun op => sourceByte op.descriptor op.coordinates offset)
def writeLocation (resolve : SharedResolver) (c : Candidate) (id : CopyId) (offset : Nat) : Option Location :=
  (copyAt c id).bind (fun op => if offset < op.descriptor.bytes then some ((resolve id.issue.thread op.destination).add offset) else none)
def transferByte (c : Candidate) (id : CopyId) (offset : Nat) : Option Symbolic.Byte :=
  (copyAt c id).bind (fun op => op.payload[offset]?)

def notification (resolve : SharedResolver) (c : Candidate) (id : CopyId) : Option BarrierEvent :=
  (copyAt c id).map (fun op => ⟨resolve id.issue.thread op.barrier,.completeTx op.descriptor.bytes⟩)

def WritePresent (c : Candidate) (id : CopyId) (offset : Nat) : Prop :=
  match copyAt c id with | some op => offset < op.descriptor.bytes | none => False
instance (c id offset) : Decidable (WritePresent c id offset) := by unfold WritePresent; split <;> infer_instance

def Present (c : Candidate) : Node → Prop
  | .source event => c.Present event
  | .descriptor id | .notify id => (copyAt c id).isSome = true
  | .read id offset => (readLocation c id offset).isSome = true
  | .write id offset => WritePresent c id offset

/-- Issuer program order relates only source events. All implicit accesses and
notification remain distinct operation nodes. -/
def ProgramOrder (c : Candidate) : Node → Node → Prop
  | .source a,.source b => Hopper.ProgramOrder c a b
  | _,_ => False

inductive InternalEdge (c : Candidate) : Node → Node → Prop
  | issue {id} : (copyAt c id).isSome = true → InternalEdge c (.source id.issue) (.descriptor id)
  | descriptorRead {id offset} : (readLocation c id offset).isSome = true → InternalEdge c (.descriptor id) (.read id offset)
  | descriptorWrite {id offset} : WritePresent c id offset → InternalEdge c (.descriptor id) (.write id offset)
  | data {id offset} : (readLocation c id offset).isSome = true → InternalEdge c (.read id offset) (.write id offset)
  | complete {id offset} : WritePresent c id offset → InternalEdge c (.write id offset) (.notify id)

/-- This checks byte agreement only. Initial descriptor agreement, proxy/order,
race/coherence, observer conditions and allocation are separate obligations. -/
def PayloadAgreement (c : Candidate) (initial : Location → Symbolic.Byte) : Prop :=
  ∀ id op, copyAt c id = some op → ∀ offset, offset < op.descriptor.bytes →
    op.payload[offset]? = some (byteValue op.descriptor op.coordinates initial offset)

def DescriptorAgreement (c : Candidate) (maps : Nat → Option Descriptor2D) : Prop :=
  ∀ id op, copyAt c id = some op → maps op.descriptorAddress = some op.descriptor

theorem same_descriptor_snapshot {c maps left right a b} (h : DescriptorAgreement c maps)
    (ha : copyAt c left = some a) (hb : copyAt c right = some b) (he : a.descriptorAddress = b.descriptorAddress) :
    a.descriptor = b.descriptor := by
  have hx := h left a ha
  have hy := h right b hb
  rw [he] at hx
  exact Option.some.inj (hx.symm.trans hy)

theorem copyAt_iff {c id op} : copyAt c id = some op ↔ c.eventAt id.issue = some (.tmaIssue op) := by
  cases he : c.eventAt id.issue with
  | none => simp [copyAt,he]
  | some event => cases event <;> simp [copyAt,he]

theorem copy_present_mem {c id op} (he : copyAt c id = some op) : id ∈ copies c := by
  apply List.mem_filterMap.mpr
  exact ⟨id.issue,present_mem_eventIds (by simp [Candidate.Present,copyAt_iff.mp he]),by simp [copyAt_iff.mp he]⟩

theorem copy_has_source {c : Candidate} {code launch id op}
    (hw : WellFormed code launch c) (he : copyAt c id = some op) :
    ∃ located, c.sourceAt code launch.params launch.geometry.block id.issue = some located ∧ located.kind = .tmaIssue op ∧
      ∃ oracle before after emitted, step {id := id.issue.thread,params := launch.params,block := launch.geometry.block} oracle
        code before = .ok (after,emitted) ∧ Event.tmaIssue op ∈ emitted ∧ located.pc = before.scalar.core.thread.pc :=
  source_event hw (copyAt_iff.mp he)

theorem notification_exact {resolve c id op} (he : copyAt c id = some op) :
    notification resolve c id = some ⟨resolve id.issue.thread op.barrier,.completeTx op.descriptor.bytes⟩ := by simp [notification,he]

theorem notification_has_actual_copy {resolve c id event} (he : notification resolve c id = some event) :
    ∃ op, copyAt c id = some op ∧ event.location = resolve id.issue.thread op.barrier ∧ event.operation = .completeTx op.descriptor.bytes := by
  unfold notification at he
  cases hc : copyAt c id with
  | none => simp [hc] at he
  | some op =>
    simp only [hc,Option.map_some,Option.some.injEq] at he
    cases he
    exact ⟨op,rfl,rfl,rfl⟩

theorem transfer_outside_program_order (c : Candidate) (id : CopyId) (offset : Nat) (other : Node) :
    ¬ ProgramOrder c (.descriptor id) other ∧ ¬ ProgramOrder c other (.descriptor id) ∧
    ¬ ProgramOrder c (.read id offset) other ∧ ¬ ProgramOrder c other (.read id offset) ∧
    ¬ ProgramOrder c (.write id offset) other ∧ ¬ ProgramOrder c other (.write id offset) ∧
    ¬ ProgramOrder c (.notify id) other ∧ ¬ ProgramOrder c other (.notify id) := by
  cases other <;> simp [ProgramOrder]

theorem descriptor_not_data_proxy (id : CopyId) (offset : Nat) :
    (Node.descriptor id).proxy ≠ (Node.read id offset).proxy ∧ (Node.descriptor id).proxy ≠ (Node.write id offset).proxy := by simp [Node.proxy]

theorem transfer_agent_distinct (id : CopyId) (offset : Nat) :
    (Node.source id.issue).agent ≠ (Node.read id offset).agent ∧
    (Node.source id.issue).agent ≠ (Node.write id offset).agent ∧
    (Node.source id.issue).agent ≠ (Node.notify id).agent := by simp [Node.agent]

end
end Ptx.Hopper.Tma
