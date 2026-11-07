import Ptx.Hopper.TmaControl
import Ptx.ISA.TensorMapStorage

/-! Combined access inventory: source ordinary/RMW accesses, source-issued
non-bulk cp.async accesses, opaque descriptor reads, and per-byte TMA accesses.
This deliberately supplies no cross-proxy memory order or consistency claim.
The generic-only MemoryGraph.MorallyStrong predicate must not be applied to
this inventory without a proxy-aware adapter. -/
namespace Ptx.Hopper.Access
open Ptx.ISA
noncomputable section

inductive Node
  | tma (node : Tma.Node)
  | copyRead (issue : Ptx.Event.EventId)
  | copyWrite (issue : Ptx.Event.EventId)
  deriving Repr, DecidableEq

def Node.proxy : Node → Tma.Proxy
  | .tma node => node.proxy
  | .copyRead _ | .copyWrite _ => .generic

inductive Agent
  | thread (id : ThreadId)
  | nonbulk (issue : Ptx.Event.EventId)
  | tensor (id : Tma.CopyId)
  deriving Repr, DecidableEq

def Node.agent : Node → Agent
  | .tma (.source event) => .thread event.thread
  | .tma (.descriptor id) | .tma (.read id _) | .tma (.write id _) | .tma (.notify id) => .tensor id
  | .copyRead event | .copyWrite event => .nonbulk event

def copyAt (c : Candidate) (event : Ptx.Event.EventId) : Option Ampere.Copy :=
  (c.eventAt event).bind (fun e => match e with | .ampere (.issue _ op) => some op | _ => none)

/-- Descriptor pointers are generic addresses. Global-only examples may choose
the global resolver; support for param/const must use a different explicit map. -/
abbrev DescriptorResolver := ThreadId → Nat → Location
def globalDescriptor : DescriptorResolver := fun _ address => ⟨.global,address⟩

def kind (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate) : Node → Option Scalar.Kind
  | .tma (.source event) => (c.eventAt event).bind (fun e => match e with | .ampere (.ordinary k) => some k | _ => none)
  | .tma (.descriptor id) => (Tma.copyAt c id).map (fun op => .read (descriptor id.issue.thread op.descriptorAddress) (TensorMap.encode op.descriptor))
  | .tma (.read id offset) => do
      let location ← Tma.readLocation c id offset
      let value ← Tma.transferByte c id offset
      pure (.read location [value])
  | .tma (.write id offset) => do
      let location ← Tma.writeLocation resolve c id offset
      let value ← Tma.transferByte c id offset
      pure (.write location [value])
  | .tma (.notify _) => none
  | .copyRead issue => (copyAt c issue).map (fun op => .read op.src op.bytes)
  | .copyWrite issue => (copyAt c issue).map (fun op => .write op.dst op.bytes)

def readByte (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate) (node : Node) (loc : Location) : Option Symbolic.Byte :=
  (kind resolve descriptor c node).bind (fun k => k.readByte loc)
def writeByte (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate) (node : Node) (loc : Location) : Option Symbolic.Byte :=
  (kind resolve descriptor c node).bind (fun k => k.writeByte loc)

def Present (c : Candidate) : Node → Prop
  | .tma node => Tma.Present c node
  | .copyRead issue | .copyWrite issue => (copyAt c issue).isSome = true

def ProgramOrder (c : Candidate) : Node → Node → Prop
  | .tma a,.tma b => Tma.ProgramOrder c a b
  | _,_ => False

theorem ordinary_preserved {resolve descriptor c event k} (he : c.eventAt event = some (.ampere (.ordinary k))) :
    kind resolve descriptor c (.tma (.source event)) = some k := by simp [kind,he]

theorem nonbulk_preserved {resolve descriptor c event ordinal op} (he : c.eventAt event = some (.ampere (.issue ordinal op))) :
    kind resolve descriptor c (.copyRead event) = some (.read op.src op.bytes) ∧
    kind resolve descriptor c (.copyWrite event) = some (.write op.dst op.bytes) := by simp [kind,copyAt,he]

theorem nonbulk_has_actual_issue {c event op} (he : copyAt c event = some op) :
    ∃ ordinal, c.eventAt event = some (.ampere (.issue ordinal op)) := by
  unfold copyAt at he
  cases hh : c.eventAt event with
  | none => simp [hh] at he
  | some e =>
    cases e with
    | ampere e =>
      cases e <;> simp_all
    | tmaIssue _ | proxyFenceAsyncShared _ | barrier _ | wgmma _ => simp [hh] at he

theorem descriptor_read {resolve descriptor c id op offset} (he : Tma.copyAt c id = some op) (ho : offset < 128) :
    readByte resolve descriptor c (.tma (.descriptor id)) ((descriptor id.issue.thread op.descriptorAddress).add offset) =
      some (.tensorMapPart op.descriptor offset) := by
  simp only [readByte,kind,he,Option.map_some,Option.bind_some,Ptx.Event.Kind.readByte]
  exact TensorMap.encoded_byte _ _ ho

theorem tensor_read {resolve descriptor c id offset loc value}
    (hl : Tma.readLocation c id offset = some loc) (hv : Tma.transferByte c id offset = some value) :
    readByte resolve descriptor c (.tma (.read id offset)) loc = some value := by
  simp [readByte,kind,hl,hv,Ptx.Event.Kind.readByte,Ptx.Event.payloadByte]

theorem tensor_write {resolve descriptor c id offset loc value}
    (hl : Tma.writeLocation resolve c id offset = some loc) (hv : Tma.transferByte c id offset = some value) :
    writeByte resolve descriptor c (.tma (.write id offset)) loc = some value := by
  simp [writeByte,kind,hl,hv,Ptx.Event.Kind.writeByte,Ptx.Event.payloadByte]

theorem singleton_payload {base loc : Location} {value observed : Symbolic.Byte}
    (he : Ptx.Event.payloadByte base [value] loc = some observed) : loc = base ∧ observed = value := by
  have hb := Ptx.Event.payloadByte_bounds he
  have hl : loc = base := by
    rcases loc with ⟨space,address⟩
    rcases base with ⟨baseSpace,baseAddress⟩
    simp only [List.length_singleton] at hb
    simp only [Location.mk.injEq]
    exact ⟨hb.1.symm,by omega⟩
  subst loc
  simpa [Ptx.Event.payloadByte] using he.symm

theorem tensor_read_no_write (resolve descriptor c id offset loc) :
    writeByte resolve descriptor c (.tma (.read id offset)) loc = none := by
  cases hl : Tma.readLocation c id offset <;> cases hv : Tma.transferByte c id offset <;>
    simp [writeByte,kind,hl,hv,Ptx.Event.Kind.writeByte]

theorem descriptor_no_write (resolve descriptor c id loc) :
    writeByte resolve descriptor c (.tma (.descriptor id)) loc = none := by
  cases hc : Tma.copyAt c id <;> simp [writeByte,kind,hc,Ptx.Event.Kind.writeByte]

theorem implicit_outside_program_order (c : Candidate) (issue : Ptx.Event.EventId) (other : Node) :
    ¬ ProgramOrder c (.copyRead issue) other ∧ ¬ ProgramOrder c other (.copyRead issue) ∧
    ¬ ProgramOrder c (.copyWrite issue) other ∧ ¬ ProgramOrder c other (.copyWrite issue) := by
  cases other <;> simp [ProgramOrder]

theorem nonbulk_tensor_agents_distinct (event : Ptx.Event.EventId) (id : Tma.CopyId) (offset : Nat) :
    (Node.copyRead event).agent ≠ (Node.tma (.read id offset)).agent := by simp [Node.agent]

theorem tensor_byte_present_of_length {resolve descriptor c id op offset}
    (hlen : op.payload.length = op.descriptor.bytes)
    (hc : Tma.copyAt c id = some op) (ho : offset < op.descriptor.bytes) :
    ∃ value, Tma.transferByte c id offset = some value ∧
      kind resolve descriptor c (.tma (.write id offset)) =
        some (.write ((resolve id.issue.thread op.destination).add offset) [value]) := by
  have hb : offset < op.payload.length := by omega
  have hv : Tma.transferByte c id offset = some op.payload[offset] := by
    simp [Tma.transferByte,hc,List.getElem?_eq_getElem hb]
  exact ⟨op.payload[offset],hv,by simp [kind,Tma.writeLocation,hc,ho,hv]⟩

theorem tensor_byte_present {resolve descriptor c code launch id op offset}
    (hw : WellFormed code launch c) (hc : Tma.copyAt c id = some op) (ho : offset < op.descriptor.bytes) :
    ∃ value, Tma.transferByte c id offset = some value ∧
      kind resolve descriptor c (.tma (.write id offset)) =
        some (.write ((resolve id.issue.thread op.destination).add offset) [value]) :=
  tensor_byte_present_of_length (tma_copy_payload_length hw hc) hc ho

theorem out_of_bounds_has_no_read {resolve descriptor c id offset}
    (hl : Tma.readLocation c id offset = none) : kind resolve descriptor c (.tma (.read id offset)) = none := by
  simp [kind,hl]

end
end Ptx.Hopper.Access
