import Ptx.Hopper.AccessGraph

/-! Input-value rules over the combined inventory. Initial views are indexed
by proxy; a generic initial value is not automatically a tensormap initial value.
Read agreement and eligibility are explicit memory-fragment obligations, not a
full Hopper admission predicate. In particular these rules neither establish
cross-proxy publication nor discharge races, observers or runtime encoding. -/
namespace Ptx.Hopper.Access
open Ptx.ISA
noncomputable section

abbrev ProxyMemory := Tma.Proxy → Location → Symbolic.Byte
abbrev ReadsFrom := Node → Location → Option Node

def sourceValue (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (initial : ProxyMemory) (read : Node) (loc : Location) : Option Node → Option Symbolic.Byte
  | none => some (initial read.proxy loc)
  | some writer => writeByte resolve descriptor c writer loc

def ReadAgreement (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (initial : ProxyMemory) (eligible : Node → Location → Prop) (rf : ReadsFrom) : Prop :=
  ∀ read loc value, eligible read loc → readByte resolve descriptor c read loc = some value →
    sourceValue resolve descriptor c initial read loc (rf read loc) = some value

/-- All writers, including ordinary/RMW and non-bulk operations, are checked.
Restricting this quantifier to the TMA subgraph would be unsound. -/
def Immutable (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate) (loc : Location) : Prop :=
  ∀ writer, writeByte resolve descriptor c writer loc = none

/-- Primitive zero-fill legality for the source-oracle representation. An OOB
byte has no memory read; read agreement alone cannot constrain its write value. -/
def ZeroFill (c : Candidate) : Prop :=
  ∀ id op, Tma.copyAt c id = some op → ∀ offset, offset < op.descriptor.bytes →
    Tma.sourceByte op.descriptor op.coordinates offset = none →
    op.payload[offset]? = some (.bits (byte 0))

theorem immutable_read_value {resolve descriptor c initial eligible rf read loc value}
    (ha : ReadAgreement resolve descriptor c initial eligible rf) (he : eligible read loc)
    (hr : readByte resolve descriptor c read loc = some value) (hi : Immutable resolve descriptor c loc) :
    value = initial read.proxy loc := by
  have hh := ha read loc value he hr
  cases hs : rf read loc with
  | none => exact (Option.some.inj (by simpa [sourceValue,hs] using hh)).symm
  | some writer =>
    have hw : writeByte resolve descriptor c writer loc = some value := by simpa [sourceValue,hs] using hh
    rw [hi writer] at hw
    cases hw

theorem immutable_descriptor {resolve descriptor c initial eligible rf id op expected}
    (ha : ReadAgreement resolve descriptor c initial eligible rf)
    (hc : Tma.copyAt c id = some op)
    (hs : TensorMap.Stored (initial .tensormap) (descriptor id.issue.thread op.descriptorAddress) expected)
    (he : ∀ offset, offset < 128 → eligible (.tma (.descriptor id)) ((descriptor id.issue.thread op.descriptorAddress).add offset))
    (hi : ∀ offset, offset < 128 → Immutable resolve descriptor c ((descriptor id.issue.thread op.descriptorAddress).add offset)) :
    op.descriptor = expected := by
  have hv := immutable_read_value ha (he 0 (by decide)) (descriptor_read hc (show 0 < 128 by decide)) (hi 0 (by decide))
  have hh : Symbolic.Byte.tensorMapPart op.descriptor 0 = .tensorMapPart expected 0 := hv.trans (hs 0 (by decide))
  exact (Symbolic.Byte.tensorMapPart.inj hh).1

theorem descriptor_agreement_from_memory {resolve descriptor c initial eligible rf maps}
    (ha : ReadAgreement resolve descriptor c initial eligible rf)
    (hm : ∀ id op, Tma.copyAt c id = some op → ∃ expected, maps op.descriptorAddress = some expected ∧
      TensorMap.Stored (initial .tensormap) (descriptor id.issue.thread op.descriptorAddress) expected)
    (he : ∀ id op, Tma.copyAt c id = some op → ∀ offset, offset < 128 →
      eligible (.tma (.descriptor id)) ((descriptor id.issue.thread op.descriptorAddress).add offset))
    (hi : ∀ id op, Tma.copyAt c id = some op → ∀ offset, offset < 128 →
      Immutable resolve descriptor c ((descriptor id.issue.thread op.descriptorAddress).add offset)) :
    Tma.DescriptorAgreement c maps := by
  intro id op hc
  obtain ⟨expected,hm,hs⟩ := hm id op hc
  have hh := immutable_descriptor ha hc hs (he id op hc) (hi id op hc)
  exact hh ▸ hm

theorem payload_agreement_from_memory_of_length {resolve descriptor c initial eligible rf}
    (shape : ∀ id op, Tma.copyAt c id = some op → op.payload.length = op.descriptor.bytes)
    (ha : ReadAgreement resolve descriptor c initial eligible rf)
    (hz : ZeroFill c)
    (he : ∀ id offset loc, Tma.readLocation c id offset = some loc → eligible (.tma (.read id offset)) loc)
    (hi : ∀ id offset loc, Tma.readLocation c id offset = some loc → Immutable resolve descriptor c loc) :
    Tma.PayloadAgreement c (initial .async) := by
  intro id op hc offset ho
  cases hs : Tma.sourceByte op.descriptor op.coordinates offset with
  | none => simpa [Tma.byteValue,hs] using hz id op hc offset ho hs
  | some loc =>
    have hl : Tma.readLocation c id offset = some loc := by simp [Tma.readLocation,hc,hs]
    have hlen := shape id op hc
    have hindex : offset < op.payload.length := by omega
    have hp : op.payload[offset]? = some op.payload[offset] := List.getElem?_eq_getElem hindex
    have hb : Tma.transferByte c id offset = some op.payload[offset] := by simp [Tma.transferByte,hc,hp]
    have hv := immutable_read_value ha (he id offset loc hl) (tensor_read hl hb) (hi id offset loc hl)
    simpa only [Tma.byteValue,hs,Node.proxy,Tma.Node.proxy] using hp.trans (congrArg some hv)

theorem payload_agreement_from_memory {resolve descriptor c initial eligible rf code launch}
    (hw : WellFormed code launch c)
    (ha : ReadAgreement resolve descriptor c initial eligible rf)
    (hz : ZeroFill c)
    (he : ∀ id offset loc, Tma.readLocation c id offset = some loc → eligible (.tma (.read id offset)) loc)
    (hi : ∀ id offset loc, Tma.readLocation c id offset = some loc → Immutable resolve descriptor c loc) :
    Tma.PayloadAgreement c (initial .async) :=
  payload_agreement_from_memory_of_length (fun _ _ hc => tma_copy_payload_length hw hc) ha hz he hi

theorem immutable_excludes_actual_write {resolve descriptor c loc writer value}
    (hi : Immutable resolve descriptor c loc) (hw : writeByte resolve descriptor c writer loc = some value) : False := by
  rw [hi writer] at hw
  cases hw

end
end Ptx.Hopper.Access
