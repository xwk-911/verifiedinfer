import Ptx.Hopper.UnifiedNativeOrder
import Ptx.Hopper.InputValues

namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

abbrev ProxyMemory := Access.ProxyMemory
abbrev ReadsFrom := Node → Location → Option Node
def readByte (resolve : Tma.SharedResolver) (descriptor : Access.DescriptorResolver) (candidate : Candidate) (node : Node) (loc : Location) : Option Symbolic.Byte :=
  (kind resolve descriptor candidate node).bind (fun k => k.readByte loc)
def writeByte (resolve : Tma.SharedResolver) (descriptor : Access.DescriptorResolver) (candidate : Candidate) (node : Node) (loc : Location) : Option Symbolic.Byte :=
  (kind resolve descriptor candidate node).bind (fun k => k.writeByte loc)
def sourceValue (resolve : Tma.SharedResolver) (descriptor : Access.DescriptorResolver) (candidate : Candidate)
    (initial : ProxyMemory) (read : Node) (loc : Location) : Option Node → Option Symbolic.Byte
  | none => some (initial read.proxy loc)
  | some writer => writeByte resolve descriptor candidate writer loc
def ReadAgreement (resolve : Tma.SharedResolver) (descriptor : Access.DescriptorResolver) (candidate : Candidate)
    (initial : ProxyMemory) (eligible : Node → Location → Prop) (rf : ReadsFrom) : Prop :=
  ∀ read loc value, eligible read loc → readByte resolve descriptor candidate read loc = some value →
    sourceValue resolve descriptor candidate initial read loc (rf read loc) = some value
def Accesses (resolve : Tma.SharedResolver) (descriptor : Access.DescriptorResolver) (candidate : Candidate) (node : Node) (loc : Location) : Prop :=
  (readByte resolve descriptor candidate node loc).isSome = true ∨ (writeByte resolve descriptor candidate node loc).isSome = true
def WritesAt (resolve : Tma.SharedResolver) (descriptor : Access.DescriptorResolver) (candidate : Candidate) (node : Node) (loc : Location) : Prop :=
  (writeByte resolve descriptor candidate node loc).isSome = true
def SameFootprint (resolve : Tma.SharedResolver) (descriptor : Access.DescriptorResolver) (candidate : Candidate) (left right : Node) : Prop :=
  (inventoryGraph resolve descriptor candidate).SameFootprint left right
def MutuallyScoped (resolve : Tma.SharedResolver) (descriptor : Access.DescriptorResolver) (candidate : Candidate) (a b : Node) : Prop :=
  ∃ sa sb, (kind resolve descriptor candidate a).bind Ptx.Event.Kind.strongScope = some sa ∧
    (kind resolve descriptor candidate b).bind Ptx.Event.Kind.strongScope = some sb ∧
    sa.Includes a.owner b.owner ∧ sb.Includes b.owner a.owner
def MorallyStrong (resolve : Tma.SharedResolver) (descriptor : Access.DescriptorResolver) (candidate : Candidate) : Node → Node → Prop
  | .base a,.base b => Access.MorallyStrong resolve descriptor candidate.view a b
  | a,b => a.proxy = b.proxy ∧ (a.memoryAgent = b.memoryAgent ∨ MutuallyScoped resolve descriptor candidate a b) ∧ SameFootprint resolve descriptor candidate a b

theorem base_read_preserved (resolve descriptor candidate node loc) :
    readByte resolve descriptor candidate (.base node) loc = Access.readByte resolve descriptor candidate.view node loc := rfl
theorem base_write_preserved (resolve descriptor candidate node loc) :
    writeByte resolve descriptor candidate (.base node) loc = Access.writeByte resolve descriptor candidate.view node loc := rfl
theorem native_write_none (resolve descriptor candidate issue operand loc) :
    writeByte resolve descriptor candidate (.wgmmaRead issue operand) loc = none := wgmma_no_write
theorem native_read_byte {resolve descriptor candidate issue mark call operand}
    (he : candidate.representativeAt issue = some (mark,call)) :
    readByte resolve descriptor candidate (.wgmmaRead issue operand) (Wgmma.operandLocation issue.thread.cta call operand) =
      some (call.operandBytes operand.index) := by
  simp only [readByte,wgmma_read_preserved he,Option.bind_some,Ptx.Event.Kind.readByte]
  simp [Ptx.Event.payloadByte]
theorem native_read_location {resolve descriptor candidate issue operand loc value}
    (hr : readByte resolve descriptor candidate (.wgmmaRead issue operand) loc = some value) :
    ∃ mark call, candidate.representativeAt issue = some (mark,call) ∧
      loc = Wgmma.operandLocation issue.thread.cta call operand ∧ value = call.operandBytes operand.index := by
  cases he : candidate.representativeAt issue with
  | none => simp [readByte,kind,he] at hr
  | some pair =>
    obtain ⟨hl,hv⟩ := Access.singleton_payload (by simpa only [readByte,kind,he,Option.map_some,Option.bind_some,Wgmma.operandKind,Ptx.Event.Kind.readByte] using hr)
    exact ⟨pair.1,pair.2,rfl,hl,hv⟩
theorem write_self_strong {resolve descriptor candidate node loc value}
    (hw : writeByte resolve descriptor candidate node loc = some value) : MorallyStrong resolve descriptor candidate node node := by
  cases node with
  | base node => exact Access.write_self_strong hw
  | wgmmaRead issue operand => rw [native_write_none] at hw; cases hw

end
end Ptx.Hopper.Unified
