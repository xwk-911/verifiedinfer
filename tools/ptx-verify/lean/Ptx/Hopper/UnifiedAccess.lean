import Ptx.Hopper.UnifiedComponents
import Ptx.Hopper.WgmmaInputs
import Ptx.Hopper.ByteOrder

/-! Combined access inventory for source ordinary/RMW/non-bulk/TMA accesses
and source-issued WGMMA shared operand reads. One lane-zero representative
identifies a warpgroup operation; full collective coverage/equivalence must
still be checked separately. No implicit WGMMA read enters thread program
order. This supplies no new launch/completion/proxy/causality edges or complete
weak-memory admission; generic-only moral strength is not applicable here. -/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

def Candidate.wgmmaAt (candidate : Candidate) (id : Ptx.Event.EventId) : Option (Wgmma.Mark × Wgmma.Call) :=
  (candidate.eventAt id).bind (fun event => match event with | .mma mark call => some (mark,call) | _ => none)
def Candidate.representativeAt (candidate : Candidate) (id : Ptx.Event.EventId) : Option (Wgmma.Mark × Wgmma.Call) :=
  (candidate.wgmmaAt id).bind (fun pair => if pair.2.lane.val = 0 then some pair else none)
def Candidate.representatives (candidate : Candidate) : List Ptx.Event.EventId :=
  candidate.view.eventIds.filter (fun id => (candidate.representativeAt id).isSome)

inductive Node
  | base (node : Access.Node)
  | wgmmaRead (issue : Ptx.Event.EventId) (operand : Wgmma.OperandByte)
  deriving Repr, DecidableEq
def Node.proxy : Node → Tma.Proxy
  | .base node => node.proxy
  | .wgmmaRead _ _ => .async
def Node.memoryAgent : Node → MemoryGraph.Agent
  | .base node => node.memoryAgent
  | .wgmmaRead issue _ => .operation issue.thread 4 issue.serial
def Node.owner : Node → ThreadId
  | .base node => node.owner
  | .wgmmaRead issue _ => issue.thread
def kind (resolve : Tma.SharedResolver) (descriptor : Access.DescriptorResolver) (candidate : Candidate) : Node → Option Scalar.Kind
  | .base node => Access.kind resolve descriptor candidate.view node
  | .wgmmaRead issue operand => (candidate.representativeAt issue).map (fun pair => Wgmma.operandKind issue.thread.cta pair.2 operand)
def Present (candidate : Candidate) : Node → Prop
  | .base node => Access.Present candidate.view node
  | .wgmmaRead issue _ => (candidate.representativeAt issue).isSome = true
def ProgramOrder (candidate : Candidate) : Node → Node → Prop
  | .base left,.base right => Access.ProgramOrder candidate.view left right
  | _,_ => False
def inventoryGraph (resolve : Tma.SharedResolver) (descriptor : Access.DescriptorResolver) (candidate : Candidate) :
    MemoryGraph.Graph Node Symbolic.Byte := {
  kind := kind resolve descriptor candidate
  present := Present candidate
  agent := Node.memoryAgent
  po := ProgramOrder candidate
  base := fun _ _ => False
  complete := Complete candidate
}

theorem wgmmaAt_iff {candidate : Candidate} {id mark call} :
    candidate.wgmmaAt id = some (mark,call) ↔ candidate.eventAt id = some (.mma mark call) := by
  cases he : candidate.eventAt id with
  | none => simp [Candidate.wgmmaAt,he]
  | some event => cases event <;> simp [Candidate.wgmmaAt,he]
theorem representative_at {candidate : Candidate} {id mark call}
    (he : candidate.representativeAt id = some (mark,call)) :
    candidate.eventAt id = some (.mma mark call) ∧ call.lane.val = 0 := by
  unfold Candidate.representativeAt at he
  cases hx : candidate.wgmmaAt id with
  | none => simp [hx] at he
  | some pair =>
    simp only [hx,Option.bind_some] at he
    split at he
    · cases he
      exact ⟨wgmmaAt_iff.mp hx,by assumption⟩
    · cases he
theorem representative_at_of_event {candidate : Candidate} {id mark call}
    (he : candidate.eventAt id = some (.mma mark call)) (hl : call.lane.val = 0) :
    candidate.representativeAt id = some (mark,call) := by
  simp only [Candidate.representativeAt,wgmmaAt_iff.mpr he,Option.bind_some,ite_eq_left hl]
theorem representative_present_mem {candidate : Candidate} {id mark call}
    (he : candidate.representativeAt id = some (mark,call)) : id ∈ candidate.representatives := by
  have hx := (representative_at he).1
  apply List.mem_filter.mpr
  refine ⟨Hopper.present_mem_eventIds ((view_present_iff candidate id).mpr (by simp only [Candidate.Present,hx,Option.isSome_some])),?_⟩
  simp only [he,Option.isSome_some]
theorem base_inventory_preserved (resolve descriptor candidate node) :
    kind resolve descriptor candidate (.base node) = Access.kind resolve descriptor candidate.view node := rfl
theorem wgmma_read_preserved {resolve descriptor candidate issue mark call}
    (he : candidate.representativeAt issue = some (mark,call)) (operand : Wgmma.OperandByte) :
    kind resolve descriptor candidate (.wgmmaRead issue operand) =
      some (.read (Wgmma.operandLocation issue.thread.cta call operand) [call.operandBytes operand.index]) := by
  simp only [kind,he,Option.map_some,Wgmma.operandKind]
theorem wgmma_read_has_actual_step {candidate : Candidate} {code launch issue mark call}
    (hw : WellFormed code launch candidate) (he : candidate.representativeAt issue = some (mark,call)) :
    ∃ located, candidate.sourceAt code launch.params launch.geometry.block issue = some located ∧ located.kind = .mma mark call ∧
      ∃ oracle before after emitted,
        Wgmma.step {id := issue.thread,params := launch.params,block := launch.geometry.block} oracle code before = .ok (after,emitted) ∧
        Wgmma.Event.mma mark call ∈ emitted ∧ located.pc = before.base.scalar.core.thread.pc :=
  source_event hw (representative_at he).1
theorem wgmma_no_write {resolve descriptor candidate issue operand location} :
    (kind resolve descriptor candidate (.wgmmaRead issue operand)).bind (fun k => k.writeByte location) = none := by
  cases he : candidate.representativeAt issue <;> simp [kind,he,Wgmma.operandKind,Ptx.Event.Kind.writeByte]
theorem wgmma_read_outside_program_order (candidate : Candidate) (issue : Ptx.Event.EventId) (operand : Wgmma.OperandByte) (other : Node) :
    ¬ProgramOrder candidate (.wgmmaRead issue operand) other ∧ ¬ProgramOrder candidate other (.wgmmaRead issue operand) := by
  cases other <;> simp [ProgramOrder]
theorem wgmma_agent_distinct_from_tma (issue : Ptx.Event.EventId) (copy : Tma.CopyId) (offset : Nat) (operand : Wgmma.OperandByte) :
    (Node.wgmmaRead issue operand).memoryAgent ≠ (Node.base (.tma (.read copy offset))).memoryAgent := by
  simp [Node.memoryAgent,Access.Node.memoryAgent]

end
end Ptx.Hopper.Unified
