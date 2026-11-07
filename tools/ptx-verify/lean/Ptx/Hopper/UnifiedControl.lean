import Ptx.Hopper.UnifiedNativeOrder
import Ptx.Hopper.TmaControl

/-! Native construct control, kept separate from byte/proxy visibility.
Each synchronous native instruction has an arrival endpoint and a source
return endpoint. PTX .sync rendezvous is warp-local; .aligned participation
is checked over the full physical warpgroup by SchedulesAdmitted. Implicit
operand reads occur after issue and before source-matched native completion.
This is construct consistency, not a proof of hardware/UB correspondence.
-/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

def Candidate.nativeSignatureAt (candidate : Candidate) (id : Ptx.Event.EventId) : Option Wgmma.SourceSignature :=
  (candidate.eventAt id).bind (fun event => (Wgmma.eventSignature event).map Wgmma.alignedSignature)
def SamePhysicalWarp (block : Dim3) (left right : ThreadId) : Prop :=
  left.cta = right.cta ∧ left.tid.linear block/32 = right.tid.linear block/32
instance (block left right) : Decidable (SamePhysicalWarp block left right) := by unfold SamePhysicalWarp; infer_instance
def NativeSync (block : Dim3) (candidate : Candidate) (left right : Ptx.Event.EventId) : Prop :=
  SamePhysicalWarp block left.thread right.thread ∧ ∃ signature,
    candidate.nativeSignatureAt left = some signature ∧ candidate.nativeSignatureAt right = some signature

inductive ControlNode
  | base (node : Tma.Node)
  | arrival (event : Ptx.Event.EventId)
  | operand (issue : Ptx.Event.EventId) (byte : Wgmma.OperandByte)
  deriving Repr, DecidableEq
def NativeArrival (candidate : Candidate) : ControlNode → ControlNode → Prop
  | .base (.source before),.arrival event => Hopper.ProgramOrder candidate.view before event ∧ (candidate.nativeSignatureAt event).isSome = true
  | _,_ => False
def NativeRendezvous (block : Dim3) (candidate : Candidate) : ControlNode → ControlNode → Prop
  | .arrival left,.base (.source right) => NativeSync block candidate left right
  | _,_ => False
def NativeIssue (candidate : Candidate) : ControlNode → ControlNode → Prop
  | .base (.source event),.operand issue _ => event = issue ∧ (candidate.representativeAt issue).isSome = true
  | _,_ => False
def NativeFinish (candidate : Candidate) : ControlNode → ControlNode → Prop
  | .operand issue _,.base (.source wait) => WgmmaCompletedAt candidate issue wait
  | _,_ => False
def ControlEdge (block : Dim3) (candidate : Candidate) (histories : Location → List Tma.Entry)
    (left right : ControlNode) : Prop :=
  (match left,right with | .base a,.base b => Tma.ControlEdge candidate.view histories a b | _,_ => False) ∨
  NativeArrival candidate left right ∨ NativeRendezvous block candidate left right ∨ NativeIssue candidate left right ∨ NativeFinish candidate left right
def ControlAcyclic (block : Dim3) (candidate : Candidate) (histories : Location → List Tma.Entry) : Prop :=
  ∀ node, ¬Ptx.Event.Path (ControlEdge block candidate histories) node node
def ControlAdmitted (block : Dim3) (candidate : Candidate) (histories : Location → List Tma.Entry) : Prop :=
  SchedulesAdmitted block candidate ∧ ControlAcyclic block candidate histories

theorem native_signature_actual {candidate : Candidate} {id signature}
    (he : candidate.nativeSignatureAt id = some signature) :
    ∃ event raw, candidate.eventAt id = some event ∧ Wgmma.eventSignature event = some raw ∧ Wgmma.alignedSignature raw = signature := by
  simp only [Candidate.nativeSignatureAt,Option.bind_eq_some_iff,Option.map_eq_some_iff] at he
  obtain ⟨event,hh,raw,hs,ha⟩ := he
  exact ⟨event,raw,hh,hs,ha⟩
theorem native_signature_present {candidate : Candidate} {id signature}
    (he : candidate.nativeSignatureAt id = some signature) : candidate.Present id := by
  obtain ⟨event,_,hh,_⟩ := native_signature_actual he
  simp only [Candidate.Present,hh,Option.isSome_some]
theorem native_signature_actual_pc {candidate code launch id signature}
    (hw : WellFormed code launch candidate) (he : candidate.nativeSignatureAt id = some signature) :
    candidate.sourcePC code launch.params launch.geometry.block id = some signature.pc := by
  obtain ⟨event,raw,hh,hs,rfl⟩ := native_signature_actual he
  exact source_signature_actual_pc (signature := raw) hw hh hs
theorem native_sync_same_warp {block candidate left right} (hs : NativeSync block candidate left right) :
    SamePhysicalWarp block left.thread right.thread := hs.1
theorem native_sync_reflexive {block candidate id signature}
    (he : candidate.nativeSignatureAt id = some signature) : NativeSync block candidate id id :=
  ⟨⟨rfl,rfl⟩,signature,he,he⟩
theorem native_sync_symmetric {block candidate left right} (hs : NativeSync block candidate left right) : NativeSync block candidate right left := by
  obtain ⟨⟨hc,hw⟩,signature,hl,hr⟩ := hs
  exact ⟨⟨hc.symm,hw.symm⟩,signature,hr,hl⟩
theorem different_warps_no_native_sync {block candidate left right}
    (hn : left.thread.tid.linear block/32 ≠ right.thread.tid.linear block/32) : ¬NativeSync block candidate left right := fun hs => hn hs.1.2
theorem different_signatures_no_native_sync {block candidate left right a b}
    (hl : candidate.nativeSignatureAt left = some a) (hr : candidate.nativeSignatureAt right = some b) (hne : a ≠ b) :
    ¬NativeSync block candidate left right := by
  rintro ⟨_,signature,ha,hb⟩
  exact hne ((Option.some.inj (hl.symm.trans ha)).trans (Option.some.inj (hb.symm.trans hr)))
theorem base_control_edge {block candidate histories left right}
    (he : Tma.ControlEdge candidate.view histories left right) : ControlEdge block candidate histories (.base left) (.base right) := .inl he
theorem base_control_path {block candidate histories left right}
    (he : Ptx.Event.Path (Tma.ControlEdge candidate.view histories) left right) :
    Ptx.Event.Path (ControlEdge block candidate histories) (.base left) (.base right) := by
  induction he with
  | single h => exact .single (base_control_edge h)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
theorem native_arrival_edge {block candidate histories before event}
    (hp : Hopper.ProgramOrder candidate.view before event) (hn : (candidate.nativeSignatureAt event).isSome = true) :
    ControlEdge block candidate histories (.base (.source before)) (.arrival event) := .inr (.inl ⟨hp,hn⟩)
theorem native_rendezvous_edge {block candidate histories left right} (hs : NativeSync block candidate left right) :
    ControlEdge block candidate histories (.arrival left) (.base (.source right)) := .inr (.inr (.inl hs))
theorem native_issue_edge {block candidate histories issue operand}
    (he : (candidate.representativeAt issue).isSome = true) :
    ControlEdge block candidate histories (.base (.source issue)) (.operand issue operand) := .inr (.inr (.inr (.inl ⟨rfl,he⟩)))
theorem native_finish_edge {block candidate histories issue wait operand} (he : WgmmaCompletedAt candidate issue wait) :
    ControlEdge block candidate histories (.operand issue operand) (.base (.source wait)) := .inr (.inr (.inr (.inr he)))
theorem native_cross_control_path {block candidate histories before left right}
    (hp : Hopper.ProgramOrder candidate.view before left) (hs : NativeSync block candidate left right) :
    Ptx.Event.Path (ControlEdge block candidate histories) (.base (.source before)) (.base (.source right)) := by
  obtain ⟨signature,hl,_⟩ := hs.2
  exact .trans (.single (native_arrival_edge hp (by rw [hl]; rfl))) (.single (native_rendezvous_edge hs))
theorem native_finish_requires_wait {candidate issue byte wait}
    (he : NativeFinish candidate (.operand issue byte) (.base (.source wait))) :
    ∃ mark groups keep before after query, candidate.eventAt wait = some (.wait mark groups keep before after query) ∧
      before ≤ after ∧ after ≤ groups ∧ keep < 8 := completed_has_actual_wait he
theorem acyclic_rejects_native_cta_cycle {block candidate histories before left right}
    (hp : Hopper.ProgramOrder candidate.view before left) (hs : NativeSync block candidate left right)
    (hb : Ptx.Event.Path (Tma.ControlEdge candidate.view histories) (.source right) (.source before)) :
    ¬ControlAdmitted block candidate histories := by
  intro hc
  exact hc.2 (.base (.source before)) (.trans (native_cross_control_path hp hs) (base_control_path hb))
theorem control_acyclic_of_rank {block candidate histories} (rank : ControlNode → Nat)
    (he : ∀ left right, ControlEdge block candidate histories left right → rank left < rank right) :
    ControlAcyclic block candidate histories := by
  intro node ho
  have hh := ho.rank_lt rank he
  omega

end
end Ptx.Hopper.Unified
