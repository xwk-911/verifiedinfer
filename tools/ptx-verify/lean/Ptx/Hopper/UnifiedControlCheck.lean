import Ptx.Hopper.UnifiedControlParticipants

/-! Decidable native rendezvous checks compare only physical coordinates and
source signatures. No equality procedure for events, states or reals is used.
-/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

def checkNativeSync (block : Dim3) (candidate : Candidate) (left right : Ptx.Event.EventId) : Bool :=
  decide (SamePhysicalWarp block left.thread right.thread) &&
    match candidate.nativeSignatureAt left,candidate.nativeSignatureAt right with
    | some a,some b => a == b
    | _,_ => false
theorem native_sync_check_iff (block candidate left right) :
    checkNativeSync block candidate left right = true ↔ NativeSync block candidate left right := by
  cases hl : candidate.nativeSignatureAt left <;> cases hr : candidate.nativeSignatureAt right <;>
    simp [checkNativeSync,NativeSync,hl,hr,beq_iff_eq]
  intro _
  exact eq_comm
instance (block candidate left right) : Decidable (NativeSync block candidate left right) :=
  decidable_of_iff (checkNativeSync block candidate left right = true) (native_sync_check_iff block candidate left right)
theorem native_self_return_cannot_arrive {candidate : Candidate} {id} :
    ¬NativeArrival candidate (.base (.source id)) (.arrival id) := by
  intro he
  exact Nat.lt_irrefl _ he.1.2.2.2
theorem native_control_keeps_base_acyclic {block candidate histories}
    (hc : ControlAdmitted block candidate histories) : Tma.ControlAcyclic candidate.view histories :=
  fun node ho => hc.2 (.base node) (base_control_path ho)

end
end Ptx.Hopper.Unified
