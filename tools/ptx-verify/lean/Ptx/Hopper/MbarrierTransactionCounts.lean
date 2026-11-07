import Ptx.Hopper.MbarrierPrefixAccounting

/-! Weighted transaction and prefix counts. A pair of completion byte sizes is
an explicit inventory property; these equations neither match copies nor
require their notifications to occur in a prescribed order. -/
namespace Ptx.Hopper.Mbarrier
open Ptx.ISA

def completionCount (bytes : Nat) (ops : List BarrierOp) : Nat :=
  (ops.filter (fun op => match op with | .completeTx n => n == bytes | _ => false)).length
def CompletionKinds (a b : Nat) : BarrierOp → Prop
  | .completeTx n => n = a ∨ n = b
  | _ => True

theorem completed_bytes_two_kinds {ops : List BarrierOp} (a b : Nat) (hne : a ≠ b)
    (hk : ∀ op ∈ ops, CompletionKinds a b op) :
    completedBytes ops = a*completionCount a ops+b*completionCount b ops := by
  induction ops with
  | nil => simp [completedBytes,completionCount]
  | cons op rest ih =>
    have hhead := hk op (by simp)
    have htail := ih (fun x hx => hk x (by simp [hx]))
    cases op with
    | completeTx n =>
      rcases hhead with rfl | rfl <;>
        simp [completedBytes,completedUnit,completionCount,hne,Ne.symm hne,Nat.mul_add] at htail ⊢ <;> omega
    | init n => simpa [completedBytes,completedUnit,completionCount] using htail
    | inval => simpa [completedBytes,completedUnit,completionCount] using htail
    | arriveExpectTx n => simpa [completedBytes,completedUnit,completionCount] using htail
    | tryWaitParity p done => simpa [completedBytes,completedUnit,completionCount] using htail

theorem arrival_count_append (first rest : List BarrierOp) :
    arrivalCount (first++rest) = arrivalCount first+arrivalCount rest := by
  simp [arrivalCount]

theorem added_bytes_append (first rest : List BarrierOp) :
    addedBytes (first++rest) = addedBytes first+addedBytes rest := by
  simp [addedBytes]

theorem completed_bytes_append (first rest : List BarrierOp) :
    completedBytes (first++rest) = completedBytes first+completedBytes rest := by
  simp [completedBytes]

theorem completion_count_append (bytes : Nat) (first rest : List BarrierOp) :
    completionCount bytes (first++rest) = completionCount bytes first+completionCount bytes rest := by
  simp [completionCount]

theorem arrival_count_take_le (ops : List BarrierOp) (cut : Nat) : arrivalCount (ops.take cut) ≤ arrivalCount ops := by
  have he := arrival_count_append (ops.take cut) (ops.drop cut)
  rw [List.take_append_drop] at he
  omega

theorem arrival_count_take_mono (ops : List BarrierOp) {first last : Nat} (hl : first ≤ last) :
    arrivalCount (ops.take first) ≤ arrivalCount (ops.take last) := by
  have h := arrival_count_take_le (ops.take last) first
  simpa only [List.take_take,Nat.min_eq_left hl] using h

theorem completion_count_take_le (bytes : Nat) (ops : List BarrierOp) (cut : Nat) :
    completionCount bytes (ops.take cut) ≤ completionCount bytes ops := by
  have he := completion_count_append bytes (ops.take cut) (ops.drop cut)
  rw [List.take_append_drop] at he
  omega

end Ptx.Hopper.Mbarrier
