import Ptx.Hopper.Mbarrier

/-! Failed-wait stuttering in the existing resource protocol. False waits
are allowed after completion, but require a live object. Erasure preserves
successful runs; its unconditional converse would admit pre-init false waits.
-/
namespace Ptx.Hopper.Mbarrier.Retries
open Ptx.ISA

def keep : BarrierOp → Bool
  | .tryWaitParity _ false => false
  | _ => true
def erase (ops : List BarrierOp) : List BarrierOp := ops.filter keep

theorem dropped_step_live {start op next} (hk : keep op = false) (hs : step start op = some next) :
    next = start ∧ start.isSome = true := by
  cases op with
  | tryWaitParity parity answer =>
    cases answer with
    | false =>
      cases start with
      | none => cases hs
      | some state =>
        have he : some state = next := by simpa only [step,Bool.false_eq_true,ite_false,Option.some.injEq] using hs
        cases he
        exact ⟨rfl,rfl⟩
    | true => cases hk
  | init _ | inval | arriveExpectTx _ | completeTx _ => cases hk

theorem run_erase_of_success {start ops last} (hr : run start ops = some last) : run start (erase ops) = some last := by
  induction ops generalizing start with
  | nil => exact hr
  | cons op rest ih =>
    simp only [run] at hr
    cases hs : step start op with
    | none => simp only [hs,Option.bind_none] at hr; cases hr
    | some mid =>
      simp only [hs,Option.bind_some] at hr
      cases hk : keep op with
      | false =>
        have he := (dropped_step_live hk hs).1
        subst mid
        simpa [erase,hk] using ih hr
      | true =>
        simpa [erase,hk,run,hs] using ih hr

theorem admitted_erase {ops} (ha : Admitted ops) : Admitted (erase ops) := by
  obtain ⟨last,hr⟩ := ha
  exact ⟨last,run_erase_of_success hr⟩

theorem run_failed_waits (state : PhaseState) (parities : List Nat) :
    run (some state) (parities.map (fun p => .tryWaitParity p false)) = some (some state) := by
  induction parities with
  | nil => rfl
  | cons parity rest ih => simp only [List.map_cons,run,failed_wait_unchanged,Option.bind_some,ih]

theorem insert_failed_waits_at_live {start before state after last} (parities : List Nat)
    (hb : run start before = some (some state)) (ha : run (some state) after = some last) :
    run start (before++parities.map (fun p => .tryWaitParity p false)++after) = some last := by
  simp only [run_append,hb,Option.bind_some,run_failed_waits,ha]

theorem run_prefix_of_success {start ops last} (hr : run start ops = some last) (index : Nat) :
    ∃ mid, run start (ops.take index) = some mid := by
  have hs : run start (ops.take index++ops.drop index) = some last := by simpa only [List.take_append_drop] using hr
  rw [run_append] at hs
  cases hp : run start (ops.take index) with
  | none => simp only [hp,Option.bind_none] at hs; cases hs
  | some mid => exact ⟨mid,rfl⟩

end Ptx.Hopper.Mbarrier.Retries
