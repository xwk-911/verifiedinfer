import Ptx.Ordered.Client
import Ptx.Ordered.Observation
import Ptx.Iris.Execution

/-! Native Iris OwnP rules for the SAME one-instruction ordered/protocol client.
Every source action invokes Ordered.step and keeps its qualifiers/event bytes;
every protocol action invokes Async.step with the explicit completion guard.
Ownership here is exclusive whole-client state, not fractional byte ownership.
Memory admission is explicit, not erased to the old weak scalar predicates.
-/
namespace Ptx.IrisOrderedClient
open Ptx.ISA Ptx.Ordered.Client
open Iris Iris.BI Iris.ProgramLogic
noncomputable section

abbrev Expr (code : List Ordered.Instr) (launch : Scalar.Launch) := IrisExecution.Expr (Ordered.Client.step code launch)
abbrev invoke (code : List Ordered.Instr) (launch : Scalar.Launch) (action : Ordered.Client.Action) : Expr code launch := IrisExecution.Expr.invoke action
abbrev script (code : List Ordered.Instr) (launch : Scalar.Launch) (actions : List Ordered.Client.Action) : Expr code launch := IrisExecution.Expr.script actions
noncomputable abbrev GF := IrisExecution.GF Ordered.Client.State
local bi (IProp GF)

theorem invoke_wp [OwnPGS Ordered.Client.State GF] {code launch state action result}
    (hs : Ordered.Client.step code launch action state = result) :
    ownP (GF := GF) state ⊢ WP (invoke code launch action)
      {{ value, ⌜value = result⌝ ∗ ownP (IrisExecution.after state value) }} := IrisExecution.invoke_wp hs

theorem source_wp [OwnPGS Ordered.Client.State GF] {code launch state index next}
    (hw : Ordered.WellFormed code launch state.source) (hi : Async.Invariant state.protocol)
    (hs : Ordered.Client.step code launch (.source index) state = .ok next) :
    ownP (GF := GF) state ⊢ WP (invoke code launch (.source index))
      {{ value, ⌜value = .ok next ∧ Ordered.WellFormed code launch next.source ∧
          Async.Invariant next.protocol ∧ next.protocol = state.protocol⌝ ∗ ownP next }} := by
  refine (invoke_wp hs).trans (wp_mono ?_)
  intro value
  iintro ⟨%hv,Hnext⟩
  subst value
  simp only [IrisExecution.after]
  isplit
  · ipureintro
    exact ⟨by trivial,step_well_formed hw hs,step_protocol_invariant hi hs,source_step_preserves_protocol hs⟩
  · iexact Hnext

theorem source_borrow_guard_wp [OwnPGS Ordered.Client.State GF] {code launch state index next bid buffer}
    (hs : Ordered.Client.step code launch (.source index) state = .ok next)
    (hb : Async.getBuffer state.protocol bid = .ok buffer) (hl : buffer.loans.isEmpty = false) :
    ownP (GF := GF) state ⊢ WP (invoke code launch (.source index))
      {{ value, ⌜value = .ok next ∧ Ordered.Client.step code launch (.protocol (.reclaim bid)) next =
          .error (.protocolFailure .outstandingLoan)⌝ ∗ ownP next }} := by
  refine (invoke_wp hs).trans (wp_mono ?_)
  intro value
  iintro ⟨%hv,Hnext⟩
  subst value
  simp only [IrisExecution.after]
  isplit
  · ipureintro; exact ⟨by trivial,source_step_cannot_discharge_loan hs hb hl⟩
  · iexact Hnext

theorem invoke_frame [OwnPGS Ordered.Client.State GF] {code launch state action result}
    (hs : Ordered.Client.step code launch action state = result) (frame : IProp GF) :
    ownP (GF := GF) state ∗ frame ⊢ WP (invoke code launch action)
      {{ value, frame ∗ ⌜value = result⌝ ∗ ownP (IrisExecution.after state value) }} :=
  IrisExecution.invoke_frame hs frame

theorem run_eq (code : List Ordered.Instr) (launch : Scalar.Launch) (actions : List Ordered.Client.Action) (state : Ordered.Client.State) :
    IrisExecution.run (Ordered.Client.step code launch) actions state = Ordered.Client.run code launch actions state := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
    cases hs : Ordered.Client.step code launch action state <;> simp only [IrisExecution.run,Ordered.Client.run,hs,Except.bind,ih]

theorem script_wp [OwnPGS Ordered.Client.State GF] {code launch actions state next}
    (hr : Ordered.Client.run code launch actions state = .ok next) :
    ownP (GF := GF) state ⊢ WP (script code launch actions) {{ value, ⌜value = .ok next⌝ ∗ ownP next }} :=
  IrisExecution.script_wp ((run_eq code launch actions state).trans hr)

theorem contract_wp [OwnPGS Ordered.Client.State GF] {code launch pre domain post actions state next observation sources co}
    (hc : Ordered.Triple code pre domain post) (hp : pre launch)
    (hw : Ordered.WellFormed code launch state.source) (hi : Async.Invariant state.protocol)
    (hr : Ordered.Client.run code launch actions state = .ok next) (hd : Ordered.Complete next.source)
    (hm : Ordered.MemoryConditions next.source launch.initial sources co)
    (ho : Ordered.ObserverConditions next.source launch.initial sources co observation)
    (hdom : observation.domain = domain launch) :
    ownP (GF := GF) state ⊢ WP (script code launch actions)
      {{ value, ⌜value = .ok next ∧ post launch observation.output ∧
          Ordered.WellFormed code launch next.source ∧ Async.Invariant next.protocol⌝ ∗ ownP next }} := by
  have hinv := run_invariants hw hi hr
  have hpost := hc launch next.source sources co observation hp hinv.1 hd hm ho hdom
  refine (script_wp hr).trans (wp_mono ?_)
  intro value
  iintro ⟨%hv,Hnext⟩
  isplit
  · ipureintro; exact ⟨hv,hpost,hinv⟩
  · iexact Hnext

theorem contract_adequate {code launch pre domain post actions state next observation sources co}
    (hc : Ordered.Triple code pre domain post) (hp : pre launch)
    (hw : Ordered.WellFormed code launch state.source) (hi : Async.Invariant state.protocol)
    (hr : Ordered.Client.run code launch actions state = .ok next) (hd : Ordered.Complete next.source)
    (hm : Ordered.MemoryConditions next.source launch.initial sources co)
    (ho : Ordered.ObserverConditions next.source launch.initial sources co observation)
    (hdom : observation.domain = domain launch) :
    adequate .NotStuck (script code launch actions) state
      (fun value _ => value = .ok next ∧ post launch observation.output ∧
        Ordered.WellFormed code launch next.source ∧ Async.Invariant next.protocol) := by
  apply ownP_adequacy (GF := GF) .NotStuck (script code launch actions) state
    (fun value => value = .ok next ∧ post launch observation.output ∧
      Ordered.WellFormed code launch next.source ∧ Async.Invariant next.protocol)
  intro _
  refine (contract_wp hc hp hw hi hr hd hm ho hdom).trans (wp_mono ?_)
  intro value
  iintro ⟨Hv,_⟩
  iexact Hv

theorem reject_not_ok_adequate {code launch state action fault}
    (hs : Ordered.Client.step code launch action state = .error fault) :
    ¬adequate .NotStuck (invoke code launch action) state (fun value _ => ∃ next, value = .ok next) :=
  IrisExecution.reject_not_ok_adequate hs

theorem script_reject_not_ok_adequate {code launch actions state fault}
    (hr : Ordered.Client.run code launch actions state = .error fault) :
    ¬adequate .NotStuck (script code launch actions) state (fun value _ => ∃ next, value = .ok next) :=
  IrisExecution.script_reject_not_ok_adequate ((run_eq code launch actions state).trans hr)

end
end Ptx.IrisOrderedClient
