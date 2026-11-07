import Ptx.Hopper.PrefixExecution

/-! Lift prepared-plan protocol scripts once their mapped actual work has
completed. Each command still uses the real interpreter and one coupled step.
Dynamic issue/wait commands are deliberately outside this prepared-plan API.
-/
namespace Ptx.Hopper.Progress.Bridge
noncomputable section

inductive Command
  | host (action : HostAction)
  | device (stream : Nat)

def Command.action : Command → Ptx.Async.Action
  | .host action => action.action
  | .device sid => .device sid

def AllCompleted (resolve : Tma.SharedResolver) (candidate : Unified.Candidate) (histories : Ptx.ISA.Location → List Tma.Entry)
    (cluster : Access.ClusterScope) (plan : Plan) (done : Cut) : Prop :=
  ∀ ticket work, plan ticket = some work → Completed resolve candidate histories cluster done work

theorem completed_script_execution {block resolve candidate histories cluster plan done protocol final}
    (hc : AllCompleted resolve candidate histories cluster plan done) (commands : List Command)
    (hrun : Ptx.Async.run protocol (commands.map Command.action) = .ok final) :
    Steps block resolve candidate histories cluster plan ⟨protocol,done⟩ ⟨final,done⟩ := by
  induction commands generalizing protocol with
  | nil =>
    simp only [List.map_nil,Ptx.Async.run,Except.ok.injEq] at hrun
    subst final
    exact .refl _
  | cons command rest ih =>
    simp only [List.map_cons,Ptx.Async.run] at hrun
    cases hs : Ptx.Async.step protocol command.action with
    | error e => simp [hs,Except.bind] at hrun
    | ok next =>
      have htail : Ptx.Async.run next (rest.map Command.action) = .ok final := by simpa [hs,Except.bind] using hrun
      apply Steps.next (s := ⟨protocol,done⟩) (mid := ⟨next,done⟩) ?_ (ih htail)
      cases command with
      | host action => exact .host action hs
      | device sid =>
        obtain ⟨st,hst,_⟩ := Ptx.Async.deviceStep_streams hs
        exact .device hst hs (fun work hm => hc _ work hm)

end
end Ptx.Hopper.Progress.Bridge
