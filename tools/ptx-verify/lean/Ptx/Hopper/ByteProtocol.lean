import Ptx.Hopper.ByteAuthorityInvariant
import Ptx.Hopper.ProtocolScript

/-! Execute actual prepared-plan host/device commands while preserving byte
authority. Device completion is checked against its next source-matched work,
in addition to the existing FIFO/dependency checks. Errors retain their reason.
These are protocol/authority metadata, not physical GPU memory effects.
-/
namespace Ptx.Hopper.ByteAuthority
open Ptx.ISA Ptx.Hopper.Progress
noncomputable section

def NextCompleted (candidate : Unified.Candidate) (histories : Location → List Tma.Entry)
    (cluster : Access.ClusterScope) (plan : Bridge.Plan) (done : Cut) (sid : Nat) (st : Ptx.Async.Stream) : Prop :=
  ∀ work, plan ⟨sid,st.completed+1⟩ = some work → Completed Tma.localShared candidate histories cluster done work

noncomputable def executeCommand (candidate : Unified.Candidate) (histories : Location → List Tma.Entry)
    (cluster : Access.ClusterScope) (plan : Bridge.Plan) (command : Bridge.Command) (state : State) : Except Error State := by
  classical
  exact match command with
  | .host action => match Ptx.Async.step state.coupled.protocol action.action with
    | .error error => .error (.protocolFailure error)
    | .ok protocol => .ok {state with coupled := {state.coupled with protocol := protocol}}
  | .device sid => match Ptx.Async.getStream state.coupled.protocol sid with
    | .error error => .error (.protocolFailure error)
    | .ok st => match Ptx.Async.deviceStep state.coupled.protocol sid with
      | .error error => .error (.protocolFailure error)
      | .ok protocol => if NextCompleted candidate histories cluster plan state.coupled.done sid st then
          .ok {state with coupled := {state.coupled with protocol := protocol}}
        else .error .incompleteWork

theorem execute_host_success {candidate histories cluster plan state action protocol}
    (hr : Ptx.Async.step state.coupled.protocol (Bridge.HostAction.action action) = .ok protocol) :
    executeCommand candidate histories cluster plan (.host action) state =
      .ok {state with coupled := {state.coupled with protocol := protocol}} := by simp [executeCommand,hr]

theorem execute_host_error {candidate histories cluster plan state action error}
    (hr : Ptx.Async.step state.coupled.protocol (Bridge.HostAction.action action) = .error error) :
    executeCommand candidate histories cluster plan (.host action) state = .error (.protocolFailure error) := by simp [executeCommand,hr]

theorem execute_device_success {candidate histories cluster plan state sid st protocol}
    (hg : Ptx.Async.getStream state.coupled.protocol sid = .ok st)
    (hr : Ptx.Async.deviceStep state.coupled.protocol sid = .ok protocol)
    (hc : NextCompleted candidate histories cluster plan state.coupled.done sid st) :
    executeCommand candidate histories cluster plan (.device sid) state =
      .ok {state with coupled := {state.coupled with protocol := protocol}} := by simp [executeCommand,hg,hr,hc]

theorem execute_device_uncompleted {candidate histories cluster plan state sid st protocol}
    (hg : Ptx.Async.getStream state.coupled.protocol sid = .ok st)
    (hr : Ptx.Async.deviceStep state.coupled.protocol sid = .ok protocol)
    (hc : ¬NextCompleted candidate histories cluster plan state.coupled.done sid st) :
    executeCommand candidate histories cluster plan (.device sid) state = .error .incompleteWork := by simp [executeCommand,hg,hr,hc]

theorem execute_device_error {candidate histories cluster plan state sid st error}
    (hg : Ptx.Async.getStream state.coupled.protocol sid = .ok st)
    (hr : Ptx.Async.deviceStep state.coupled.protocol sid = .error error) :
    executeCommand candidate histories cluster plan (.device sid) state = .error (.protocolFailure error) := by simp [executeCommand,hg,hr]

theorem executeCommand_spec {block candidate histories cluster plan command state next}
    (hs : executeCommand candidate histories cluster plan command state = .ok next) :
    Bridge.Step block Tma.localShared candidate histories cluster plan state.coupled next.coupled ∧
      next.coupled.done = state.coupled.done ∧ next.bytes = state.bytes := by
  cases command with
  | host action =>
    unfold executeCommand at hs
    cases hr : Ptx.Async.step state.coupled.protocol action.action with
    | error error => simp [hr] at hs
    | ok protocol =>
      simp only [hr,Except.ok.injEq] at hs
      subst next
      exact ⟨.host action hr,rfl,rfl⟩
  | device sid =>
    unfold executeCommand at hs
    cases hg : Ptx.Async.getStream state.coupled.protocol sid with
    | error error => simp [hg] at hs
    | ok st =>
      cases hr : Ptx.Async.deviceStep state.coupled.protocol sid with
      | error error => simp [hg,hr] at hs
      | ok protocol =>
        simp only [hg,hr] at hs
        split at hs
        · rename_i hc
          cases Except.ok.inj hs
          exact ⟨.device hg hr hc,rfl,rfl⟩
        · cases hs

theorem executeCommand_is_step {block candidate histories cluster plan command state next}
    (hs : executeCommand candidate histories cluster plan command state = .ok next) :
    Step block candidate histories cluster plan state next := by
  obtain ⟨hp,hd,hb⟩ := executeCommand_spec (block := block) hs
  have he : {state with coupled := next.coupled} = next := by
    apply congrArg₂ State.mk
    · rfl
    · exact hb.symm
  rw [← he]
  exact .protocol hp hd.symm

def runCommands (candidate : Unified.Candidate) (histories : Location → List Tma.Entry)
    (cluster : Access.ClusterScope) (plan : Bridge.Plan) : List Bridge.Command → State → Except Error State
  | [],state => .ok state
  | command::rest,state => (executeCommand candidate histories cluster plan command state).bind
      (fun next => runCommands candidate histories cluster plan rest next)

theorem runCommands_steps {block candidate histories cluster plan commands state next}
    (hs : runCommands candidate histories cluster plan commands state = .ok next) :
    Steps block candidate histories cluster plan state next := by
  induction commands generalizing state with
  | nil => cases hs; exact .refl _
  | cons head rest ih =>
    unfold runCommands at hs
    cases hh : executeCommand candidate histories cluster plan head state with
    | error error => simp [hh,Except.bind] at hs
    | ok mid => exact .next (executeCommand_is_step hh) (ih (by simpa only [hh,Except.bind] using hs))

theorem runCommands_succeeds {candidate histories cluster plan done protocol final}
    (hc : Bridge.AllCompleted Tma.localShared candidate histories cluster plan done) (commands : List Bridge.Command)
    (hrun : Ptx.Async.run protocol (commands.map Bridge.Command.action) = .ok final) (bytes : HeapF Owner) :
    runCommands candidate histories cluster plan commands ⟨⟨protocol,done⟩,bytes⟩ = .ok ⟨⟨final,done⟩,bytes⟩ := by
  induction commands generalizing protocol with
  | nil =>
    simp only [List.map_nil,Ptx.Async.run,Except.ok.injEq] at hrun
    subst final
    rfl
  | cons command rest ih =>
    simp only [List.map_cons,Ptx.Async.run] at hrun
    cases hs : Ptx.Async.step protocol command.action with
    | error error => simp [hs,Except.bind] at hrun
    | ok next =>
      have ht : Ptx.Async.run next (rest.map Bridge.Command.action) = .ok final := by simpa only [hs,Except.bind] using hrun
      have hh : executeCommand candidate histories cluster plan command ⟨⟨protocol,done⟩,bytes⟩ = .ok ⟨⟨next,done⟩,bytes⟩ := by
        cases command with
        | host action => exact execute_host_success hs
        | device sid =>
          obtain ⟨st,hg,_⟩ := Ptx.Async.deviceStep_streams hs
          exact execute_device_success hg hs (fun work hm => hc _ work hm)
      simp only [runCommands,hh,Except.bind]
      exact ih ht

theorem executeCommand_protocol_error {candidate histories cluster plan state command error}
    (hr : Ptx.Async.step state.coupled.protocol command.action = .error error) :
    executeCommand candidate histories cluster plan command state = .error (.protocolFailure error) := by
  cases command with
  | host action => exact execute_host_error hr
  | device sid =>
    change Ptx.Async.deviceStep state.coupled.protocol sid = .error error at hr
    cases hg : Ptx.Async.getStream state.coupled.protocol sid with
    | error other =>
      have he : other = error := by
        simpa only [Ptx.Async.deviceStep,hg,bind,Except.bind,Except.error.injEq] using hr
      subst other
      simp only [executeCommand,hg]
    | ok st => exact execute_device_error hg hr

theorem runCommands_error {candidate histories cluster plan done protocol error}
    (hc : Bridge.AllCompleted Tma.localShared candidate histories cluster plan done) (commands : List Bridge.Command)
    (hrun : Ptx.Async.run protocol (commands.map Bridge.Command.action) = .error error) (bytes : HeapF Owner) :
    runCommands candidate histories cluster plan commands ⟨⟨protocol,done⟩,bytes⟩ = .error (.protocolFailure error) := by
  induction commands generalizing protocol with
  | nil => cases hrun
  | cons command rest ih =>
    simp only [List.map_cons,Ptx.Async.run] at hrun
    cases hs : Ptx.Async.step protocol command.action with
    | error cause =>
      have he : cause = error := by simpa only [hs,Except.bind,Except.error.injEq] using hrun
      subst cause
      rw [runCommands,executeCommand_protocol_error hs]
      rfl
    | ok next =>
      have ht : Ptx.Async.run next (rest.map Bridge.Command.action) = .error error := by simpa only [hs,Except.bind] using hrun
      have hh : executeCommand candidate histories cluster plan command ⟨⟨protocol,done⟩,bytes⟩ = .ok ⟨⟨next,done⟩,bytes⟩ := by
        cases command with
        | host action => exact execute_host_success hs
        | device sid =>
          obtain ⟨st,hg,_⟩ := Ptx.Async.deviceStep_streams hs
          exact execute_device_success hg hs (fun work hm => hc _ work hm)
      simp only [runCommands,hh,Except.bind]
      exact ih ht

end
end Ptx.Hopper.ByteAuthority
