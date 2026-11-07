import Ptx.Hopper.ByteContents
import Ptx.Hopper.ByteProtocol

/-! Lift the existing checked prepared-plan commands into the value state.
Device completion retains its actual-source guard and all original errors.
Commands affect protocol metadata, not the symbolic GPU byte cells. In
particular scalar protocol buffers are not identified with physical bytes;
physical host writes/reclamation require a further runtime interpretation.
-/
namespace Ptx.Hopper.ByteContents
open Ptx.ISA Ptx.Hopper.Progress
noncomputable section

def withCoupled (state : State) (coupled : Bridge.State) : State :=
  {state with coupled := coupled}

noncomputable def executeCommand (candidate : Unified.Candidate) (histories : Location → List Tma.Entry)
    (cluster : Access.ClusterScope) (plan : Bridge.Plan) (command : Bridge.Command) (state : State) : Except Error State :=
  match ByteAuthority.executeCommand candidate histories cluster plan command (erase state) with
  | .error error => .error (.authority error)
  | .ok authority => .ok (withCoupled state authority.coupled)

theorem executeCommand_error {candidate histories cluster plan command state error}
    (hs : ByteAuthority.executeCommand candidate histories cluster plan command (erase state) = .error error) :
    executeCommand candidate histories cluster plan command state = .error (.authority error) := by
  simp only [executeCommand,hs]

theorem executeCommand_success {candidate histories cluster plan command state authority}
    (hs : ByteAuthority.executeCommand candidate histories cluster plan command (erase state) = .ok authority) :
    executeCommand candidate histories cluster plan command state = .ok (withCoupled state authority.coupled) := by
  simp only [executeCommand,hs]

theorem executeCommand_spec {block candidate histories cluster plan command state next}
    (hs : executeCommand candidate histories cluster plan command state = .ok next) :
    ByteAuthority.executeCommand candidate histories cluster plan command (erase state) = .ok (erase next) ∧
      Bridge.Step block Tma.localShared candidate histories cluster plan state.coupled next.coupled ∧
      next.coupled.done = state.coupled.done ∧ next.cells = state.cells := by
  unfold executeCommand at hs
  cases ha : ByteAuthority.executeCommand candidate histories cluster plan command (erase state) with
  | error error => simp [ha] at hs
  | ok authority =>
    have hn : next = withCoupled state authority.coupled := (Except.ok.inj (by simpa only [ha] using hs)).symm
    subst next
    have hh := ByteAuthority.executeCommand_spec (block := block) ha
    have he : erase (withCoupled state authority.coupled) = authority := by
      apply congrArg₂ ByteAuthority.State.mk
      · rfl
      · exact hh.2.2.symm
    exact ⟨by rw [he],hh.1,hh.2.1,rfl⟩

theorem executeCommand_projects {block candidate histories cluster plan command state next}
    (hs : executeCommand candidate histories cluster plan command state = .ok next) :
    ByteAuthority.Step block candidate histories cluster plan (erase state) (erase next) :=
  ByteAuthority.executeCommand_is_step (executeCommand_spec (block := block) hs).1

theorem executeCommand_value {candidate histories cluster plan command state next}
    (hs : executeCommand candidate histories cluster plan command state = .ok next) (loc : Location) :
    valueAt next loc = valueAt state loc := by
  unfold valueAt
  rw [(executeCommand_spec (block := .one) hs).2.2.2]

def runCommands (candidate : Unified.Candidate) (histories : Location → List Tma.Entry)
    (cluster : Access.ClusterScope) (plan : Bridge.Plan) : List Bridge.Command → State → Except Error State
  | [],state => .ok state
  | command::rest,state => (executeCommand candidate histories cluster plan command state).bind
      (fun next => runCommands candidate histories cluster plan rest next)

theorem runCommands_succeeds {candidate histories cluster plan done protocol final}
    (hc : Bridge.AllCompleted Tma.localShared candidate histories cluster plan done) (commands : List Bridge.Command)
    (hr : Ptx.Async.run protocol (commands.map Bridge.Command.action) = .ok final) (cells : HeapF Payload) :
    runCommands candidate histories cluster plan commands ⟨⟨protocol,done⟩,cells⟩ = .ok ⟨⟨final,done⟩,cells⟩ := by
  induction commands generalizing protocol with
  | nil =>
    simp only [List.map_nil,Ptx.Async.run,Except.ok.injEq] at hr
    subst final
    rfl
  | cons command rest ih =>
    simp only [List.map_cons,Ptx.Async.run] at hr
    cases hs : Ptx.Async.step protocol command.action with
    | error error => simp [hs,Except.bind] at hr
    | ok next =>
      have ht : Ptx.Async.run next (rest.map Bridge.Command.action) = .ok final := by simpa only [hs,Except.bind] using hr
      have hh : ByteAuthority.executeCommand candidate histories cluster plan command (erase (⟨⟨protocol,done⟩,cells⟩ : State)) =
          .ok (erase (⟨⟨next,done⟩,cells⟩ : State)) := by
        cases command with
        | host action => exact ByteAuthority.execute_host_success hs
        | device sid =>
          obtain ⟨st,hg,_⟩ := Ptx.Async.deviceStep_streams hs
          exact ByteAuthority.execute_device_success hg hs (fun work hm => hc _ work hm)
      simp only [runCommands,executeCommand_success hh,Except.bind]
      exact ih ht

end
end Ptx.Hopper.ByteContents
