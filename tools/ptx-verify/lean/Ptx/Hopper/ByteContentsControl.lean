import Ptx.Hopper.ByteContentsPhases

/-! Checked control-only completion. Empty authority footprints exclude all
source byte/resource uses; the extra guard excludes every actual memory effect
mapped to this control node. Source presence, predecessors, freshness and the
absence of held fragments for this node remain checked by the original finish.
-/
namespace Ptx.Hopper.ByteContents
open Ptx.ISA Ptx.Hopper.Progress
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

def NoMemoryAt (candidate : Unified.Candidate) (control : Unified.ControlNode) : Prop :=
  ∀ memory, Unified.memoryControlNode memory = control →
    ∀ loc, readByte candidate memory loc = none ∧ writeByte candidate memory loc = none

def controlFinished (state : State) (node : Unified.ControlNode) : State :=
  {state with coupled := ⟨state.coupled.protocol,fun n => state.coupled.done n ∨ n = node⟩}

noncomputable def finishControl (block : Dim3) (candidate : Unified.Candidate) (histories : Location → List Tma.Entry)
    (node : Unified.ControlNode) (state : State) : Except Error State := by
  classical
  exact match ByteAuthority.Footprint.finish block candidate histories node [] (erase state) with
    | .error error => .error (.authority error)
    | .ok _ => if NoMemoryAt candidate node then .ok (controlFinished state node) else .error .memoryControl

theorem finishControl_spec {block candidate histories node state next}
    (hs : finishControl block candidate histories node state = .ok next) :
    NoMemoryAt candidate node ∧ next = controlFinished state node ∧
      ByteAuthority.Ready block candidate histories state.coupled.done node ∧
      ByteAuthority.Footprint.Covers candidate node [] ∧ ByteAuthority.Footprint.Frame (erase state) node [] := by
  unfold finishControl at hs
  cases ha : ByteAuthority.Footprint.finish block candidate histories node [] (erase state) with
  | error error => simp [ha] at hs
  | ok authority =>
    simp only [ha] at hs
    split at hs
    · rename_i hn
      have hf := ByteAuthority.Footprint.finish_spec ha
      exact ⟨hn,(Except.ok.inj hs).symm,hf.1,hf.2.2.1,hf.2.2.2.2.2.1⟩
    · cases hs

theorem finishControl_succeeds {block candidate histories node state}
    (hr : ByteAuthority.Ready block candidate histories state.coupled.done node)
    (hu : ∀ loc mode, ¬ByteAuthority.Uses candidate node loc mode)
    (hn : NoMemoryAt candidate node) (hf : ByteAuthority.Footprint.Frame (erase state) node []) :
    finishControl block candidate histories node state = .ok (controlFinished state node) := by
  have ha := ByteAuthority.Footprint.finish_succeeds hr
    (show ByteAuthority.Footprint.Sound candidate node [] from by intro _ h; cases h)
    (show ByteAuthority.Footprint.Covers candidate node [] from fun loc mode h => (hu loc mode h).elim)
    (show ByteAuthority.Footprint.Distinct [] from List.nodup_nil)
    (show ByteAuthority.Footprint.Held (erase state) node [] from by intro _ h; cases h) hf
  simp only [finishControl,ha,hn,ite_true]

theorem erase_controlFinished {state node}
    (hf : ByteAuthority.Footprint.Frame (erase state) node []) :
    erase (controlFinished state node) = ByteAuthority.retired (erase state) node := by
  apply congrArg₂ ByteAuthority.State.mk
  · rfl
  · exact ByteAuthority.Footprint.clear_eq_release (demands := []) (by intro _ h; cases h) hf

theorem finishControl_projects {block candidate histories cluster plan node state next}
    (hs : finishControl block candidate histories node state = .ok next) :
    ByteAuthority.Step block candidate histories cluster plan (erase state) (erase next) := by
  obtain ⟨_,rfl,hr,hc,hf⟩ := finishControl_spec hs
  rw [erase_controlFinished hf]
  exact .retire hr (ByteAuthority.Footprint.all_held hc (by intro _ h; cases h))

theorem finishControl_preserves_cells {block candidate histories node state next}
    (hs : finishControl block candidate histories node state = .ok next) : next.cells = state.cells := by
  rw [(finishControl_spec hs).2.1]
  rfl

theorem finishControl_preserves_value {block candidate histories node state next}
    (hs : finishControl block candidate histories node state = .ok next) (loc : Location) : valueAt next loc = valueAt state loc := by
  unfold valueAt
  rw [finishControl_preserves_cells hs]

theorem finishControl_rejects_actual_read {block candidate histories node state memory loc value}
    (hm : Unified.memoryControlNode memory = node) (hr : readByte candidate memory loc = some value) :
    ∀ next, finishControl block candidate histories node state ≠ .ok next := by
  intro next hs
  have hn := (finishControl_spec hs).1 memory hm loc
  rw [hr] at hn
  cases hn.1

theorem finishControl_rejects_actual_write {block candidate histories node state memory loc value}
    (hm : Unified.memoryControlNode memory = node) (hw : writeByte candidate memory loc = some value) :
    ∀ next, finishControl block candidate histories node state ≠ .ok next := by
  intro next hs
  have hn := (finishControl_spec hs).1 memory hm loc
  rw [hw] at hn
  cases hn.2

theorem finishControl_rejects_source_use {block candidate histories node state loc mode}
    (hu : ByteAuthority.Uses candidate node loc mode) : ∀ next, finishControl block candidate histories node state ≠ .ok next := by
  intro next hs
  obtain ⟨demand,hd,_⟩ := (finishControl_spec hs).2.2.2.1 loc mode hu
  cases hd

theorem arrival_no_memory (candidate : Unified.Candidate) (id : Ptx.Event.EventId) : NoMemoryAt candidate (.arrival id) := by
  intro memory he
  cases memory with
  | base node => cases node <;> cases he
  | wgmmaRead issue operand => cases he

theorem arrival_no_uses (candidate : Unified.Candidate) (id : Ptx.Event.EventId) :
    ∀ loc mode, ¬ByteAuthority.Uses candidate (.arrival id) loc mode := by
  rintro loc mode ⟨work,hu⟩
  cases hu with
  | async hu => cases hu
  | kernel hu => cases hu

theorem available_control_frame {state : State}
    (ha : ∀ k payload, get? state.cells k = some payload → payload.owner = .available)
    (node : Unified.ControlNode) : ByteAuthority.Footprint.Frame (erase state) node [] := by
  intro k mode hg
  change get? (Iris.Std.PartialMap.map Payload.owner state.cells) k = some (.held node mode) at hg
  rw [get?_map] at hg
  cases he : get? state.cells k with
  | none => simp [he] at hg
  | some payload =>
    have ho := ha k payload he
    have hx : payload.owner = .held node mode := by simpa only [he,Option.map_some,Option.some.injEq] using hg
    rw [hx] at ho
    cases ho

theorem finish_arrival_succeeds {block candidate histories id state}
    (hr : ByteAuthority.Ready block candidate histories state.coupled.done (.arrival id))
    (hf : ByteAuthority.Footprint.Frame (erase state) (.arrival id) []) :
    finishControl block candidate histories (.arrival id) state = .ok (controlFinished state (.arrival id)) :=
  finishControl_succeeds hr (arrival_no_uses candidate id) (arrival_no_memory candidate id) hf

theorem finishControl_rejects_missing_predecessor {block candidate histories node state before}
    (he : Unified.ControlEdge block candidate histories before node) (hn : ¬state.coupled.done before) :
    ∀ next, finishControl block candidate histories node state ≠ .ok next := by
  intro next hs
  exact hn ((finishControl_spec hs).2.2.1.2.2 before he)

theorem finishControl_rejects_completed {block candidate histories node state}
    (hd : state.coupled.done node) : ∀ next, finishControl block candidate histories node state ≠ .ok next := by
  intro next hs
  exact (finishControl_spec hs).2.2.1.2.1 hd

theorem finishControl_unready {block candidate histories node state}
    (hr : ¬ByteAuthority.Ready block candidate histories state.coupled.done node) :
    finishControl block candidate histories node state = .error (.authority .unready) := by
  simp only [finishControl,ByteAuthority.Footprint.finish,erase,hr,ite_false]

theorem finishControl_rejects_held {block candidate histories node state k mode}
    (hh : get? (erase state).bytes k = some (.held node mode)) :
    ∀ next, finishControl block candidate histories node state ≠ .ok next := by
  intro next hs
  have hm := (finishControl_spec hs).2.2.2.2 k mode hh
  cases hm

end
end Ptx.Hopper.ByteContents
