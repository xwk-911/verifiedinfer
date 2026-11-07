import Ptx.Iris.ByteContentsControl

/-! Actual claim runs and native local continuations for composing complete
memory-event cycles without consuming unrelated heap fragments.
-/
namespace Ptx.ByteContentsHeap
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

theorem acquisition_run (ctx : Context) (state : State) (node : Unified.ControlNode) (demands : List Demand)
    (values : Location → Option Symbolic.Byte)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories state.coupled.done node)
    (hs : ByteAuthority.Footprint.Sound ctx.candidate node demands) (hd : ByteAuthority.Footprint.Distinct demands)
    (hf : Free state demands values) :
    IrisExecution.run (transition ctx) (acquisitionActions node demands) state = .ok (granted state node demands values) := by
  induction demands generalizing state with
  | nil => rfl
  | cons head rest ih =>
    have hc := ByteContents.claim_succeeds (request := ⟨node,head.location,head.mode⟩) (state := state) hr (hs head (by simp)) (hf head (by simp))
    change (ByteContents.claim ctx.block ctx.candidate ctx.histories ⟨node,head.location,head.mode⟩ state).bind _ = _
    rw [hc]
    exact ih _ hr (by intro d hm; exact hs d (by simp [hm])) (ByteAuthority.Footprint.distinct_tail hd).2 (free_after_head hd hf)

theorem cycle_run (ctx : Context) (state next : State) (node : Unified.Node) (demands : List Demand)
    (values : Location → Option Symbolic.Byte)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories state.coupled.done (Unified.memoryControlNode node))
    (hs : ByteAuthority.Footprint.Sound ctx.candidate (Unified.memoryControlNode node) demands)
    (hd : ByteAuthority.Footprint.Distinct demands) (hf : Free state demands values)
    (hfinish : transition ctx (.finish node demands) (granted state (Unified.memoryControlNode node) demands values) = .ok next) :
    IrisExecution.run (transition ctx) (cycleActions node demands) state = .ok next := by
  rw [cycleActions,IrisExecution.run_append,acquisition_run ctx state _ demands values hr hs hd hf]
  change (transition ctx (.finish node demands) _).bind _ = _
  rw [hfinish]
  rfl

theorem cycle_local_cps [GS] (ctx : Context) (state next : State) (node : Unified.Node) (demands : List Demand)
    (values : Location → Option Symbolic.Byte) (tail : List Action) (frame : IProp GF) (post : Except ByteContents.Error State → IProp GF)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories state.coupled.done (Unified.memoryControlNode node))
    (hs : ByteAuthority.Footprint.Sound ctx.candidate (Unified.memoryControlNode node) demands)
    (hd : ByteAuthority.Footprint.Distinct demands) (hf : Free state demands values)
    (hfinish : transition ctx (.finish node demands) (granted state (Unified.memoryControlNode node) demands values) = .ok next)
    (hcont : control next ∗ freePoints demands (returnedValues ctx.candidate node values) ∗ frame ⊢
      WP (script ctx tail) {{ result, post result }}) :
    control state ∗ freePoints demands values ∗ frame ⊢ WP (script ctx (cycleActions node demands ++ tail)) {{ result, post result }} := by
  rw [cycleActions,List.append_assoc]
  apply acquisition_cps ctx state _ demands values (.finish node demands::tail) frame post hr hs hd hf
  exact finish_local_cps ctx _ next node demands values tail frame post hfinish (granted_matches state _ demands values hd) hcont

theorem finish_free {ctx : Context} {state next node demands values}
    (hs : transition ctx (.finish node demands) state = .ok next)
    (hm : Matches state (Unified.memoryControlNode node) demands values) :
    Free next demands (returnedValues ctx.candidate node values) := by
  intro demand hd
  rw [(ByteContents.finish_spec hs).2.2.1]
  exact ByteContents.finishCells_member (candidate := ctx.candidate) (node := node) (finish_distinct hs) hd (hm demand hd)

theorem matches_held {state node demands values} (hm : Matches state node demands values) :
    ByteAuthority.Footprint.Held (ByteContents.erase state) node demands := by
  intro demand hd
  change get? (Iris.Std.PartialMap.map ByteContents.Payload.owner state.cells) (ByteAuthority.key demand.location) = _
  rw [get?_map,hm demand hd]
  rfl

theorem granted_frame {state node demands values}
    (hf : ByteAuthority.Footprint.Frame (ByteContents.erase state) node []) :
    ByteAuthority.Footprint.Frame (ByteContents.erase (granted state node demands values)) node demands := by
  intro k mode hg
  by_contra hn
  change get? (Iris.Std.PartialMap.map ByteContents.Payload.owner (granted state node demands values).cells) k = _ at hg
  rw [get?_map,granted_outside _ _ _ _ _ hn] at hg
  have hx : get? (ByteContents.erase state).bytes k = some (.held node mode) := by
    change get? (Iris.Std.PartialMap.map ByteContents.Payload.owner state.cells) k = _
    rw [get?_map]; exact hg
  have hm := hf k mode hx
  cases hm

theorem granted_frame_other {state node other demands values}
    (hd : ByteAuthority.Footprint.Distinct demands) (hn : node ≠ other)
    (hf : ByteAuthority.Footprint.Frame (ByteContents.erase state) other []) :
    ByteAuthority.Footprint.Frame (ByteContents.erase (granted state node demands values)) other [] := by
  intro k mode hg
  change get? (Iris.Std.PartialMap.map ByteContents.Payload.owner (granted state node demands values).cells) k = _ at hg
  rw [get?_map] at hg
  by_cases hk : k ∈ ByteAuthority.Footprint.keys demands
  · obtain ⟨demand,hm,he⟩ := List.mem_map.mp hk
    rw [← he,granted_matches state node demands values hd demand hm] at hg
    have hx : node = other := ByteAuthority.Owner.held.inj (Option.some.inj hg) |>.1
    exact (hn hx).elim
  · rw [granted_outside _ _ _ _ _ hk] at hg
    apply hf k mode
    change get? (Iris.Std.PartialMap.map ByteContents.Payload.owner state.cells) k = _
    rw [get?_map]; exact hg

end
end Ptx.ByteContentsHeap
