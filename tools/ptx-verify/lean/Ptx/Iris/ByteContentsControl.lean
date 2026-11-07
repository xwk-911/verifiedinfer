import Ptx.Iris.ByteContentsPhases

/-! Native local rules for checked control-only steps. Only the authoritative
controller fragment is updated; every byte fragment can remain in the frame.
-/
namespace Ptx.ByteContentsHeap
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

theorem store_controlFinished (state : State) (node : Unified.ControlNode) :
    store (ByteContents.controlFinished state node) =
      insert (store state) ByteAuthority.controlKey (.control (ByteContents.controlFinished state node)) := by
  apply equiv_iff_eq.mp
  intro k
  by_cases he : ByteAuthority.controlKey = k
  · subst k; simp [store,get?_insert]
  · simp only [store,get?_insert_ne he]
    rfl

theorem control_update_local [GS] (state : State) (node : Unified.ControlNode) :
    genHeapInterp (store state) ∗ control state ==∗
      genHeapInterp (store (ByteContents.controlFinished state node)) ∗ control (ByteContents.controlFinished state node) := by
  unfold control
  iintro ⟨Hheap,Hcontrol⟩
  imod genHeap_update (v₂ := Cell.control (ByteContents.controlFinished state node)) $$ [$Hheap $Hcontrol] with ⟨Hheap,Hcontrol⟩
  rw [← store_controlFinished]
  imodintro
  iframe Hheap Hcontrol

theorem control_local_cps [GS] (ctx : Context) (state : State) (node : Unified.ControlNode)
    (tail : List Action) (frame : IProp GF) (post : Except ByteContents.Error State → IProp GF)
    (hs : ByteContents.finishControl ctx.block ctx.candidate ctx.histories node state = .ok (ByteContents.controlFinished state node))
    (hcont : control (ByteContents.controlFinished state node) ∗ frame ⊢ WP (script ctx tail) {{ result, post result }}) :
    control state ∗ frame ⊢ WP (script ctx (.control node::tail)) {{ result, post result }} := by
  apply step_script_wp ctx state (ByteContents.controlFinished state node) (.control node) tail frame frame post hs ?_ hcont
  iintro ⟨Hheap,Hcontrol,Hframe⟩
  imod control_update_local state node $$ [$Hheap $Hcontrol] with ⟨Hheap,Hcontrol⟩
  imodintro
  iframe Hheap Hcontrol Hframe

theorem control_local_wp [GS] (ctx : Context) (state : State) (node : Unified.ControlNode) (frame : IProp GF)
    (hs : ByteContents.finishControl ctx.block ctx.candidate ctx.histories node state = .ok (ByteContents.controlFinished state node)) :
    control state ∗ frame ⊢ WP (script ctx [.control node])
      {{ result, ⌜result = .ok (ByteContents.controlFinished state node)⌝ ∗ control (ByteContents.controlFinished state node) ∗ frame }} := by
  apply control_local_cps ctx state node [] frame _ hs
  exact script_nil_wp ctx _ frame

end
end Ptx.ByteContentsHeap
