import Ptx.Iris.ByteAcquisition
import Ptx.Hopper.ByteExecution

/-! Native GenHeap witnesses for automatically selected actual-byte footprints.
Global inventory coverage is explicit and supplies all per-node premises.
-/
namespace Ptx.ByteAuthorityHeap
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris Iris.BI Iris.ProgramLogic
noncomputable section

theorem inventory_cycle_run (ctx : Context) (coupled : Bridge.State) (locations : List Location) (node : Unified.ControlNode)
    (hb : ∀ loc mode, ByteAuthority.Uses ctx.candidate node loc mode → loc ∈ locations)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories coupled.done node) :
    IrisExecution.run (transition ctx) (cycleActions node (ByteAuthority.Footprint.inventory ctx.candidate node locations))
      (ByteAuthority.Footprint.initialized coupled locations) =
      .ok (ByteAuthority.Footprint.initialized {coupled with done := fun n => coupled.done n ∨ n = node} locations) := by
  rw [cycle_run]
  exact ByteAuthority.Footprint.inventory_cycle_run hb hr

theorem inventory_cycle_wp [GS] (ctx : Context) (coupled : Bridge.State) (locations : List Location)
    (node : Unified.ControlNode) (frame : IProp GF)
    (hb : ∀ loc mode, ByteAuthority.Uses ctx.candidate node loc mode → loc ∈ locations)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories coupled.done node) :
    control (ByteAuthority.Footprint.initialized coupled locations) ∗
      freePoints (ByteAuthority.Footprint.inventory ctx.candidate node locations) ∗ frame ⊢
      WP (script ctx (cycleActions node (ByteAuthority.Footprint.inventory ctx.candidate node locations)))
      {{ value, ⌜value = .ok (ByteAuthority.Footprint.initialized {coupled with done := fun n => coupled.done n ∨ n = node} locations)⌝ ∗
        control (ByteAuthority.Footprint.initialized {coupled with done := fun n => coupled.done n ∨ n = node} locations) ∗
        freePoints (ByteAuthority.Footprint.inventory ctx.candidate node locations) ∗ frame }} := by
  have hw := cycle_wp_available ctx (ByteAuthority.Footprint.initialized coupled locations) node
    (ByteAuthority.Footprint.inventory ctx.candidate node locations) frame
    (ByteAuthority.Footprint.initialized_available coupled locations) hr
    (ByteAuthority.Footprint.inventory_sound _ _ _) (ByteAuthority.Footprint.inventory_covers hb)
    (ByteAuthority.Footprint.inventory_distinct _ _ _) (ByteAuthority.Footprint.inventory_available _ _ _ _)
  rw [ByteAuthority.Footprint.inventory_cycle_endpoint hb hr] at hw
  exact hw

theorem inventory_cycle_adequate (ctx : Context) (coupled : Bridge.State) (locations : List Location) (node : Unified.ControlNode)
    (hb : ∀ loc mode, ByteAuthority.Uses ctx.candidate node loc mode → loc ∈ locations)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories coupled.done node) :
    adequate .NotStuck (script ctx (cycleActions node (ByteAuthority.Footprint.inventory ctx.candidate node locations)))
      (ByteAuthority.Footprint.initialized coupled locations)
      (fun value _ => value = .ok (ByteAuthority.Footprint.initialized {coupled with done := fun n => coupled.done n ∨ n = node} locations)) := by
  have hw := cycle_adequate ctx (ByteAuthority.Footprint.initialized coupled locations) node
    (ByteAuthority.Footprint.inventory ctx.candidate node locations)
    (ByteAuthority.Footprint.available_pool_supported (ByteAuthority.Footprint.initialized_available coupled locations))
    (ByteAuthority.available_pool_active (ByteAuthority.Footprint.initialized_available coupled locations)) hr
    (ByteAuthority.Footprint.inventory_sound _ _ _) (ByteAuthority.Footprint.inventory_covers hb)
    (ByteAuthority.Footprint.inventory_distinct _ _ _) (ByteAuthority.Footprint.inventory_available _ _ _ _)
  rw [ByteAuthority.Footprint.inventory_cycle_endpoint hb hr] at hw
  exact hw

end
end Ptx.ByteAuthorityHeap
