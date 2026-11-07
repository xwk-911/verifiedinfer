import Ptx.Iris.ByteContentsAvailable
import Ptx.Hopper.ByteExecution

/-! Construct checked value scripts from actual reached control prefixes.
Every memory control executes its finite actual-use inventory and real reads;
arrivals execute the checked control action. Frontier obligations must be
established for the source family; arbitrary weak executions are not serialized.
-/
namespace Ptx.ByteContentsHeap
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

theorem ready_value_step (ctx : Context) (locations : List Location) {initial rf co scope state node}
    (hm : Unified.CausalConstraints Tma.localShared Access.globalDescriptor ctx.candidate initial rf co ctx.histories scope)
    (he : ∀ read loc value, ByteContents.readByte ctx.candidate read loc = some value →
      Unified.Eligible Tma.localShared Access.globalDescriptor ctx.candidate ctx.histories scope rf read loc)
    (hn : ∀ id, Access.copyAt ctx.candidate.view id = none)
    (hb : ByteAuthority.Footprint.Bounded ctx.candidate locations)
    (hv : Valid ctx.block ctx.candidate ctx.histories state.coupled.done)
    (hf : ReadFrontier ctx rf) (hi : FutureReads ctx initial rf state)
    (ha : Available state) (hl : Allocated state locations)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories state.coupled.done node) :
    ∃ actions next, IrisExecution.run (transition ctx) actions state = .ok next ∧
      next.coupled.done = (fun n => state.coupled.done n ∨ n = node) ∧ Available next ∧ Allocated next locations ∧ FutureReads ctx initial rf next := by
  cases hrep : ByteContents.memoryOfControl node with
  | none =>
    cases node with
    | base _ | operand _ _ => cases hrep
    | arrival id =>
      have hs := ByteContents.finish_arrival_succeeds hr (ByteContents.available_control_frame ha _)
      have hrun : IrisExecution.run (transition ctx) [.control (.arrival id)] state = .ok (ByteContents.controlFinished state (.arrival id)) := by
        rw [IrisExecution.run_singleton]
        exact hs
      exact ⟨[.control (.arrival id)],ByteContents.controlFinished state (.arrival id),hrun,rfl,ha,hl,
        future_run_preserved ctx _ hm he hv hf hi hrun⟩
  | some memory =>
    have hc := ByteContents.memoryOfControl_actual hrep
    let demands := ByteAuthority.Footprint.inventory ctx.candidate (Unified.memoryControlNode memory) locations
    let values := ByteContents.valueAt state
    let acquired := granted state (Unified.memoryControlNode memory) demands values
    let finished := ByteContents.finished ctx.candidate memory demands acquired
    have hd : ByteAuthority.Footprint.Distinct demands := ByteAuthority.Footprint.inventory_distinct _ _ _
    have hsound : ByteAuthority.Footprint.Sound ctx.candidate (Unified.memoryControlNode memory) demands := ByteAuthority.Footprint.inventory_sound _ _ _
    have hcover : ByteAuthority.Footprint.Covers ctx.candidate (Unified.memoryControlNode memory) demands := ByteAuthority.Footprint.inventory_covers (hb _)
    have hfree : Free state demands values := free_of_available ha hl (fun _ hd => ByteAuthority.Footprint.inventory_location hd)
    have hready : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories state.coupled.done (Unified.memoryControlNode memory) := by rw [hc]; exact hr
    have hacquire := acquisition_run ctx state _ demands values hready hsound hd hfree
    have hvalid : Valid ctx.block ctx.candidate ctx.histories acquired.coupled.done := run_valid ctx _ hv hacquire
    have hfuture : FutureReads ctx initial rf acquired := future_run_preserved ctx _ hm he hv hf hi hacquire
    have hready' : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories acquired.coupled.done (Unified.memoryControlNode memory) := by
      change ByteAuthority.Ready _ _ _ (granted _ _ _ _).coupled.done _
      rw [granted_coupled]
      exact hready
    have hreads := future_reads_at_ready hm he hvalid hf hfuture hready'
    have hmeta := ByteAuthority.Footprint.finish_succeeds hready' hsound hcover hd (matches_held (granted_matches state _ demands values hd))
      (granted_frame (ByteContents.available_control_frame ha _))
    have hfinish : transition ctx (.finish memory demands) acquired = .ok finished :=
      ByteContents.finish_succeeds hmeta (ByteContents.memoryOfControl_linked hn hrep) hreads
    have hrun := cycle_run ctx state finished memory demands values hready hsound hd hfree hfinish
    refine ⟨cycleActions memory demands,finished,hrun,?_,cycle_available ha hd hfinish,
      allocated_of_domain hl (run_domain ctx _ hrun),future_run_preserved ctx _ hm he hv hf hi hrun⟩
    change (fun n => acquired.coupled.done n ∨ n = Unified.memoryControlNode memory) = _
    rw [show acquired.coupled = state.coupled from granted_coupled _ _ _ _,hc]

theorem reached_value_witness (ctx : Context) (locations : List Location) (state : State) {initial rf co scope done}
    (hm : Unified.CausalConstraints Tma.localShared Access.globalDescriptor ctx.candidate initial rf co ctx.histories scope)
    (he : ∀ read loc value, ByteContents.readByte ctx.candidate read loc = some value →
      Unified.Eligible Tma.localShared Access.globalDescriptor ctx.candidate ctx.histories scope rf read loc)
    (hn : ∀ id, Access.copyAt ctx.candidate.view id = none)
    (hb : ByteAuthority.Footprint.Bounded ctx.candidate locations)
    (hf : ReadFrontier ctx rf) (hi : FutureReads ctx initial rf state)
    (ha : Available state) (hl : Allocated state locations) (hstart : state.coupled.done = (fun _ => False))
    (hr : Reached ctx.block ctx.candidate ctx.histories done) :
    ∃ actions next, IrisExecution.run (transition ctx) actions state = .ok next ∧
      next.coupled.done = done ∧ Available next ∧ Allocated next locations ∧ FutureReads ctx initial rf next := by
  induction hr with
  | empty => exact ⟨[],state,rfl,hstart,ha,hl,hi⟩
  | @next before after hprefix hadvance ih =>
    obtain ⟨first,mid,hrun,hcut,ha',hl',hi'⟩ := ih
    cases hadvance with
    | next node actual fresh predecessors =>
      have hready : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories mid.coupled.done node := by
        rw [hcut]
        exact ⟨actual,fresh,predecessors⟩
      have hvalid : Valid ctx.block ctx.candidate ctx.histories mid.coupled.done := by rw [hcut]; exact reached_valid hprefix
      obtain ⟨rest,last,hrest,hcut',ha'',hl'',hi''⟩ := ready_value_step ctx locations hm he hn hb hvalid hf hi' ha' hl' hready
      refine ⟨first++rest,last,?_,?_,ha'',hl'',hi''⟩
      · rw [IrisExecution.run_append,hrun]
        exact hrest
      · rw [hcut',hcut]

end
end Ptx.ByteContentsHeap
