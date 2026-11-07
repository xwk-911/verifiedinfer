import Ptx.Iris.ByteContentsFuture
import Ptx.Hopper.ByteContentsNodes
import Ptx.Hopper.ByteInventory

/-! Available value pools and complete local cycles. Availability and allocation
are propagated by actual checked actions; no initially held fragments or desired
per-node byte values are supplied by the caller.
-/
namespace Ptx.ByteContentsHeap
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

def Available (state : State) : Prop := ∀ k payload, get? state.cells k = some payload → payload.owner = .available
def Allocated (state : State) (locations : List Location) : Prop :=
  ∀ loc ∈ locations, (get? state.cells (ByteAuthority.key loc)).isSome = true

theorem allocated_of_domain {before after : State} {locations}
    (ha : Allocated before locations) (hd : dom before.cells = dom after.cells) : Allocated after locations := by
  intro loc hm
  have hx : dom before.cells (ByteAuthority.key loc) := ha loc hm
  rw [hd] at hx
  exact hx

theorem free_of_available {state demands locations}
    (ha : Available state) (hl : Allocated state locations)
    (hb : ∀ demand ∈ demands, demand.location ∈ locations) : Free state demands (ByteContents.valueAt state) := by
  intro demand hm
  obtain ⟨payload,hg⟩ := Option.isSome_iff_exists.mp (hl demand.location (hb demand hm))
  have ho := ha _ _ hg
  cases payload with
  | mk owner value =>
    cases ho
    unfold ByteContents.valueAt
    rw [hg]
    rfl

theorem run_domain (ctx : Context) (actions : List Action) {state next}
    (hr : IrisExecution.run (transition ctx) actions state = .ok next) : dom state.cells = dom next.cells := by
  induction actions generalizing state with
  | nil => cases hr; rfl
  | cons head rest ih =>
    change (transition ctx head state).bind (fun mid => IrisExecution.run (transition ctx) rest mid) = .ok next at hr
    cases hs : transition ctx head state with
    | error error => simp [hs,Except.bind] at hr
    | ok mid => exact (action_domain ctx hs).trans (ih (by simpa only [hs,Except.bind] using hr))

theorem action_protocol (ctx : Context) {action state next}
    (hs : transition ctx action state = .ok next) : next.coupled.protocol = state.coupled.protocol := by
  cases action with
  | claim request => rw [(ByteContents.claim_spec hs).choose_spec.2.2.1]; rfl
  | control node => rw [(ByteContents.finishControl_spec hs).2.1]; rfl
  | finish node demands => rw [(ByteContents.finish_spec hs).2.2.1]; rfl

theorem run_protocol (ctx : Context) (actions : List Action) {state next}
    (hr : IrisExecution.run (transition ctx) actions state = .ok next) : next.coupled.protocol = state.coupled.protocol := by
  induction actions generalizing state with
  | nil => cases hr; rfl
  | cons head rest ih =>
    change (transition ctx head state).bind (fun mid => IrisExecution.run (transition ctx) rest mid) = .ok next at hr
    cases hs : transition ctx head state with
    | error error => simp [hs,Except.bind] at hr
    | ok mid => exact (ih (by simpa only [hs,Except.bind] using hr)).trans (action_protocol ctx hs)

theorem cycle_available {ctx : Context} {state next memory demands}
    (ha : Available state) (hd : ByteAuthority.Footprint.Distinct demands)
    (hs : transition ctx (.finish memory demands) (granted state (Unified.memoryControlNode memory) demands (ByteContents.valueAt state)) = .ok next) : Available next := by
  have hfree := finish_free hs (granted_matches state _ demands _ hd)
  intro k payload hg
  by_cases hk : k ∈ ByteAuthority.Footprint.keys demands
  · obtain ⟨demand,hm,he⟩ := List.mem_map.mp hk
    have hx := hfree demand hm
    rw [he] at hx
    rw [hx] at hg
    cases hg
    rfl
  · rw [(ByteContents.finish_spec hs).2.2.1] at hg
    change get? (ByteContents.finishCells ctx.candidate memory demands (granted state (Unified.memoryControlNode memory) demands (ByteContents.valueAt state)).cells) k = some payload at hg
    rw [ByteContents.finishCells_outside _ _ _ _ _ hk,granted_outside _ _ _ _ _ hk] at hg
    exact ha k payload hg

theorem initial_cells_available (coupled : Bridge.State) (locations : List Location) (initial : Location → Symbolic.Byte) :
    Available ⟨coupled,ByteContents.initialCells locations initial⟩ :=
  fun _ _ hg => ByteContents.initialCells_owner_available hg

theorem initial_cells_allocated (coupled : Bridge.State) (locations : List Location) (initial : Location → Symbolic.Byte) :
    Allocated ⟨coupled,ByteContents.initialCells locations initial⟩ locations := by
  intro loc hm
  rw [ByteContents.initialCells_member hm]
  rfl

end
end Ptx.ByteContentsHeap
