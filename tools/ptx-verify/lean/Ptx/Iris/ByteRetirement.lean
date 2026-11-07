import Ptx.Iris.ByteAuthority

/-! Local multibyte retirement consumes full fragments for its complete finite
footprint and the exclusive controller snapshot. The snapshot states metadata;
it supplies no ownership of other bytes. All unrelated byte fragments frame.
-/
namespace Ptx.ByteAuthorityHeap
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language
open Iris.ProgramLogic.Language.Notation
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section
local bi (IProp GF)

abbrev Demand := ByteAuthority.Footprint.Demand

def heldPoints [GS] (node : Unified.ControlNode) (demands : List Demand) : IProp GF :=
  iprop([∗list] demand ∈ demands, byte demand.location (.own 1) (.held node demand.mode))
def freePoints [GS] (demands : List Demand) : IProp GF :=
  iprop([∗list] demand ∈ demands, byte demand.location (.own 1) .available)

def releaseStore : List Demand → HeapF Cell → HeapF Cell
  | [],heap => heap
  | demand::rest,heap => insert (releaseStore rest heap) (ByteAuthority.key demand.location) (.byte .available)

theorem releaseStore_lookup (demands : List Demand) (heap : HeapF Cell) (k : Nat) :
    get? (releaseStore demands heap) k = if k ∈ ByteAuthority.Footprint.keys demands then some (.byte .available) else get? heap k := by
  induction demands with
  | nil => simp [releaseStore,ByteAuthority.Footprint.keys]
  | cons demand rest ih =>
    by_cases he : ByteAuthority.key demand.location = k
    · simp [releaseStore,get?_insert,he,ByteAuthority.Footprint.keys]
    · simp [releaseStore,get?_insert_ne he,ih,ByteAuthority.Footprint.keys,Ne.symm he]

theorem store_retired_footprint (state : State) (node : Unified.ControlNode) (demands : List Demand)
    (hh : ByteAuthority.Footprint.Held state node demands) (hf : ByteAuthority.Footprint.Frame state node demands) :
    store (ByteAuthority.retired state node) =
      insert (releaseStore demands (store state)) ByteAuthority.controlKey (.control (ByteAuthority.retired state node)) := by
  apply equiv_iff_eq.mp
  intro k
  by_cases he : ByteAuthority.controlKey = k
  · subst k; simp [get?_insert]
  · rw [get?_insert_ne he,releaseStore_lookup]
    simp only [store,get?_insert_ne he,ByteAuthority.retired]
    rw [← ByteAuthority.Footprint.clear_eq_release hh hf]
    simp only [get?_map,ByteAuthority.Footprint.clear_lookup]
    split <;> rfl

theorem release_points [GS] (node : Unified.ControlNode) (demands : List Demand) (heap : HeapF Cell) :
    genHeapInterp heap ∗ heldPoints node demands ==∗ genHeapInterp (releaseStore demands heap) ∗ freePoints demands := by
  induction demands generalizing heap with
  | nil =>
    simp only [releaseStore,heldPoints,freePoints,Iris.Algebra.BigOpL.bigOpL_nil]
    iintro H
    imodintro
    iexact H
  | cons demand rest ih =>
    change genHeapInterp heap ∗ (byte demand.location (.own 1) (.held node demand.mode) ∗ heldPoints node rest) ==∗
      genHeapInterp (insert (releaseStore rest heap) (ByteAuthority.key demand.location) (.byte .available)) ∗
        (byte demand.location (.own 1) .available ∗ freePoints rest)
    iintro ⟨Hheap,Hhead,Hrest⟩
    imod ih heap $$ [$Hheap $Hrest] with ⟨Hheap,Hrest⟩
    unfold byte
    imod genHeap_update (v₂ := Cell.byte .available) $$ [$Hheap $Hhead] with ⟨Hheap,Hhead⟩
    imodintro
    iframe Hheap Hhead Hrest

theorem finish_local_wp [g : GS] (ctx : Context) (state : State) (node : Unified.ControlNode) (demands : List Demand)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories state.coupled.done node)
    (hs : ByteAuthority.Footprint.Sound ctx.candidate node demands) (hc : ByteAuthority.Footprint.Covers ctx.candidate node demands)
    (hd : ByteAuthority.Footprint.Distinct demands) (hh : ByteAuthority.Footprint.Held state node demands)
    (hf : ByteAuthority.Footprint.Frame state node demands) :
    control state ∗ heldPoints node demands ⊢ WP (finishInvoke ctx node demands)
      {{ value, ⌜value = .ok (ByteAuthority.retired state node)⌝ ∗ control (ByteAuthority.retired state node) ∗ freePoints demands }} := by
  let _ := g.inv
  iintro ⟨Hcontrol,Hheld⟩
  iapply wp_lift_atomic_step (show toVal (finishInvoke ctx node demands) = none from rfl)
  isimp [stateInterp]
  iintro %actual %ns %obs %obs' %nt Hheap
  ihave %heq : ⌜actual = state⌝ $$ [Hheap Hcontrol]
  · imod control_valid actual state $$ [$Hheap $Hcontrol] with %h
    ipureintro; exact h
  subst actual
  have hstep : transition ctx (.finish node demands) state = .ok (ByteAuthority.retired state node) :=
    ByteAuthority.Footprint.finish_succeeds hr hs hc hd hh hf
  imodintro
  isplit
  · ipureintro
    exact ⟨[],IrisExecution.Expr.result (.ok (ByteAuthority.retired state node)),ByteAuthority.retired state node,[],IrisExecution.Prim.success hstep⟩
  inext
  iintro %e' %actual %forks %hp Hcredit
  obtain ⟨hstate,hval,hfork⟩ := IrisExecution.prim_deterministic hstep hp
  simp only [IrisExecution.after] at hstate
  subst actual forks
  imod release_points node demands (store state) $$ [$Hheap $Hheld] with ⟨Hheap,Hfree⟩
  unfold control
  imod genHeap_update (v₂ := Cell.control (ByteAuthority.retired state node)) $$ [$Hheap $Hcontrol] with ⟨Hheap,Hcontrol⟩
  rw [← store_retired_footprint state node demands hh hf]
  imodintro
  simp only [Iris.Algebra.BigOpL.bigOpL_nil]
  isplitl [Hheap]
  · iexact Hheap
  · isplitl [Hcontrol Hfree]
    · iexists (.ok (ByteAuthority.retired state node))
      isplit
      · ipureintro; exact hval
      · isplit
        · ipureintro; rfl
        · iframe Hcontrol Hfree
    · itrivial

theorem map_heldPoints [GS] (node : Unified.ControlNode) (demands : List Demand) (heap : HeapF Cell)
    (hd : ByteAuthority.Footprint.Distinct demands)
    (hl : ∀ demand ∈ demands, get? heap (ByteAuthority.key demand.location) = some (.byte (.held node demand.mode))) :
    iprop([∗map] k ↦ value ∈ heap, pointsTo k (.own 1) value) ⊢ heldPoints node demands := by
  induction demands generalizing heap with
  | nil =>
    iintro Hall
    unfold heldPoints
    simp only [Iris.Algebra.BigOpL.bigOpL_nil]
    itrivial
  | cons head rest ih =>
    have hdistinct : ByteAuthority.key head.location ∉ ByteAuthority.Footprint.keys rest ∧ ByteAuthority.Footprint.Distinct rest := by
      simpa only [ByteAuthority.Footprint.Distinct,ByteAuthority.Footprint.keys,List.map_cons,List.nodup_cons] using hd
    change _ ⊢ byte head.location (.own 1) (.held node head.mode) ∗ heldPoints node rest
    iintro Hall
    icases (BigSepM.bigSepM_delete (hl head (by simp))) $$ Hall with ⟨Hhead,Hrest⟩
    isplitl [Hhead]
    · unfold byte; iexact Hhead
    · iapply ih (Iris.Std.PartialMap.delete heap (ByteAuthority.key head.location)) hdistinct.2 ?_ $$ Hrest
      intro demand hm
      have hne : ByteAuthority.key head.location ≠ ByteAuthority.key demand.location := by
        intro he
        exact hdistinct.1 (List.mem_map.mpr ⟨demand,hm,he.symm⟩)
      rw [get?_delete_ne hne]
      exact hl demand (by simp [hm])

theorem allPoints_control_held [GS] (state : State) (node : Unified.ControlNode) (demands : List Demand)
    (hd : ByteAuthority.Footprint.Distinct demands) (hh : ByteAuthority.Footprint.Held state node demands) :
    allPoints state ⊢ control state ∗ heldPoints node demands := by
  unfold allPoints control
  iintro Hall
  icases (BigSepM.bigSepM_delete (store_control state)) $$ Hall with ⟨Hcontrol,Hrest⟩
  isplitl [Hcontrol]
  · iexact Hcontrol
  · iapply map_heldPoints node demands _ hd ?_ $$ Hrest
    intro demand hm
    rw [get?_delete_ne (Ne.symm (ByteAuthority.byte_key_not_control demand.location)),store_byte,hh demand hm]
    rfl

theorem finish_adequate (ctx : Context) (state : State) (node : Unified.ControlNode) (demands : List Demand)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories state.coupled.done node)
    (hs : ByteAuthority.Footprint.Sound ctx.candidate node demands) (hc : ByteAuthority.Footprint.Covers ctx.candidate node demands)
    (hd : ByteAuthority.Footprint.Distinct demands) (hh : ByteAuthority.Footprint.Held state node demands)
    (hf : ByteAuthority.Footprint.Frame state node demands) :
    adequate .NotStuck (finishInvoke ctx node demands) state (fun value _ => value = .ok (ByteAuthority.retired state node)) := by
  apply heap_adequacy
  intro _
  iintro Hall
  ihave Hparts := allPoints_control_held state node demands hd hh $$ Hall
  ihave Hwp := finish_local_wp ctx state node demands hr hs hc hd hh hf $$ Hparts
  iapply wp_mono ?_ $$ Hwp
  intro value
  iintro ⟨%hv,Hcontrol,Hfree⟩
  ipureintro; exact hv

theorem finish_wp_after_available_execution [GS] (ctx : Context) (initial state : State) (node : Unified.ControlNode) (demands : List Demand)
    {cluster plan} (hp : ∀ k owner, get? initial.bytes k = some owner → owner = .available)
    (hsteps : ByteAuthority.Steps ctx.block ctx.candidate ctx.histories cluster plan initial state)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories state.coupled.done node)
    (hs : ByteAuthority.Footprint.Sound ctx.candidate node demands) (hc : ByteAuthority.Footprint.Covers ctx.candidate node demands)
    (hd : ByteAuthority.Footprint.Distinct demands) (hh : ByteAuthority.Footprint.Held state node demands) :
    control state ∗ heldPoints node demands ⊢ WP (finishInvoke ctx node demands)
      {{ value, ⌜value = .ok (ByteAuthority.retired state node)⌝ ∗ control (ByteAuthority.retired state node) ∗ freePoints demands }} := by
  apply finish_local_wp ctx state node demands hr hs hc hd hh
  exact ByteAuthority.Footprint.frame_of_source
    (ByteAuthority.Footprint.supported_steps (ByteAuthority.Footprint.available_pool_supported hp) hsteps)
    (ByteAuthority.steps_active (ByteAuthority.available_pool_active hp) hsteps) hc

end
end Ptx.ByteAuthorityHeap
