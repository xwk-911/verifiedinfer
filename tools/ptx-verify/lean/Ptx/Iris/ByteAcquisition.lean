import Ptx.Iris.ByteRetirement
import Ptx.Hopper.ByteAcquisition

/-! Native GenHeap composition for actual byte acquisition scripts. Each claim
is a separate physical step; no whole-script OwnP/atomic replacement is used.
-/
namespace Ptx.ByteAuthorityHeap
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language
open Iris.ProgramLogic.Language.Notation
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
open Iris.Std.LawfulSet
noncomputable section
local bi (IProp GF)

abbrev script (ctx : Context) (actions : List Action) : Expr ctx := IrisExecution.Expr.script actions

def acquisitionActions (node : Unified.ControlNode) (demands : List Demand) : List Action :=
  demands.map (fun demand => .claim ⟨node,demand.location,demand.mode⟩)
def cycleActions (node : Unified.ControlNode) (demands : List Demand) : List Action :=
  acquisitionActions node demands ++ [.finish node demands]

theorem step_script_wp [g : GS] (ctx : Context) (state next : State) (action : Action) (tail : List Action)
    (before after : IProp GF) (post : Except ByteAuthority.Error State → IProp GF)
    (hs : transition ctx action state = .ok next)
    (hupdate : genHeapInterp (store state) ∗ control state ∗ before ==∗ genHeapInterp (store next) ∗ control next ∗ after)
    (hcont : control next ∗ after ⊢ WP (script ctx tail) {{ value, post value }}) :
    control state ∗ before ⊢ WP (script ctx (action::tail)) {{ value, post value }} := by
  let _ := g.inv
  iintro ⟨Hcontrol,Hbefore⟩
  iapply wp_lift_step (show toVal (script ctx (action::tail)) = none from rfl)
  isimp [stateInterp]
  iintro %actual %ns %obs %obs' %nt Hheap
  ihave %heq : ⌜actual = state⌝ $$ [Hheap Hcontrol]
  · imod control_valid actual state $$ [$Hheap $Hcontrol] with %h
    ipureintro; exact h
  subst actual
  iapply fupd_mask_intro empty_subset
  iintro Hclose
  isplit
  · ipureintro
    exact ⟨[],IrisExecution.Expr.script tail,next,[],IrisExecution.Prim.next hs⟩
  inext
  iintro %e' %actual %forks %hp Hcredit
  change IrisExecution.Prim (transition ctx) (.script (action::tail),state) obs (e',actual,forks) at hp
  cases hp with
  | next hnext =>
    have heq := Except.ok.inj (hs.symm.trans hnext)
    subst actual
    imod hupdate $$ [$Hheap $Hcontrol $Hbefore] with ⟨Hheap,Hcontrol,Hafter⟩
    imod Hclose
    imodintro
    simp only [Iris.Algebra.BigOpL.bigOpL_nil]
    isplitl [Hheap]
    · iexact Hheap
    · isplitl [Hcontrol Hafter]
      · iapply hcont $$ [$Hcontrol $Hafter]
      · itrivial
  | abort herr => cases hs.symm.trans herr

theorem script_nil_wp [g : GS] (ctx : Context) (state : State) (frame : IProp GF) :
    control state ∗ frame ⊢ WP (script ctx []) {{ value, ⌜value = .ok state⌝ ∗ control state ∗ frame }} := by
  let _ := g.inv
  iintro ⟨Hcontrol,Hframe⟩
  iapply wp_lift_atomic_step (show toVal (script ctx []) = none from rfl)
  isimp [stateInterp]
  iintro %actual %ns %obs %obs' %nt Hheap
  ihave %heq : ⌜actual = state⌝ $$ [Hheap Hcontrol]
  · imod control_valid actual state $$ [$Hheap $Hcontrol] with %h
    ipureintro; exact h
  subst actual
  imodintro
  isplit
  · ipureintro
    exact ⟨[],IrisExecution.Expr.result (.ok state),state,[],IrisExecution.Prim.finish state⟩
  inext
  iintro %e' %actual %forks %hp Hcredit
  change IrisExecution.Prim (transition ctx) (.script [],state) obs (e',actual,forks) at hp
  cases hp
  imodintro
  simp only [Iris.Algebra.BigOpL.bigOpL_nil]
  isplitl [Hheap]
  · iexact Hheap
  · isplitl [Hcontrol Hframe]
    · iexists (.ok state)
      isplit
      · ipureintro; rfl
      · isplit
        · ipureintro; rfl
        · iframe Hcontrol Hframe
    · itrivial

theorem claim_update [GS] (state : State) (request : ByteAuthority.Claim) :
    genHeapInterp (store state) ∗ control state ∗ byte request.location (.own 1) .available ==∗
      genHeapInterp (store {state with bytes := insert state.bytes (ByteAuthority.key request.location) (.held request.node request.mode)}) ∗
      control {state with bytes := insert state.bytes (ByteAuthority.key request.location) (.held request.node request.mode)} ∗
      byte request.location (.own 1) (.held request.node request.mode) := by
  iintro ⟨Hheap,Hcontrol,Hbyte⟩
  unfold control byte
  imod genHeap_update (v₂ := Cell.byte (.held request.node request.mode)) $$ [$Hheap $Hbyte] with ⟨Hheap,Hbyte⟩
  imod genHeap_update (v₂ := Cell.control {state with bytes := insert state.bytes (ByteAuthority.key request.location) (.held request.node request.mode)})
    $$ [$Hheap $Hcontrol] with ⟨Hheap,Hcontrol⟩
  rw [← store_set_byte]
  imodintro
  iframe Hheap Hcontrol Hbyte

theorem finish_update [GS] (state : State) (node : Unified.ControlNode) (demands : List Demand)
    (hh : ByteAuthority.Footprint.Held state node demands) (hf : ByteAuthority.Footprint.Frame state node demands) :
    genHeapInterp (store state) ∗ control state ∗ heldPoints node demands ==∗
      genHeapInterp (store (ByteAuthority.retired state node)) ∗ control (ByteAuthority.retired state node) ∗ freePoints demands := by
  iintro ⟨Hheap,Hcontrol,Hheld⟩
  imod release_points node demands (store state) $$ [$Hheap $Hheld] with ⟨Hheap,Hfree⟩
  unfold control
  imod genHeap_update (v₂ := Cell.control (ByteAuthority.retired state node)) $$ [$Hheap $Hcontrol] with ⟨Hheap,Hcontrol⟩
  rw [← store_retired_footprint state node demands hh hf]
  imodintro
  iframe Hheap Hcontrol Hfree

theorem acquisition_cps [GS] (ctx : Context) (state : State) (node : Unified.ControlNode) (demands : List Demand)
    (tail : List Action) (frame : IProp GF) (post : Except ByteAuthority.Error State → IProp GF)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories state.coupled.done node)
    (hs : ByteAuthority.Footprint.Sound ctx.candidate node demands) (hd : ByteAuthority.Footprint.Distinct demands)
    (ha : ByteAuthority.Footprint.Available state demands)
    (hcont : control (ByteAuthority.Footprint.granted state node demands) ∗ heldPoints node demands ∗ frame ⊢
      WP (script ctx tail) {{ value, post value }}) :
    control state ∗ freePoints demands ∗ frame ⊢ WP (script ctx (acquisitionActions node demands ++ tail)) {{ value, post value }} := by
  induction demands generalizing state tail frame post with
  | nil =>
    simpa only [acquisitionActions,List.map_nil,List.nil_append,ByteAuthority.Footprint.granted,heldPoints,freePoints,Iris.Algebra.BigOpL.bigOpL_nil] using hcont
  | cons head rest ih =>
    let mid : State := {state with bytes := insert state.bytes (ByteAuthority.key head.location) (.held node head.mode)}
    have hstep : transition ctx (.claim ⟨node,head.location,head.mode⟩) state = .ok mid :=
      ByteAuthority.claim_succeeds hr (hs head (by simp)) (ha head (by simp))
    change (control state ∗ (byte head.location (.own 1) .available ∗ freePoints rest) ∗ frame) ⊢
      WP (script ctx (.claim ⟨node,head.location,head.mode⟩ :: (acquisitionActions node rest ++ tail))) {{ value, post value }}
    iintro ⟨Hcontrol,⟨Hhead,Hrest⟩,Hframe⟩
    iapply step_script_wp ctx state mid (.claim ⟨node,head.location,head.mode⟩) (acquisitionActions node rest ++ tail)
      iprop(byte head.location (.own 1) .available ∗ freePoints rest ∗ frame)
      iprop(freePoints rest ∗ byte head.location (.own 1) (.held node head.mode) ∗ frame) post hstep ?_ ?_
      $$ [$Hcontrol $Hhead $Hrest $Hframe]
    · iintro ⟨Hheap,Hcontrol,Hhead,Hrest,Hframe⟩
      imod claim_update state ⟨node,head.location,head.mode⟩ $$ [$Hheap $Hcontrol $Hhead] with ⟨Hheap,Hcontrol,Hhead⟩
      imodintro
      iframe Hheap Hcontrol Hhead Hrest Hframe
    · iintro ⟨Hcontrol,Hrest,Hhead,Hframe⟩
      iapply ih (state := mid) (tail := tail) (frame := iprop(byte head.location (.own 1) (.held node head.mode) ∗ frame))
        (post := post) hr (by intro demand hm; exact hs demand (by simp [hm])) (ByteAuthority.Footprint.distinct_tail hd).2
        (ByteAuthority.Footprint.available_after_head hd ha) ?_ $$ [$Hcontrol $Hrest $Hhead $Hframe]
      iintro ⟨Hcontrol,Hheld,Hhead,Hframe⟩
      have hcont' : control (ByteAuthority.Footprint.granted mid node rest) ∗
          (byte head.location (.own 1) (.held node head.mode) ∗ heldPoints node rest) ∗ frame ⊢
          WP (script ctx tail) {{ value, post value }} := hcont
      iapply hcont' $$ [$Hcontrol $Hhead $Hheld $Hframe]

theorem run_append (ctx : Context) (first last : List Action) (state : State) :
    IrisExecution.run (transition ctx) (first++last) state =
      (IrisExecution.run (transition ctx) first state).bind (fun mid => IrisExecution.run (transition ctx) last mid) := by
  induction first generalizing state with
  | nil => rfl
  | cons action rest ih =>
    cases hs : transition ctx action state <;> simp [IrisExecution.run,hs,Except.bind,ih]

theorem acquisition_run (ctx : Context) (node : Unified.ControlNode) (demands : List Demand) (state : State) :
    IrisExecution.run (transition ctx) (acquisitionActions node demands) state =
      ByteAuthority.Footprint.acquire ctx.block ctx.candidate ctx.histories node demands state := by
  induction demands generalizing state with
  | nil => rfl
  | cons head rest ih =>
    change (ByteAuthority.claim ctx.block ctx.candidate ctx.histories ⟨node,head.location,head.mode⟩ state).bind
        (fun mid => IrisExecution.run (transition ctx) (acquisitionActions node rest) mid) =
      (ByteAuthority.claim ctx.block ctx.candidate ctx.histories ⟨node,head.location,head.mode⟩ state).bind
        (fun mid => ByteAuthority.Footprint.acquire ctx.block ctx.candidate ctx.histories node rest mid)
    cases hs : ByteAuthority.claim ctx.block ctx.candidate ctx.histories ⟨node,head.location,head.mode⟩ state with
    | error error => rfl
    | ok mid => exact ih mid

theorem cycle_run (ctx : Context) (node : Unified.ControlNode) (demands : List Demand) (state : State) :
    IrisExecution.run (transition ctx) (cycleActions node demands) state =
      ByteAuthority.Footprint.cycle ctx.block ctx.candidate ctx.histories node demands state := by
  simp only [cycleActions,run_append,acquisition_run,ByteAuthority.Footprint.cycle]
  cases hs : ByteAuthority.Footprint.acquire ctx.block ctx.candidate ctx.histories node demands state with
  | error error => rfl
  | ok mid =>
    cases hf : ByteAuthority.Footprint.finish ctx.block ctx.candidate ctx.histories node demands mid <;>
      simp [hs,hf,Except.bind,IrisExecution.run,transition]

theorem cycle_wp [GS] (ctx : Context) (state : State) (node : Unified.ControlNode) (demands : List Demand) (frame : IProp GF)
    (hp : ByteAuthority.Footprint.Supported state) (hi : ByteAuthority.Active ctx.block ctx.candidate ctx.histories state)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories state.coupled.done node)
    (hs : ByteAuthority.Footprint.Sound ctx.candidate node demands) (hc : ByteAuthority.Footprint.Covers ctx.candidate node demands)
    (hd : ByteAuthority.Footprint.Distinct demands) (ha : ByteAuthority.Footprint.Available state demands) :
    control state ∗ freePoints demands ∗ frame ⊢ WP (script ctx (cycleActions node demands))
      {{ value, ⌜value = .ok (ByteAuthority.retired (ByteAuthority.Footprint.granted state node demands) node)⌝ ∗
        control (ByteAuthority.retired (ByteAuthority.Footprint.granted state node demands) node) ∗ freePoints demands ∗ frame }} := by
  let granted := ByteAuthority.Footprint.granted state node demands
  have hready : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories granted.coupled.done node := by
    simpa only [granted,ByteAuthority.Footprint.granted_coupled] using hr
  have hheld := ByteAuthority.Footprint.granted_held state node demands hd
  have hframe := ByteAuthority.Footprint.granted_frame_from_invariants hp hi hr hs hc hd ha
  have hfinish : transition ctx (.finish node demands) granted = .ok (ByteAuthority.retired granted node) :=
    ByteAuthority.Footprint.finish_succeeds hready hs hc hd hheld hframe
  apply acquisition_cps ctx state node demands [.finish node demands] frame _ hr hs hd ha
  iintro ⟨Hcontrol,Hheld,Hframe⟩
  iapply step_script_wp ctx granted (ByteAuthority.retired granted node) (.finish node demands) []
    iprop(heldPoints node demands ∗ frame) iprop(freePoints demands ∗ frame) _ hfinish ?_ ?_ $$ [$Hcontrol $Hheld $Hframe]
  · iintro ⟨Hheap,Hcontrol,Hheld,Hframe⟩
    imod finish_update granted node demands hheld hframe $$ [$Hheap $Hcontrol $Hheld] with ⟨Hheap,Hcontrol,Hfree⟩
    imodintro
    iframe Hheap Hcontrol Hfree Hframe
  · exact script_nil_wp ctx (ByteAuthority.retired granted node) iprop(freePoints demands ∗ frame)

theorem cycle_wp_available [GS] (ctx : Context) (state : State) (node : Unified.ControlNode) (demands : List Demand) (frame : IProp GF)
    (hp : ∀ k owner, get? state.bytes k = some owner → owner = .available)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories state.coupled.done node)
    (hs : ByteAuthority.Footprint.Sound ctx.candidate node demands) (hc : ByteAuthority.Footprint.Covers ctx.candidate node demands)
    (hd : ByteAuthority.Footprint.Distinct demands) (ha : ByteAuthority.Footprint.Available state demands) :
    control state ∗ freePoints demands ∗ frame ⊢ WP (script ctx (cycleActions node demands))
      {{ value, ⌜value = .ok (ByteAuthority.retired (ByteAuthority.Footprint.granted state node demands) node)⌝ ∗
        control (ByteAuthority.retired (ByteAuthority.Footprint.granted state node demands) node) ∗ freePoints demands ∗ frame }} :=
  cycle_wp ctx state node demands frame (ByteAuthority.Footprint.available_pool_supported hp)
    (ByteAuthority.available_pool_active hp) hr hs hc hd ha

theorem map_freePoints [GS] (demands : List Demand) (heap : HeapF Cell) (hd : ByteAuthority.Footprint.Distinct demands)
    (hl : ∀ demand ∈ demands, get? heap (ByteAuthority.key demand.location) = some (.byte .available)) :
    iprop([∗map] k ↦ value ∈ heap, pointsTo k (.own 1) value) ⊢ freePoints demands := by
  induction demands generalizing heap with
  | nil =>
    iintro Hall
    unfold freePoints
    simp only [Iris.Algebra.BigOpL.bigOpL_nil]
    itrivial
  | cons head rest ih =>
    have hdistinct := ByteAuthority.Footprint.distinct_tail hd
    change _ ⊢ byte head.location (.own 1) .available ∗ freePoints rest
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

theorem allPoints_control_free [GS] (state : State) (demands : List Demand)
    (hd : ByteAuthority.Footprint.Distinct demands) (ha : ByteAuthority.Footprint.Available state demands) :
    allPoints state ⊢ control state ∗ freePoints demands := by
  unfold allPoints control
  iintro Hall
  icases (BigSepM.bigSepM_delete (store_control state)) $$ Hall with ⟨Hcontrol,Hrest⟩
  isplitl [Hcontrol]
  · iexact Hcontrol
  · iapply map_freePoints demands _ hd ?_ $$ Hrest
    intro demand hm
    rw [get?_delete_ne (Ne.symm (ByteAuthority.byte_key_not_control demand.location)),store_byte,ha demand hm]
    rfl

theorem cycle_adequate (ctx : Context) (state : State) (node : Unified.ControlNode) (demands : List Demand)
    (hp : ByteAuthority.Footprint.Supported state) (hi : ByteAuthority.Active ctx.block ctx.candidate ctx.histories state)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories state.coupled.done node)
    (hs : ByteAuthority.Footprint.Sound ctx.candidate node demands) (hc : ByteAuthority.Footprint.Covers ctx.candidate node demands)
    (hd : ByteAuthority.Footprint.Distinct demands) (ha : ByteAuthority.Footprint.Available state demands) :
    adequate .NotStuck (script ctx (cycleActions node demands)) state
      (fun value _ => value = .ok (ByteAuthority.retired (ByteAuthority.Footprint.granted state node demands) node)) := by
  apply heap_adequacy
  intro _
  iintro Hall
  ihave Hparts := allPoints_control_free state demands hd ha $$ Hall
  icases Hparts with ⟨Hcontrol,Hfree⟩
  ihave Hwp := cycle_wp ctx state node demands iprop(True) hp hi hr hs hc hd ha $$ [$Hcontrol $Hfree]
  iapply wp_mono ?_ $$ Hwp
  intro value
  iintro ⟨%hv,Hcontrol,Hfree,Hframe⟩
  ipureintro; exact hv

end
end Ptx.ByteAuthorityHeap
