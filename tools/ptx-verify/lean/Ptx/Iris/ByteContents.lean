import Ptx.Hopper.ByteContents
import Ptx.Hopper.ByteContentsControl
import Ptx.Iris.Execution

/-! Native GenHeap cells contain both source authority and actual modeled
symbolic byte contents. Symbolic real fragments retain their existing abstraction;
this does not provide IEEE bit reinterpretation or a CUDA physical simulation.
-/
namespace Ptx.ByteContentsHeap
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language
open Iris.ProgramLogic.Language.Notation
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

abbrev State := ByteContents.State
abbrev Payload := ByteContents.Payload
abbrev HeapF := ByteAuthority.HeapF
local instance : Iris.Std.LawfulPartialMap HeapF Nat :=
  (inferInstance : Iris.Std.LawfulFiniteMap HeapF Nat).toLawfulPartialMap
local instance : Iris.Std.PartialMap HeapF Nat :=
  (inferInstance : Iris.Std.LawfulFiniteMap HeapF Nat).toLawfulPartialMap.toPartialMap

inductive Cell
  | control (state : State)
  | byte (payload : Payload)
def store (state : State) : HeapF Cell :=
  insert (Iris.Std.PartialMap.map Cell.byte state.cells) ByteAuthority.controlKey (.control state)

@[simp] theorem store_control (state : State) : get? (store state) ByteAuthority.controlKey = some (.control state) := by
  simp [store,get?_insert]
@[simp] theorem store_byte (state : State) (loc : Location) :
    get? (store state) (ByteAuthority.key loc) = (get? state.cells (ByteAuthority.key loc)).map Cell.byte := by
  simp [store,get?_insert_ne (Ne.symm (ByteAuthority.byte_key_not_control loc)),get?_map]

structure Context where
  block : Dim3
  candidate : Unified.Candidate
  histories : Location → List Tma.Entry
inductive Action
  | claim (request : ByteAuthority.Claim)
  | control (node : Unified.ControlNode)
  | finish (node : Unified.Node) (demands : List ByteAuthority.Footprint.Demand)
def transition (ctx : Context) : Action → State → Except ByteContents.Error State
  | .claim request => ByteContents.claim ctx.block ctx.candidate ctx.histories request
  | .control node => ByteContents.finishControl ctx.block ctx.candidate ctx.histories node
  | .finish node demands => ByteContents.finish ctx.block ctx.candidate ctx.histories node demands
abbrev Expr (ctx : Context) := IrisExecution.Expr (transition ctx)
abbrev script (ctx : Context) (actions : List Action) : Expr ctx := IrisExecution.Expr.script actions

open COFE Auth Std.LawfulSet
noncomputable def GF : BundledGFunctors := fun n =>
  match n with
  | 0 => ⟨InvMapF⟩
  | 1 => ⟨constOF CoPsetDisjL⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet)⟩
  | 3 => ⟨AuthURF (constOF Credit)⟩
  | 4 => ⟨constOF (HeapView Nat (Agree (DiscreteO Cell)) HeapF)⟩
  | 5 => ⟨constOF (HeapView Nat (Agree (DiscreteO GName)) HeapF)⟩
  | 6 => ⟨constOF MetaUR⟩
  | _ => ⟨constOF Unit⟩

instance : WsatGpreS GF where
  inv := {τ := 0,transp := by unfold GF; rfl}
  enabled := {τ := 1,transp := by unfold GF; rfl}
  disabled := {τ := 2,transp := by unfold GF; rfl}
instance : LcGpreS GF where
  lc_elem := {τ := 3,transp := by unfold GF; rfl}
instance : InvGpreS GF where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance
instance : genHeapPreS Nat Cell GF HeapF where
  heap := ⟨⟨4,by unfold GF; rfl⟩⟩
  metaInfo := ⟨⟨5,by unfold GF; rfl⟩⟩
  metaData := ⟨6,by unfold GF; rfl⟩

class GS where
  inv : InvGS GF
  heap : genHeapGS Nat Cell GF HeapF
attribute [reducible, instance] GS.heap

instance [GS] : StateInterp State Unit GF where
  stateInterp state _ _ _ := genHeapInterp (store state)

instance [g : GS] (ctx : Context) : IrisGS_gen .hasLC (Expr ctx) GF where
  invGS := g.inv
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := letI := g.inv; fupd_intro

local bi (IProp GF)

def byte [GS] (loc : Location) (dq : DFrac) (payload : Payload) : IProp GF :=
  pointsTo (ByteAuthority.key loc) dq (.byte payload)
def control [GS] (state : State) : IProp GF := pointsTo ByteAuthority.controlKey (.own 1) (.control state)
def allPoints [GS] (state : State) : IProp GF :=
  iprop([∗map] k ↦ value ∈ store state, pointsTo k (.own 1) value)

theorem control_valid [GS] (actual expected : State) :
    genHeapInterp (store actual) ∗ control expected ==∗ ⌜actual = expected⌝ := by
  unfold control
  iintro H
  imod genHeap_valid $$ H with %h
  ipureintro
  exact Cell.control.inj (Option.some.inj ((store_control actual).symm.trans h))

theorem byte_valid [GS] (state : State) (loc : Location) (dq : DFrac) (payload : Payload) :
    genHeapInterp (store state) ∗ byte loc dq payload ==∗ ⌜get? state.cells (ByteAuthority.key loc) = some payload⌝ := by
  unfold byte
  iintro H
  imod genHeap_valid $$ H with %h
  ipureintro
  rw [store_byte] at h
  cases hg : get? state.cells (ByteAuthority.key loc) with
  | none => simp [hg] at h
  | some actual =>
    have he : Cell.byte actual = Cell.byte payload := by simpa only [hg,Option.map_some,Option.some.injEq] using h
    rw [Cell.byte.inj he]

theorem step_script_wp [g : GS] (ctx : Context) (state next : State) (action : Action) (tail : List Action)
    (before after : IProp GF) (post : Except ByteContents.Error State → IProp GF)
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

theorem heap_adequacy (ctx : Context) (state : State) (e : Expr ctx)
    (post : Except ByteContents.Error State → Prop)
    (hwp : ∀ [GS], allPoints state ⊢ WP e {{ result, ⌜post result⌝ }}) :
    adequate .NotStuck e state (fun result _ => post result) := by
  apply wp_adequacy (GF := GF) .NotStuck e state post
  intro inv obs
  imod genHeap_init (GF := GF) (H := HeapF) (store state) with ⟨%heap,Hinterp,Hpts,_⟩
  let _ : GS := ⟨inv,heap⟩
  imodintro
  iexists (fun state (_ : List Unit) => genHeapInterp (store state)), (fun _ => iprop(True))
  isplitl [Hinterp]
  · iexact Hinterp
  · ihave Hinitial : allPoints state $$ [Hpts]
    · unfold allPoints
      iexact Hpts
    ihave Hwp := (@hwp _) $$ Hinitial
    iexact Hwp

theorem store_domain {before after : State} (hd : dom before.cells = dom after.cells) : dom (store before) = dom (store after) := by
  funext k
  by_cases hz : ByteAuthority.controlKey = k
  · subst k; simp [dom,store,get?_insert]
  · simpa only [dom,store,get?_insert_ne hz,get?_map,Option.isSome_map] using congrFun hd k

theorem store_union {before after : State} (hd : dom before.cells = dom after.cells) :
    Iris.Std.PartialMap.union (store after) (store before) = store after := by
  apply equiv_iff_eq.mp
  intro k
  simp only [Iris.Std.PartialMap.union,get?_merge]
  cases ha : get? (store after) k with
  | some payload => cases get? (store before) k <;> simp [Option.merge]
  | none =>
    have hb : get? (store before) k = none := by
      cases hb : get? (store before) k with
      | none => rfl
      | some payload =>
        have hmem : dom (store before) k := by simp [dom,hb]
        rw [store_domain hd] at hmem
        simp [dom,ha] at hmem
    simp [hb,Option.merge]

theorem allPoints_update [g : GS] (before after : State) (hd : dom before.cells = dom after.cells) :
    genHeapInterp (store before) ∗ allPoints before ==∗ genHeapInterp (store after) ∗ allPoints after := by
  letI : genHeapPreS Nat Cell GF HeapF := g.heap.togenHeapPreS
  unfold genHeapInterp allPoints pointsTo
  iintro ⟨⟨%metadata,%hdom,Hauth,Hmeta⟩,Hpts⟩
  imod ghost_map_update_big (store before) (store after) (store_domain hd) $$ Hauth Hpts with ⟨Hauth,Hpts⟩
  isimp only [Union.union] at Hauth
  isimp only [store_union hd] at Hauth
  imodintro
  iframe Hpts
  iexists metadata
  iframe Hauth Hmeta
  ipureintro
  intro k hk
  rw [← store_domain hd]
  exact hdom k hk

theorem allPoints_control [GS] (state : State) : allPoints state ⊢ control state := by
  unfold allPoints control
  exact BigSepM.bigSepM_lookup (store_control state)

theorem action_domain (ctx : Context) {action state next} (hs : transition ctx action state = .ok next) :
    dom state.cells = dom next.cells := by
  cases action with
  | claim request => exact (ByteContents.claim_domain hs).symm
  | control node => rw [ByteContents.finishControl_preserves_cells hs]
  | finish node demands => exact (ByteContents.finish_domain hs).symm

theorem step_all_cps [g : GS] (ctx : Context) (state next : State) (action : Action) (tail : List Action)
    (frame : IProp GF) (post : Except ByteContents.Error State → IProp GF)
    (hs : transition ctx action state = .ok next)
    (hcont : allPoints next ∗ frame ⊢ WP (script ctx tail) {{ value, post value }}) :
    allPoints state ∗ frame ⊢ WP (script ctx (action::tail)) {{ value, post value }} := by
  let _ := g.inv
  iintro ⟨Hall,Hframe⟩
  iapply wp_lift_step (show toVal (script ctx (action::tail)) = none from rfl)
  isimp [stateInterp]
  iintro %actual %ns %obs %obs' %nt Hheap
  ihave %heq : ⌜actual = state⌝ $$ [Hheap Hall]
  · ihave Hcontrol := allPoints_control state $$ Hall
    imod control_valid actual state $$ [$Hheap $Hcontrol] with %h
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
    have he := Except.ok.inj (hs.symm.trans hnext)
    subst actual
    imod allPoints_update state next (action_domain ctx hs) $$ [$Hheap $Hall] with ⟨Hheap,Hall⟩
    imod Hclose
    imodintro
    simp only [Iris.Algebra.BigOpL.bigOpL_nil]
    isplitl [Hheap]
    · iexact Hheap
    · isplitl [Hall Hframe]
      · iapply hcont $$ [$Hall $Hframe]
      · itrivial
  | abort herr => cases hs.symm.trans herr

theorem script_nil_all_wp [g : GS] (ctx : Context) (state : State) (frame : IProp GF) :
    allPoints state ∗ frame ⊢ WP (script ctx []) {{ value, ⌜value = .ok state⌝ ∗ allPoints state ∗ frame }} := by
  let _ := g.inv
  iintro ⟨Hall,Hframe⟩
  iapply wp_lift_atomic_step (show toVal (script ctx []) = none from rfl)
  isimp [stateInterp]
  iintro %actual %ns %obs %obs' %nt Hheap
  ihave %heq : ⌜actual = state⌝ $$ [Hheap Hall]
  · ihave Hcontrol := allPoints_control state $$ Hall
    imod control_valid actual state $$ [$Hheap $Hcontrol] with %h
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
  · isplitl [Hall Hframe]
    · iexists (.ok state)
      isplit
      · ipureintro; rfl
      · isplit
        · ipureintro; rfl
        · iframe Hall Hframe
    · itrivial

theorem script_cps [GS] (ctx : Context) (actions tail : List Action) (state final : State)
    (frame : IProp GF) (post : Except ByteContents.Error State → IProp GF)
    (hr : IrisExecution.run (transition ctx) actions state = .ok final)
    (hcont : allPoints final ∗ frame ⊢ WP (script ctx tail) {{ value, post value }}) :
    allPoints state ∗ frame ⊢ WP (script ctx (actions ++ tail)) {{ value, post value }} := by
  induction actions generalizing state with
  | nil => cases hr; exact hcont
  | cons head rest ih =>
    change (transition ctx head state).bind (fun mid => IrisExecution.run (transition ctx) rest mid) = .ok final at hr
    cases hs : transition ctx head state with
    | error error => simp [hs,Except.bind] at hr
    | ok mid =>
      apply step_all_cps ctx state mid head (rest ++ tail) frame post hs
      exact ih mid (by simpa only [hs,Except.bind] using hr)

theorem script_wp [GS] (ctx : Context) (actions : List Action) (state final : State)
    (frame : IProp GF) (hr : IrisExecution.run (transition ctx) actions state = .ok final) :
    allPoints state ∗ frame ⊢ WP (script ctx actions) {{ value, ⌜value = .ok final⌝ ∗ allPoints final ∗ frame }} := by
  have hw := script_cps ctx actions [] state final frame _ hr (script_nil_all_wp ctx final frame)
  simpa only [List.append_nil] using hw

theorem script_adequate (ctx : Context) (actions : List Action) (state final : State)
    (hr : IrisExecution.run (transition ctx) actions state = .ok final) :
    adequate .NotStuck (script ctx actions) state (fun value _ => value = .ok final) := by
  apply heap_adequacy
  intro _
  iintro Hall
  ihave Hwp := script_wp ctx actions state final iprop(True) hr $$ [$Hall]
  iapply wp_mono ?_ $$ Hwp
  intro value
  iintro ⟨%hv,Hall,Hframe⟩
  ipureintro; exact hv

theorem action_projects (ctx : Context) {action state next cluster plan}
    (hs : transition ctx action state = .ok next) :
    ByteAuthority.Step ctx.block ctx.candidate ctx.histories cluster plan (ByteContents.erase state) (ByteContents.erase next) := by
  cases action with
  | claim request => exact .claim (ByteContents.claim_spec hs).choose_spec.2.2.2
  | control node => exact ByteContents.finishControl_projects hs
  | finish node demands => exact ByteContents.finish_projects hs

theorem run_projects (ctx : Context) (actions : List Action) {state next cluster plan}
    (hr : IrisExecution.run (transition ctx) actions state = .ok next) :
    ByteAuthority.Steps ctx.block ctx.candidate ctx.histories cluster plan (ByteContents.erase state) (ByteContents.erase next) := by
  induction actions generalizing state with
  | nil => cases hr; exact .refl _
  | cons head rest ih =>
    change (transition ctx head state).bind (fun mid => IrisExecution.run (transition ctx) rest mid) = .ok next at hr
    cases hs : transition ctx head state with
    | error error => simp [hs,Except.bind] at hr
    | ok mid => exact .next (action_projects ctx hs) (ih (by simpa only [hs,Except.bind] using hr))

theorem byte_agree [GS] (loc : Location) (dq dr : DFrac) (a b : Payload) :
    byte loc dq a ∗ byte loc dr b ⊢ ⌜a = b⌝ := by
  unfold byte
  iintro H
  ihave %he := pointsTo_agree $$ H
  ipureintro; exact Cell.byte.inj he

theorem byte_full_exclusive [GS] (loc : Location) (a b : Payload) :
    byte loc (.own 1) a ∗ byte loc (.own 1) b ⊢ False := by
  unfold byte
  iintro ⟨Ha,Hb⟩
  ihave %hne := pointsTo_ne $$ Ha Hb
  ipureintro; exact hne rfl

theorem allPoints_byte [GS] (state : State) (loc : Location) (payload : Payload)
    (hg : get? state.cells (ByteAuthority.key loc) = some payload) : allPoints state ⊢ byte loc (.own 1) payload := by
  unfold allPoints byte
  apply BigSepM.bigSepM_lookup
  rw [store_byte,hg]
  rfl

theorem store_set_cell (state : State) (loc : Location) (payload : Payload) :
    store {state with cells := insert state.cells (ByteAuthority.key loc) payload} =
      insert (insert (store state) (ByteAuthority.key loc) (.byte payload)) ByteAuthority.controlKey
        (.control {state with cells := insert state.cells (ByteAuthority.key loc) payload}) := by
  apply equiv_iff_eq.mp
  intro k
  by_cases hz : ByteAuthority.controlKey = k
  · subst k; simp [store,get?_insert,ByteAuthority.byte_key_not_control loc]
  · by_cases hl : ByteAuthority.key loc = k
    · subst k; simp [store,get?_insert,get?_map,Ne.symm (ByteAuthority.byte_key_not_control loc)]
    · simp [store,get?_insert_ne hz,get?_insert_ne hl,get?_map]

theorem claim_update_local [GS] (state : State) (request : ByteAuthority.Claim) (old : Payload) :
    genHeapInterp (store state) ∗ control state ∗ byte request.location (.own 1) old ==∗
      genHeapInterp (store (ByteContents.claimed state request old)) ∗ control (ByteContents.claimed state request old) ∗
        byte request.location (.own 1) ⟨.held request.node request.mode,old.value⟩ := by
  unfold control byte
  iintro ⟨Hheap,Hcontrol,Hbyte⟩
  imod genHeap_update (v₂ := Cell.byte ⟨.held request.node request.mode,old.value⟩) $$ [$Hheap $Hbyte] with ⟨Hheap,Hbyte⟩
  imod genHeap_update (v₂ := Cell.control (ByteContents.claimed state request old)) $$ [$Hheap $Hcontrol] with ⟨Hheap,Hcontrol⟩
  have he : store (ByteContents.claimed state request old) =
      insert (insert (store state) (ByteAuthority.key request.location) (.byte ⟨.held request.node request.mode,old.value⟩))
        ByteAuthority.controlKey (.control (ByteContents.claimed state request old)) :=
    store_set_cell state request.location ⟨.held request.node request.mode,old.value⟩
  rw [← he]
  imodintro
  iframe Hheap Hcontrol Hbyte

theorem claim_local_cps [GS] (ctx : Context) (state : State) (request : ByteAuthority.Claim) (value : Option Symbolic.Byte)
    (tail : List Action) (frame : IProp GF) (post : Except ByteContents.Error State → IProp GF)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories state.coupled.done request.node)
    (hu : ByteAuthority.Uses ctx.candidate request.node request.location request.mode)
    (hg : get? state.cells (ByteAuthority.key request.location) = some ⟨.available,value⟩)
    (hcont : control (ByteContents.claimed state request ⟨.available,value⟩) ∗
      byte request.location (.own 1) ⟨.held request.node request.mode,value⟩ ∗ frame ⊢
      WP (script ctx tail) {{ result, post result }}) :
    control state ∗ byte request.location (.own 1) ⟨.available,value⟩ ∗ frame ⊢
      WP (script ctx (.claim request::tail)) {{ result, post result }} := by
  apply step_script_wp ctx state (ByteContents.claimed state request ⟨.available,value⟩) (.claim request) tail
    iprop(byte request.location (.own 1) ⟨.available,value⟩ ∗ frame)
    iprop(byte request.location (.own 1) ⟨.held request.node request.mode,value⟩ ∗ frame) post
    (ByteContents.claim_succeeds hr hu hg) ?_ hcont
  iintro ⟨Hheap,Hcontrol,Hbyte,Hframe⟩
  imod claim_update_local state request ⟨.available,value⟩ $$ [$Hheap $Hcontrol $Hbyte] with ⟨Hheap,Hcontrol,Hbyte⟩
  imodintro
  iframe Hheap Hcontrol Hbyte Hframe

end
end Ptx.ByteContentsHeap
