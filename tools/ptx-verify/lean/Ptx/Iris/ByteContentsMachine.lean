import Ptx.Iris.ByteContents

/-! The existing native symbolic-byte heap interpretation for a fixed supplied
transition. Successful actions must preserve the allocated cell domain. The
whole-map update remains the baseline; source and protocol soundness are proved
separately for each transition. No new execution or memory assumptions are added.
-/
namespace Ptx.ByteContentsMachine
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.ByteContentsHeap
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language
open Iris.ProgramLogic.Language.Notation
open COFE Auth Std.LawfulSet
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section
variable {Action : Type}

abbrev State := ByteContents.State
abbrev Expr (step : Action → State → Except ByteContents.Error State) := IrisExecution.Expr step
abbrev script (step : Action → State → Except ByteContents.Error State) (actions : List Action) : Expr step := IrisExecution.Expr.script actions

instance [g : GS] (step : Action → State → Except ByteContents.Error State) : IrisGS_gen .hasLC (Expr step) GF where
  invGS := g.inv
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := letI := g.inv; fupd_intro

local bi (IProp GF)

theorem step_script_wp [g : GS] (step : Action → State → Except ByteContents.Error State) (state next : State) (action : Action) (tail : List Action)
    (before after : IProp GF) (post : Except ByteContents.Error State → IProp GF)
    (hs : step action state = .ok next)
    (hupdate : genHeapInterp (store state) ∗ control state ∗ before ==∗ genHeapInterp (store next) ∗ control next ∗ after)
    (hcont : control next ∗ after ⊢ WP (script step tail) {{ value, post value }}) :
    control state ∗ before ⊢ WP (script step (action::tail)) {{ value, post value }} := by
  let _ := g.inv
  iintro ⟨Hcontrol,Hbefore⟩
  iapply wp_lift_step (show toVal (script step (action::tail)) = none from rfl)
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
  change IrisExecution.Prim step (.script (action::tail),state) obs (e',actual,forks) at hp
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

theorem script_nil_wp [g : GS] (step : Action → State → Except ByteContents.Error State) (state : State) (frame : IProp GF) :
    control state ∗ frame ⊢ WP (script step []) {{ value, ⌜value = .ok state⌝ ∗ control state ∗ frame }} := by
  let _ := g.inv
  iintro ⟨Hcontrol,Hframe⟩
  iapply wp_lift_atomic_step (show toVal (script step []) = none from rfl)
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
  change IrisExecution.Prim step (.script [],state) obs (e',actual,forks) at hp
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

theorem heap_adequacy (step : Action → State → Except ByteContents.Error State) (state : State) (e : Expr step)
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


theorem step_all_cps [g : GS] (step : Action → State → Except ByteContents.Error State) (state next : State) (action : Action) (tail : List Action)
    (frame : IProp GF) (post : Except ByteContents.Error State → IProp GF)
    (hs : step action state = .ok next)
    (hd : Iris.Std.PartialMap.dom state.cells = Iris.Std.PartialMap.dom next.cells)
    (hcont : allPoints next ∗ frame ⊢ WP (script step tail) {{ value, post value }}) :
    allPoints state ∗ frame ⊢ WP (script step (action::tail)) {{ value, post value }} := by
  let _ := g.inv
  iintro ⟨Hall,Hframe⟩
  iapply wp_lift_step (show toVal (script step (action::tail)) = none from rfl)
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
  change IrisExecution.Prim step (.script (action::tail),state) obs (e',actual,forks) at hp
  cases hp with
  | next hnext =>
    have he := Except.ok.inj (hs.symm.trans hnext)
    subst actual
    imod allPoints_update state next hd $$ [$Hheap $Hall] with ⟨Hheap,Hall⟩
    imod Hclose
    imodintro
    simp only [Iris.Algebra.BigOpL.bigOpL_nil]
    isplitl [Hheap]
    · iexact Hheap
    · isplitl [Hall Hframe]
      · iapply hcont $$ [$Hall $Hframe]
      · itrivial
  | abort herr => cases hs.symm.trans herr

theorem script_nil_all_wp [g : GS] (step : Action → State → Except ByteContents.Error State) (state : State) (frame : IProp GF) :
    allPoints state ∗ frame ⊢ WP (script step []) {{ value, ⌜value = .ok state⌝ ∗ allPoints state ∗ frame }} := by
  let _ := g.inv
  iintro ⟨Hall,Hframe⟩
  iapply wp_lift_atomic_step (show toVal (script step []) = none from rfl)
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
  change IrisExecution.Prim step (.script [],state) obs (e',actual,forks) at hp
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

theorem script_cps [GS] (step : Action → State → Except ByteContents.Error State) (actions tail : List Action) (state final : State)
    (frame : IProp GF) (post : Except ByteContents.Error State → IProp GF)
    (hd : ∀ action state next, step action state = .ok next → Iris.Std.PartialMap.dom state.cells = Iris.Std.PartialMap.dom next.cells)
    (hr : IrisExecution.run step actions state = .ok final)
    (hcont : allPoints final ∗ frame ⊢ WP (script step tail) {{ value, post value }}) :
    allPoints state ∗ frame ⊢ WP (script step (actions ++ tail)) {{ value, post value }} := by
  induction actions generalizing state with
  | nil => cases hr; exact hcont
  | cons head rest ih =>
    change (step head state).bind (fun mid => IrisExecution.run step rest mid) = .ok final at hr
    cases hs : step head state with
    | error error => simp [hs,Except.bind] at hr
    | ok mid =>
      apply step_all_cps step state mid head (rest ++ tail) frame post hs (hd _ _ _ hs)
      exact ih mid (by simpa only [hs,Except.bind] using hr)

theorem script_wp [GS] (step : Action → State → Except ByteContents.Error State) (actions : List Action) (state final : State)
    (frame : IProp GF)
    (hd : ∀ action state next, step action state = .ok next → Iris.Std.PartialMap.dom state.cells = Iris.Std.PartialMap.dom next.cells)
    (hr : IrisExecution.run step actions state = .ok final) :
    allPoints state ∗ frame ⊢ WP (script step actions) {{ value, ⌜value = .ok final⌝ ∗ allPoints final ∗ frame }} := by
  have hw := script_cps step actions [] state final frame _ hd hr (script_nil_all_wp step final frame)
  simpa only [List.append_nil] using hw

theorem script_adequate (step : Action → State → Except ByteContents.Error State) (actions : List Action) (state final : State)
    (hd : ∀ action state next, step action state = .ok next → Iris.Std.PartialMap.dom state.cells = Iris.Std.PartialMap.dom next.cells)
    (hr : IrisExecution.run step actions state = .ok final) :
    adequate .NotStuck (script step actions) state (fun value _ => value = .ok final) := by
  apply heap_adequacy step
  intro _
  iintro Hall
  ihave Hwp := script_wp step actions state final iprop(True) hd hr $$ [$Hall]
  iapply wp_mono ?_ $$ Hwp
  intro value
  iintro ⟨%hv,Hall,Hframe⟩
  ipureintro; exact hv

theorem script_reject_wp [g : GS] (step : Action → State → Except ByteContents.Error State) (state : State) (action : Action) (tail : List Action)
    (error : ByteContents.Error) (frame : IProp GF) (hs : step action state = .error error) :
    control state ∗ frame ⊢ WP (script step (action::tail))
      {{ value, ⌜value = .error error⌝ ∗ control state ∗ frame }} := by
  let _ := g.inv
  iintro ⟨Hcontrol,Hframe⟩
  iapply wp_lift_atomic_step (show toVal (script step (action::tail)) = none from rfl)
  isimp [stateInterp]
  iintro %actual %ns %obs %obs' %nt Hheap
  ihave %heq : ⌜actual = state⌝ $$ [Hheap Hcontrol]
  · imod control_valid actual state $$ [$Hheap $Hcontrol] with %h
    ipureintro; exact h
  subst actual
  imodintro
  isplit
  · ipureintro
    exact ⟨[],IrisExecution.Expr.result (.error error),state,[],IrisExecution.Prim.abort hs⟩
  inext
  iintro %e' %actual %forks %hp Hcredit
  change IrisExecution.Prim step (.script (action::tail),state) obs (e',actual,forks) at hp
  cases hp with
  | next hnext => cases hs.symm.trans hnext
  | abort herr =>
    have he : error = _ := Except.error.inj (hs.symm.trans herr)
    subst he
    imodintro
    simp only [Iris.Algebra.BigOpL.bigOpL_nil]
    isplitl [Hheap]
    · iexact Hheap
    · isplitl [Hcontrol Hframe]
      · iexists (.error error)
        isplit
        · ipureintro; rfl
        · isplit
          · ipureintro; rfl
          · iframe Hcontrol Hframe
      · itrivial

end
end Ptx.ByteContentsMachine
