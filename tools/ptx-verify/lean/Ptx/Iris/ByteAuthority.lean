import Ptx.Hopper.ByteFootprint
import Ptx.Hopper.ByteProtocol
import Ptx.Iris.Execution

/-! Iris active byte-access authority over actual location keys. Values are
authority states, not GPU memory contents. Claim WP consumes full authority
for exactly one physical-location key plus the source/control fragment; other
byte fragments can be framed. Opaque resource bytes share the same key space.
-/
namespace Ptx.ByteAuthorityHeap
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language
open Iris.ProgramLogic.Language.Notation
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

abbrev State := ByteAuthority.State
abbrev HeapF := ByteAuthority.HeapF
local instance : Iris.Std.LawfulPartialMap HeapF Nat :=
  (inferInstance : Iris.Std.LawfulFiniteMap HeapF Nat).toLawfulPartialMap
local instance : Iris.Std.PartialMap HeapF Nat :=
  (inferInstance : Iris.Std.LawfulFiniteMap HeapF Nat).toLawfulPartialMap.toPartialMap

inductive Cell
  | control (state : State)
  | byte (owner : ByteAuthority.Owner)

def store (state : State) : HeapF Cell :=
  insert (Iris.Std.PartialMap.map Cell.byte state.bytes) ByteAuthority.controlKey (.control state)

@[simp] theorem store_control (state : State) : get? (store state) ByteAuthority.controlKey = some (.control state) := by
  simp [store,get?_insert]

@[simp] theorem store_byte (state : State) (loc : Location) :
    get? (store state) (ByteAuthority.key loc) = (get? state.bytes (ByteAuthority.key loc)).map Cell.byte := by
  simp [store,get?_insert_ne (Ne.symm (ByteAuthority.byte_key_not_control loc)),get?_map]

theorem store_set_byte (state : State) (loc : Location) (owner : ByteAuthority.Owner) :
    store {state with bytes := insert state.bytes (ByteAuthority.key loc) owner} =
      insert (insert (store state) (ByteAuthority.key loc) (.byte owner)) ByteAuthority.controlKey
        (.control {state with bytes := insert state.bytes (ByteAuthority.key loc) owner}) := by
  apply equiv_iff_eq.mp
  intro k
  by_cases hz : ByteAuthority.controlKey = k
  · subst k
    simp [store,get?_insert,ByteAuthority.byte_key_not_control loc]
  · by_cases hb : ByteAuthority.key loc = k
    · subst k
      simp [store,get?_insert,get?_map,Ne.symm (ByteAuthority.byte_key_not_control loc)]
    · simp [store,get?_insert_ne hz,get?_insert_ne hb,get?_map]

structure Context where
  block : Dim3
  candidate : Unified.Candidate
  histories : Location → List Tma.Entry
  cluster : Access.ClusterScope := fun _ _ => False
  plan : Bridge.Plan := fun _ => none

inductive Action
  | claim (request : ByteAuthority.Claim)
  | finish (node : Unified.ControlNode) (demands : List ByteAuthority.Footprint.Demand)
  | protocol (command : Bridge.Command)

def transition (ctx : Context) : Action → State → Except ByteAuthority.Error State
  | .claim request => ByteAuthority.claim ctx.block ctx.candidate ctx.histories request
  | .finish node demands => ByteAuthority.Footprint.finish ctx.block ctx.candidate ctx.histories node demands
  | .protocol command => ByteAuthority.executeCommand ctx.candidate ctx.histories ctx.cluster ctx.plan command
abbrev Expr (ctx : Context) := IrisExecution.Expr (transition ctx)
abbrev invoke (ctx : Context) (request : ByteAuthority.Claim) : Expr ctx := IrisExecution.Expr.invoke (.claim request)
abbrev finishInvoke (ctx : Context) (node : Unified.ControlNode) (demands : List ByteAuthority.Footprint.Demand) : Expr ctx :=
  IrisExecution.Expr.invoke (.finish node demands)

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

def byte [GS] (loc : Location) (dq : DFrac) (owner : ByteAuthority.Owner) : IProp GF :=
  pointsTo (ByteAuthority.key loc) dq (.byte owner)
def control [GS] (state : State) : IProp GF :=
  pointsTo ByteAuthority.controlKey (.own 1) (.control state)

theorem byte_full_exclusive [GS] (loc : Location) (a b : ByteAuthority.Owner) :
    byte loc (.own 1) a ∗ byte loc (.own 1) b ⊢ False := by
  unfold byte
  iintro ⟨Ha,Hb⟩
  ihave %hne := pointsTo_ne $$ Ha Hb
  ipureintro; exact hne rfl

theorem byte_split [GS] (loc : Location) (q : Qp) (owner : ByteAuthority.Owner) :
    byte loc (.own q) owner ⊣⊢ byte loc (.own q.half) owner ∗ byte loc (.own q.half) owner := by
  unfold byte
  have hs := (Iris.instFractionalPointsTo (GF := GF) (l := ByteAuthority.key loc) (v := Cell.byte owner)).fractional q.half q.half
  simpa only [Qp.half_add_half] using hs

theorem control_valid [GS] (actual expected : State) :
    genHeapInterp (store actual) ∗ control expected ==∗ ⌜actual = expected⌝ := by
  unfold control
  iintro H
  imod genHeap_valid $$ H with %h
  ipureintro
  have heq : Cell.control actual = Cell.control expected := Option.some.inj ((store_control actual).symm.trans h)
  exact Cell.control.inj heq

theorem byte_valid [GS] (state : State) (loc : Location) (dq : DFrac) (owner : ByteAuthority.Owner) :
    genHeapInterp (store state) ∗ byte loc dq owner ==∗ ⌜get? state.bytes (ByteAuthority.key loc) = some owner⌝ := by
  unfold byte
  iintro H
  imod genHeap_valid $$ H with %h
  ipureintro
  rw [store_byte] at h
  cases hg : get? state.bytes (ByteAuthority.key loc) with
  | none => simp [hg] at h
  | some actual =>
    have heq : Cell.byte actual = Cell.byte owner := by simpa only [hg,Option.map_some,Option.some.injEq] using h
    rw [Cell.byte.inj heq]

/-- Only the control fragment and this actual byte's full authority are used.
The rule's interpreter checks the real source use and readiness at that cut. -/
theorem claim_local_wp [g : GS] (ctx : Context) (expected : State) (request : ByteAuthority.Claim)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories expected.coupled.done request.node)
    (hu : ByteAuthority.Uses ctx.candidate request.node request.location request.mode) :
    control expected ∗ byte request.location (.own 1) .available ⊢ WP (invoke ctx request)
      {{ value, ⌜∃ next, value = .ok next⌝ ∗ control {expected with bytes := insert expected.bytes (ByteAuthority.key request.location) (.held request.node request.mode)} ∗ byte request.location (.own 1) (.held request.node request.mode) }} := by
  let _ := g.inv
  iintro ⟨Hcontrol,Hbyte⟩
  iapply wp_lift_atomic_step (show toVal (invoke ctx request) = none from rfl)
  isimp [stateInterp]
  iintro %state %ns %obs %obs' %nt Hheap
  ihave %hcontrol : ⌜state = expected⌝ $$ [Hheap Hcontrol]
  · imod control_valid state expected $$ [$Hheap $Hcontrol] with %h
    ipureintro; exact h
  subst state
  ihave %hbyte : ⌜get? expected.bytes (ByteAuthority.key request.location) = some .available⌝ $$ [Hheap Hbyte]
  · imod byte_valid expected request.location (.own 1) .available $$ [$Hheap $Hbyte] with %h
    ipureintro; exact h
  let next : State := {expected with bytes := insert expected.bytes (ByteAuthority.key request.location) (.held request.node request.mode)}
  have hs : transition ctx (.claim request) expected = .ok next :=
    ByteAuthority.claim_succeeds hr hu hbyte
  imodintro
  isplit
  · ipureintro
    exact ⟨[],IrisExecution.Expr.result (.ok next),next,[],IrisExecution.Prim.success hs⟩
  inext
  iintro %e' %actual %forks %hp Hcredit
  obtain ⟨hstate,hval,hfork⟩ := IrisExecution.prim_deterministic hs hp
  simp only [IrisExecution.after] at hstate
  subst actual forks
  unfold byte control
  imod genHeap_update (v₂ := Cell.byte (.held request.node request.mode)) $$ [$Hheap $Hbyte] with ⟨Hheap,Hbyte⟩
  imod genHeap_update (v₂ := Cell.control next) $$ [$Hheap $Hcontrol] with ⟨Hheap,Hcontrol⟩
  rw [← store_set_byte]
  imodintro
  simp only [Iris.Algebra.BigOpL.bigOpL_nil]
  isplitl [Hheap]
  · iexact Hheap
  · isplitl [Hcontrol Hbyte]
    · iexists (.ok next)
      isplit
      · ipureintro; exact hval
      · isplit
        · ipureintro; exact ⟨next,rfl⟩
        · isplitl [Hcontrol]
          · iexact Hcontrol
          · iexact Hbyte
    · itrivial

def allPoints [GS] (state : State) : IProp GF :=
  iprop([∗map] k ↦ value ∈ store state, pointsTo k (.own 1) value)

theorem allPoints_control_byte [GS] {state : State} {loc : Location} {owner : ByteAuthority.Owner}
    (hb : get? state.bytes (ByteAuthority.key loc) = some owner) :
    allPoints state ⊢ control state ∗ byte loc (.own 1) owner := by
  unfold allPoints control byte
  iintro Hall
  icases (BigSepM.bigSepM_delete (store_control state)) $$ Hall with ⟨Hcontrol,Hrest⟩
  have hh : get? (Iris.Std.PartialMap.delete (store state) ByteAuthority.controlKey) (ByteAuthority.key loc) = some (.byte owner) := by
    rw [get?_delete_ne (Ne.symm (ByteAuthority.byte_key_not_control loc)),store_byte,hb]
    rfl
  ihave Hbyte := BigSepM.bigSepM_lookup hh $$ Hrest
  iframe Hcontrol Hbyte

/-- Closed initialization allocates authority for the actual supplied map.
No freely chosen GS/heap realization premise is exported by adequacy. -/
theorem heap_adequacy (ctx : Context) (state : State) (e : Expr ctx)
    (post : Except ByteAuthority.Error State → Prop)
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

theorem claim_adequate (ctx : Context) (state : State) (request : ByteAuthority.Claim)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories state.coupled.done request.node)
    (hu : ByteAuthority.Uses ctx.candidate request.node request.location request.mode)
    (hb : get? state.bytes (ByteAuthority.key request.location) = some .available) :
    adequate .NotStuck (invoke ctx request) state (fun result _ => ∃ next, result = .ok next) := by
  apply heap_adequacy
  intro _
  iintro Hall
  ihave Hparts := allPoints_control_byte hb $$ Hall
  ihave Hwp := claim_local_wp ctx state request hr hu $$ Hparts
  iapply wp_mono ?_ $$ Hwp
  intro value
  iintro ⟨%hv,Hcontrol,Hbyte⟩
  ipureintro; exact hv

end
end Ptx.ByteAuthorityHeap
