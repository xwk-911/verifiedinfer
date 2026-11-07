import Ptx.Iris.ByteContents
import Ptx.Hopper.ByteContentsFrames

/-! Footprint-local value updates. Only the actual listed full cells and the
controller snapshot are consumed; all unrelated byte/value fragments frame.
One source memory event still checks every read before its indivisible update.
-/
namespace Ptx.ByteContentsHeap
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

abbrev Demand := ByteAuthority.Footprint.Demand

def Matches (state : State) (node : Unified.ControlNode) (demands : List Demand) (values : Location → Option Symbolic.Byte) : Prop :=
  ∀ demand ∈ demands, get? state.cells (ByteAuthority.key demand.location) = some ⟨.held node demand.mode,values demand.location⟩

def heldPoints [GS] (node : Unified.ControlNode) (demands : List Demand) (values : Location → Option Symbolic.Byte) : IProp GF :=
  iprop([∗list] demand ∈ demands, byte demand.location (.own 1) ⟨.held node demand.mode,values demand.location⟩)
def freePoints [GS] (demands : List Demand) (values : Location → Option Symbolic.Byte) : IProp GF :=
  iprop([∗list] demand ∈ demands, byte demand.location (.own 1) ⟨.available,values demand.location⟩)
def returnedValues (candidate : Unified.Candidate) (node : Unified.Node) (values : Location → Option Symbolic.Byte) : Location → Option Symbolic.Byte :=
  fun loc => (ByteContents.writeByte candidate node loc).or (values loc)

theorem matches_from_held {state node demands}
    (hh : ByteAuthority.Footprint.Held (ByteContents.erase state) node demands) :
    Matches state node demands (ByteContents.valueAt state) := by
  intro demand hm
  obtain ⟨value,hg⟩ := ByteContents.payload_of_held (hh demand hm)
  have hv : ByteContents.valueAt state demand.location = value := by rw [ByteContents.valueAt,hg]; rfl
  simpa only [hv] using hg

def releaseStore (candidate : Unified.Candidate) (node : Unified.Node) (values : Location → Option Symbolic.Byte) :
    List Demand → HeapF Cell → HeapF Cell
  | [],heap => heap
  | demand::rest,heap => insert (releaseStore candidate node values rest heap) (ByteAuthority.key demand.location)
      (.byte ⟨.available,returnedValues candidate node values demand.location⟩)

theorem releaseStore_member {candidate node values demands heap demand} (hm : demand ∈ demands) :
    get? (releaseStore candidate node values demands heap) (ByteAuthority.key demand.location) =
      some (.byte ⟨.available,returnedValues candidate node values demand.location⟩) := by
  induction demands with
  | nil => cases hm
  | cons head rest ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · simp [releaseStore,get?_insert]
    · by_cases he : ByteAuthority.key head.location = ByteAuthority.key demand.location
      · have hl := ByteAuthority.key_injective he
        simp only [releaseStore,get?_insert,he,ite_true,hl]
      · rw [releaseStore,get?_insert_ne he]
        exact ih hm

theorem releaseStore_outside (candidate : Unified.Candidate) (node : Unified.Node) (values : Location → Option Symbolic.Byte)
    (demands : List Demand) (heap : HeapF Cell) (k : Nat) (hn : k ∉ ByteAuthority.Footprint.keys demands) :
    get? (releaseStore candidate node values demands heap) k = get? heap k := by
  induction demands with
  | nil => rfl
  | cons head rest ih =>
    have he : ByteAuthority.key head.location ≠ k := by intro h; exact hn (by simp [ByteAuthority.Footprint.keys,h])
    rw [releaseStore,get?_insert_ne he]
    exact ih (fun hm => hn (List.mem_cons_of_mem _ hm))

theorem store_finished_footprint (state : State) (candidate : Unified.Candidate) (node : Unified.Node)
    (demands : List Demand) (values : Location → Option Symbolic.Byte)
    (hd : ByteAuthority.Footprint.Distinct demands) (hm : Matches state (Unified.memoryControlNode node) demands values) :
    store (ByteContents.finished candidate node demands state) =
      insert (releaseStore candidate node values demands (store state)) ByteAuthority.controlKey
        (.control (ByteContents.finished candidate node demands state)) := by
  apply equiv_iff_eq.mp
  intro k
  by_cases hz : ByteAuthority.controlKey = k
  · subst k; simp [store,get?_insert]
  · rw [get?_insert_ne hz]
    by_cases hk : k ∈ ByteAuthority.Footprint.keys demands
    · obtain ⟨demand,hmem,he⟩ := List.mem_map.mp hk
      subst k
      rw [store_byte]
      change (get? (ByteContents.finishCells candidate node demands state.cells) (ByteAuthority.key demand.location)).map Cell.byte = _
      rw [ByteContents.finishCells_member hd hmem (hm demand hmem),releaseStore_member hmem]
      rfl
    · rw [releaseStore_outside _ _ _ _ _ _ hk]
      simp only [store,get?_insert_ne hz,get?_map,ByteContents.finished]
      rw [ByteContents.finishCells_outside _ _ _ _ _ hk]

theorem release_points [GS] (candidate : Unified.Candidate) (node : Unified.Node) (demands : List Demand)
    (values : Location → Option Symbolic.Byte) (heap : HeapF Cell) :
    genHeapInterp heap ∗ heldPoints (Unified.memoryControlNode node) demands values ==∗
      genHeapInterp (releaseStore candidate node values demands heap) ∗ freePoints demands (returnedValues candidate node values) := by
  induction demands generalizing heap with
  | nil =>
    simp only [releaseStore,heldPoints,freePoints,Iris.Algebra.BigOpL.bigOpL_nil]
    iintro H
    imodintro
    iexact H
  | cons demand rest ih =>
    change genHeapInterp heap ∗ (byte demand.location (.own 1) ⟨.held (Unified.memoryControlNode node) demand.mode,values demand.location⟩ ∗ heldPoints (Unified.memoryControlNode node) rest values) ==∗
      genHeapInterp (insert (releaseStore candidate node values rest heap) (ByteAuthority.key demand.location)
        (.byte ⟨.available,returnedValues candidate node values demand.location⟩)) ∗
      (byte demand.location (.own 1) ⟨.available,returnedValues candidate node values demand.location⟩ ∗ freePoints rest (returnedValues candidate node values))
    iintro ⟨Hheap,Hhead,Hrest⟩
    imod ih heap $$ [$Hheap $Hrest] with ⟨Hheap,Hrest⟩
    unfold byte
    imod genHeap_update (v₂ := Cell.byte ⟨.available,returnedValues candidate node values demand.location⟩) $$ [$Hheap $Hhead] with ⟨Hheap,Hhead⟩
    imodintro
    iframe Hheap Hhead Hrest

theorem finish_distinct {ctx : Context} {node demands state next}
    (hs : transition ctx (.finish node demands) state = .ok next) : ByteAuthority.Footprint.Distinct demands := by
  change ByteContents.finish ctx.block ctx.candidate ctx.histories node demands state = .ok next at hs
  unfold ByteContents.finish at hs
  cases ha : ByteAuthority.Footprint.finish ctx.block ctx.candidate ctx.histories (Unified.memoryControlNode node) demands (ByteContents.erase state) with
  | error error => simp [ha] at hs
  | ok authority => exact (ByteAuthority.Footprint.finish_spec ha).2.2.2.1

theorem finish_update_local [GS] (state : State) (candidate : Unified.Candidate) (node : Unified.Node)
    (demands : List Demand) (values : Location → Option Symbolic.Byte)
    (hd : ByteAuthority.Footprint.Distinct demands) (hm : Matches state (Unified.memoryControlNode node) demands values) :
    genHeapInterp (store state) ∗ control state ∗ heldPoints (Unified.memoryControlNode node) demands values ==∗
      genHeapInterp (store (ByteContents.finished candidate node demands state)) ∗ control (ByteContents.finished candidate node demands state) ∗
        freePoints demands (returnedValues candidate node values) := by
  iintro ⟨Hheap,Hcontrol,Hheld⟩
  imod release_points candidate node demands values (store state) $$ [$Hheap $Hheld] with ⟨Hheap,Hfree⟩
  unfold control
  imod genHeap_update (v₂ := Cell.control (ByteContents.finished candidate node demands state)) $$ [$Hheap $Hcontrol] with ⟨Hheap,Hcontrol⟩
  rw [← store_finished_footprint state candidate node demands values hd hm]
  imodintro
  iframe Hheap Hcontrol Hfree

theorem finish_local_cps [GS] (ctx : Context) (state next : State) (node : Unified.Node) (demands : List Demand)
    (values : Location → Option Symbolic.Byte) (tail : List Action) (frame : IProp GF) (post : Except ByteContents.Error State → IProp GF)
    (hs : transition ctx (.finish node demands) state = .ok next)
    (hm : Matches state (Unified.memoryControlNode node) demands values)
    (hcont : control next ∗ freePoints demands (returnedValues ctx.candidate node values) ∗ frame ⊢
      WP (script ctx tail) {{ result, post result }}) :
    control state ∗ heldPoints (Unified.memoryControlNode node) demands values ∗ frame ⊢
      WP (script ctx (.finish node demands::tail)) {{ result, post result }} := by
  have he := (ByteContents.finish_spec hs).2.2.1
  subst next
  apply step_script_wp ctx state (ByteContents.finished ctx.candidate node demands state) (.finish node demands) tail
    iprop(heldPoints (Unified.memoryControlNode node) demands values ∗ frame)
    iprop(freePoints demands (returnedValues ctx.candidate node values) ∗ frame) post hs ?_ hcont
  iintro ⟨Hheap,Hcontrol,Hheld,Hframe⟩
  imod finish_update_local state ctx.candidate node demands values (finish_distinct hs) hm $$ [$Hheap $Hcontrol $Hheld]
    with ⟨Hheap,Hcontrol,Hfree⟩
  imodintro
  iframe Hheap Hcontrol Hfree Hframe

theorem finish_local_wp [GS] (ctx : Context) (state next : State) (node : Unified.Node) (demands : List Demand)
    (values : Location → Option Symbolic.Byte) (frame : IProp GF)
    (hs : transition ctx (.finish node demands) state = .ok next)
    (hm : Matches state (Unified.memoryControlNode node) demands values) :
    control state ∗ heldPoints (Unified.memoryControlNode node) demands values ∗ frame ⊢
      WP (script ctx [.finish node demands])
      {{ result, ⌜result = .ok next⌝ ∗ control next ∗ freePoints demands (returnedValues ctx.candidate node values) ∗ frame }} := by
  exact finish_local_cps ctx state next node demands values [] frame _ hs hm
    (script_nil_wp ctx next iprop(freePoints demands (returnedValues ctx.candidate node values) ∗ frame))

def Free (state : State) (demands : List Demand) (values : Location → Option Symbolic.Byte) : Prop :=
  ∀ demand ∈ demands, get? state.cells (ByteAuthority.key demand.location) = some ⟨.available,values demand.location⟩

def granted : State → Unified.ControlNode → List Demand → (Location → Option Symbolic.Byte) → State
  | state,_,[],_ => state
  | state,node,demand::rest,values => granted
      (ByteContents.claimed state ⟨node,demand.location,demand.mode⟩ ⟨.available,values demand.location⟩) node rest values

def acquisitionActions (node : Unified.ControlNode) (demands : List Demand) : List Action :=
  demands.map (fun demand => .claim ⟨node,demand.location,demand.mode⟩)
def cycleActions (node : Unified.Node) (demands : List Demand) : List Action :=
  acquisitionActions (Unified.memoryControlNode node) demands ++ [.finish node demands]

theorem granted_coupled (state : State) (node : Unified.ControlNode) (demands : List Demand) (values : Location → Option Symbolic.Byte) :
    (granted state node demands values).coupled = state.coupled := by
  induction demands generalizing state with
  | nil => rfl
  | cons demand rest ih => exact ih _

theorem granted_outside (state : State) (node : Unified.ControlNode) (demands : List Demand) (values : Location → Option Symbolic.Byte)
    (k : Nat) (hn : k ∉ ByteAuthority.Footprint.keys demands) :
    get? (granted state node demands values).cells k = get? state.cells k := by
  induction demands generalizing state with
  | nil => rfl
  | cons head rest ih =>
    have he : ByteAuthority.key head.location ≠ k := by intro h; exact hn (by simp [ByteAuthority.Footprint.keys,h])
    rw [granted,ih _ (fun hm => hn (List.mem_cons_of_mem _ hm))]
    exact get?_insert_ne he

theorem free_after_head {state head rest values node} (hd : ByteAuthority.Footprint.Distinct (head::rest))
    (hf : Free state (head::rest) values) :
    Free (ByteContents.claimed state ⟨node,head.location,head.mode⟩ ⟨.available,values head.location⟩) rest values := by
  intro demand hm
  have he : ByteAuthority.key head.location ≠ ByteAuthority.key demand.location := by
    intro h
    exact (ByteAuthority.Footprint.distinct_tail hd).1 (List.mem_map.mpr ⟨demand,hm,h.symm⟩)
  rw [ByteContents.claimed,get?_insert_ne he]
  exact hf demand (by simp [hm])

theorem granted_matches (state : State) (node : Unified.ControlNode) (demands : List Demand) (values : Location → Option Symbolic.Byte)
    (hd : ByteAuthority.Footprint.Distinct demands) : Matches (granted state node demands values) node demands values := by
  induction demands generalizing state with
  | nil => intro demand hm; cases hm
  | cons head rest ih =>
    intro demand hm
    rcases List.mem_cons.mp hm with rfl | hm
    · rw [granted,granted_outside _ _ _ _ _ (ByteAuthority.Footprint.distinct_tail hd).1]
      simp [ByteContents.claimed,get?_insert]
    · exact ih _ (ByteAuthority.Footprint.distinct_tail hd).2 demand hm

theorem acquisition_cps [GS] (ctx : Context) (state : State) (node : Unified.ControlNode) (demands : List Demand)
    (values : Location → Option Symbolic.Byte) (tail : List Action) (frame : IProp GF) (post : Except ByteContents.Error State → IProp GF)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories state.coupled.done node)
    (hs : ByteAuthority.Footprint.Sound ctx.candidate node demands) (hd : ByteAuthority.Footprint.Distinct demands)
    (hf : Free state demands values)
    (hcont : control (granted state node demands values) ∗ heldPoints node demands values ∗ frame ⊢
      WP (script ctx tail) {{ result, post result }}) :
    control state ∗ freePoints demands values ∗ frame ⊢
      WP (script ctx (acquisitionActions node demands ++ tail)) {{ result, post result }} := by
  induction demands generalizing state tail frame post with
  | nil =>
    simpa only [acquisitionActions,List.map_nil,List.nil_append,granted,heldPoints,freePoints,Iris.Algebra.BigOpL.bigOpL_nil] using hcont
  | cons head rest ih =>
    let mid := ByteContents.claimed state ⟨node,head.location,head.mode⟩ ⟨.available,values head.location⟩
    change (control state ∗ (byte head.location (.own 1) ⟨.available,values head.location⟩ ∗ freePoints rest values) ∗ frame) ⊢
      WP (script ctx (.claim ⟨node,head.location,head.mode⟩ :: (acquisitionActions node rest ++ tail))) {{ result, post result }}
    iintro ⟨Hcontrol,⟨Hhead,Hrest⟩,Hframe⟩
    iapply claim_local_cps ctx state ⟨node,head.location,head.mode⟩ (values head.location)
      (acquisitionActions node rest ++ tail) iprop(freePoints rest values ∗ frame) post hr
      (hs head (by simp)) (hf head (by simp)) ?_ $$ [$Hcontrol $Hhead $Hrest $Hframe]
    iintro ⟨Hcontrol,Hhead,Hrest,Hframe⟩
    iapply ih (state := mid) (tail := tail) (frame := iprop(byte head.location (.own 1) ⟨.held node head.mode,values head.location⟩ ∗ frame))
      (post := post) hr (by intro demand hm; exact hs demand (by simp [hm])) (ByteAuthority.Footprint.distinct_tail hd).2
      (free_after_head hd hf) ?_ $$ [$Hcontrol $Hrest $Hhead $Hframe]
    iintro ⟨Hcontrol,Hheld,Hhead,Hframe⟩
    have hcont' : control (granted mid node rest values) ∗
        (byte head.location (.own 1) ⟨.held node head.mode,values head.location⟩ ∗ heldPoints node rest values) ∗ frame ⊢
        WP (script ctx tail) {{ result, post result }} := hcont
    iapply hcont' $$ [$Hcontrol $Hhead $Hheld $Hframe]

theorem cycle_local_wp [GS] (ctx : Context) (state next : State) (node : Unified.Node) (demands : List Demand)
    (values : Location → Option Symbolic.Byte) (frame : IProp GF)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories state.coupled.done (Unified.memoryControlNode node))
    (hs : ByteAuthority.Footprint.Sound ctx.candidate (Unified.memoryControlNode node) demands)
    (hd : ByteAuthority.Footprint.Distinct demands) (hf : Free state demands values)
    (hfinish : transition ctx (.finish node demands) (granted state (Unified.memoryControlNode node) demands values) = .ok next) :
    control state ∗ freePoints demands values ∗ frame ⊢ WP (script ctx (cycleActions node demands))
      {{ result, ⌜result = .ok next⌝ ∗ control next ∗ freePoints demands (returnedValues ctx.candidate node values) ∗ frame }} := by
  apply acquisition_cps ctx state (Unified.memoryControlNode node) demands values [.finish node demands] frame _ hr hs hd hf
  exact finish_local_wp ctx _ next node demands values frame hfinish (granted_matches state _ demands values hd)

theorem map_freePoints [GS] (demands : List Demand) (values : Location → Option Symbolic.Byte) (heap : HeapF Cell)
    (hd : ByteAuthority.Footprint.Distinct demands)
    (hl : ∀ demand ∈ demands, get? heap (ByteAuthority.key demand.location) = some (.byte ⟨.available,values demand.location⟩)) :
    iprop([∗map] k ↦ value ∈ heap, pointsTo k (.own 1) value) ⊢ freePoints demands values := by
  induction demands generalizing heap with
  | nil =>
    iintro Hall
    simp only [freePoints,Iris.Algebra.BigOpL.bigOpL_nil]
    itrivial
  | cons head rest ih =>
    have hdistinct := ByteAuthority.Footprint.distinct_tail hd
    change _ ⊢ byte head.location (.own 1) ⟨.available,values head.location⟩ ∗ freePoints rest values
    iintro Hall
    icases (BigSepM.bigSepM_delete (hl head (by simp))) $$ Hall with ⟨Hhead,Hrest⟩
    isplitl [Hhead]
    · unfold byte; iexact Hhead
    · iapply ih (Iris.Std.PartialMap.delete heap (ByteAuthority.key head.location)) hdistinct.2 ?_ $$ Hrest
      intro demand hm
      have he : ByteAuthority.key head.location ≠ ByteAuthority.key demand.location := by
        intro h; exact hdistinct.1 (List.mem_map.mpr ⟨demand,hm,h.symm⟩)
      rw [get?_delete_ne he]
      exact hl demand (by simp [hm])

theorem allPoints_control_free [GS] (state : State) (demands : List Demand) (values : Location → Option Symbolic.Byte)
    (hd : ByteAuthority.Footprint.Distinct demands) (hf : Free state demands values) :
    allPoints state ⊢ control state ∗ freePoints demands values := by
  unfold allPoints control
  iintro Hall
  icases (BigSepM.bigSepM_delete (store_control state)) $$ Hall with ⟨Hcontrol,Hrest⟩
  isplitl [Hcontrol]
  · iexact Hcontrol
  · iapply map_freePoints demands values _ hd ?_ $$ Hrest
    intro demand hm
    rw [get?_delete_ne (Ne.symm (ByteAuthority.byte_key_not_control demand.location)),store_byte,hf demand hm]
    rfl

theorem cycle_local_adequate (ctx : Context) (state next : State) (node : Unified.Node) (demands : List Demand)
    (values : Location → Option Symbolic.Byte)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories state.coupled.done (Unified.memoryControlNode node))
    (hs : ByteAuthority.Footprint.Sound ctx.candidate (Unified.memoryControlNode node) demands)
    (hd : ByteAuthority.Footprint.Distinct demands) (hf : Free state demands values)
    (hfinish : transition ctx (.finish node demands) (granted state (Unified.memoryControlNode node) demands values) = .ok next) :
    adequate .NotStuck (script ctx (cycleActions node demands)) state (fun result _ => result = .ok next) := by
  apply heap_adequacy
  intro _
  iintro Hall
  ihave Hparts := allPoints_control_free state demands values hd hf $$ Hall
  icases Hparts with ⟨Hcontrol,Hfree⟩
  ihave Hwp := cycle_local_wp ctx state next node demands values iprop(True) hr hs hd hf hfinish $$ [$Hcontrol $Hfree]
  iapply wp_mono ?_ $$ Hwp
  intro result
  iintro ⟨%hv,Hcontrol,Hfree,Hframe⟩
  ipureintro; exact hv

theorem granted_withSpare (state : State) (node : Unified.ControlNode) (demands : List Demand)
    (values : Location → Option Symbolic.Byte) (loc : Location) (value : Option Symbolic.Byte)
    (hn : ByteAuthority.key loc ∉ ByteAuthority.Footprint.keys demands) :
    granted (ByteContents.withSpare state loc value) node demands values =
      ByteContents.withSpare (granted state node demands values) loc value := by
  induction demands generalizing state with
  | nil => rfl
  | cons head rest ih =>
    have he : ByteAuthority.key loc ≠ ByteAuthority.key head.location := by
      intro h; exact hn (by simp [ByteAuthority.Footprint.keys,h])
    have hc : ByteContents.claimed (ByteContents.withSpare state loc value) ⟨node,head.location,head.mode⟩ ⟨.available,values head.location⟩ =
        ByteContents.withSpare (ByteContents.claimed state ⟨node,head.location,head.mode⟩ ⟨.available,values head.location⟩) loc value := by
      apply congrArg₂ ByteContents.State.mk
      · rfl
      · exact insert_insert_comm he
    simp only [granted]
    rw [hc]
    exact ih _ (fun hm => hn (List.mem_cons_of_mem _ hm))

theorem free_withSpare {state demands values loc value} (hf : Free state demands values)
    (hn : ByteAuthority.key loc ∉ ByteAuthority.Footprint.keys demands) : Free (ByteContents.withSpare state loc value) demands values := by
  intro demand hm
  have he : ByteAuthority.key loc ≠ ByteAuthority.key demand.location := by
    intro h; exact hn (List.mem_map.mpr ⟨demand,hm,h.symm⟩)
  rw [ByteContents.withSpare,get?_insert_ne he]
  exact hf demand hm

theorem byte_split [GS] (loc : Location) (q : Qp) (payload : Payload) :
    byte loc (.own q) payload ⊣⊢ byte loc (.own q.half) payload ∗ byte loc (.own q.half) payload := by
  unfold byte
  have hs := (Iris.instFractionalPointsTo (GF := GF) (l := ByteAuthority.key loc) (v := Cell.byte payload)).fractional q.half q.half
  simpa only [Qp.half_add_half] using hs

theorem allPoints_control_free_frame [GS] (state : State) (demands : List Demand) (values : Location → Option Symbolic.Byte)
    (loc : Location) (payload : Payload) (hd : ByteAuthority.Footprint.Distinct demands) (hf : Free state demands values)
    (hn : ByteAuthority.key loc ∉ ByteAuthority.Footprint.keys demands) (hg : get? state.cells (ByteAuthority.key loc) = some payload) :
    allPoints state ⊢ control state ∗ freePoints demands values ∗ byte loc (.own 1) payload := by
  unfold allPoints control
  iintro Hall
  icases (BigSepM.bigSepM_delete (store_control state)) $$ Hall with ⟨Hcontrol,Hrest⟩
  have hl : get? (delete (store state) ByteAuthority.controlKey) (ByteAuthority.key loc) = some (.byte payload) := by
    rw [get?_delete_ne (Ne.symm (ByteAuthority.byte_key_not_control loc)),store_byte,hg]
    rfl
  icases (BigSepM.bigSepM_delete hl) $$ Hrest with ⟨Hbyte,Hrest⟩
  isplitl [Hcontrol]
  · iexact Hcontrol
  isplitr [Hbyte]
  · iapply map_freePoints demands values _ hd ?_ $$ Hrest
    intro demand hm
    have he : ByteAuthority.key loc ≠ ByteAuthority.key demand.location := by
      intro h; exact hn (List.mem_map.mpr ⟨demand,hm,h.symm⟩)
    rw [get?_delete_ne he,get?_delete_ne (Ne.symm (ByteAuthority.byte_key_not_control demand.location)),store_byte,hf demand hm]
    rfl
  · unfold byte; iexact Hbyte

end
end Ptx.ByteContentsHeap
