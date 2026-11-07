import Ptx.Iris.ByteInventory

/-! Native source-script composition retains every heap fragment between
nodes. Each source node still executes its actual per-byte claims and finish;
no whole-script atomic update or assumed initial loans replace those steps.
-/
namespace Ptx.ByteAuthorityHeap
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

theorem map_freePoints_accessor [GS] (demands : List ByteAuthority.Footprint.Demand) (heap : HeapF Cell)
    (hd : ByteAuthority.Footprint.Distinct demands)
    (hl : ∀ demand ∈ demands, get? heap (ByteAuthority.key demand.location) = some (.byte .available)) :
    ([∗map] k ↦ value ∈ heap, pointsTo k (.own 1) value) ⊢
      freePoints demands ∗ (freePoints demands -∗ [∗map] k ↦ value ∈ heap, pointsTo k (.own 1) value) := by
  induction demands generalizing heap with
  | nil =>
    simp only [freePoints,Iris.Algebra.BigOpL.bigOpL_nil]
    iintro Hall
    isplitl []
    · itrivial
    · iintro Hempty
      iexact Hall
  | cons head rest ih =>
    have hdistinct := ByteAuthority.Footprint.distinct_tail hd
    have hhead := hl head (by simp)
    change _ ⊢ (byte head.location (.own 1) .available ∗ freePoints rest) ∗
      ((byte head.location (.own 1) .available ∗ freePoints rest) -∗ [∗map] k ↦ value ∈ heap, pointsTo k (.own 1) value)
    iintro Hall
    icases (BigSepM.bigSepM_delete hhead) $$ Hall with ⟨Hhead,Hrest⟩
    have hrest : ∀ demand ∈ rest, get? (delete heap (ByteAuthority.key head.location)) (ByteAuthority.key demand.location) = some (.byte .available) := by
      intro demand hm
      have hne : ByteAuthority.key head.location ≠ ByteAuthority.key demand.location := by
        intro he
        exact hdistinct.1 (List.mem_map.mpr ⟨demand,hm,he.symm⟩)
      rw [get?_delete_ne hne]
      exact hl demand (by simp [hm])
    icases ih _ hdistinct.2 hrest $$ Hrest with ⟨Hfree,Hreturn⟩
    isplitl [Hhead Hfree]
    · isplitl [Hhead]
      · unfold byte; iexact Hhead
      · iexact Hfree
    · iintro ⟨Hhead,Hfree⟩
      ihave Hrest := Hreturn $$ Hfree
      have hrebuild : byte head.location (.own 1) .available ∗
          iprop([∗map] k ↦ value ∈ delete heap (ByteAuthority.key head.location), pointsTo k (.own 1) value) ⊢
          iprop([∗map] k ↦ value ∈ heap, pointsTo k (.own 1) value) := by
        unfold byte
        exact (BigSepM.bigSepM_delete hhead).2
      iapply hrebuild $$ [$Hhead $Hrest]

theorem allPoints_parts [GS] (state : State) :
    allPoints state ⊣⊢ control state ∗ iprop([∗map] k ↦ value ∈ delete (store state) ByteAuthority.controlKey, pointsTo k (.own 1) value) := by
  unfold allPoints control
  exact BigSepM.bigSepM_delete (store_control state)

theorem store_frame_eq (before after : State) (hb : before.bytes = after.bytes) :
    delete (store before) ByteAuthority.controlKey = delete (store after) ByteAuthority.controlKey := by
  apply equiv_iff_eq.mp
  intro k
  by_cases hz : ByteAuthority.controlKey = k
  · subst k; simp [get?_delete]
  · simp only [get?_delete_ne hz,store,get?_insert_ne hz,get?_map,hb]

theorem cycle_cps [GS] (ctx : Context) (state : State) (node : Unified.ControlNode)
    (demands : List ByteAuthority.Footprint.Demand) (tail : List Action) (frame : IProp GF)
    (post : Except ByteAuthority.Error State → IProp GF)
    (hp : ByteAuthority.Footprint.Supported state) (hi : ByteAuthority.Active ctx.block ctx.candidate ctx.histories state)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories state.coupled.done node)
    (hs : ByteAuthority.Footprint.Sound ctx.candidate node demands) (hc : ByteAuthority.Footprint.Covers ctx.candidate node demands)
    (hd : ByteAuthority.Footprint.Distinct demands) (ha : ByteAuthority.Footprint.Available state demands)
    (hcont : control (ByteAuthority.retired (ByteAuthority.Footprint.granted state node demands) node) ∗
      freePoints demands ∗ frame ⊢ WP (script ctx tail) {{ value, post value }}) :
    control state ∗ freePoints demands ∗ frame ⊢ WP (script ctx (cycleActions node demands ++ tail)) {{ value, post value }} := by
  let granted := ByteAuthority.Footprint.granted state node demands
  have hready : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories granted.coupled.done node := by
    simpa only [granted,ByteAuthority.Footprint.granted_coupled] using hr
  have hheld := ByteAuthority.Footprint.granted_held state node demands hd
  have hframe := ByteAuthority.Footprint.granted_frame_from_invariants hp hi hr hs hc hd ha
  have hfinish : transition ctx (.finish node demands) granted = .ok (ByteAuthority.retired granted node) :=
    ByteAuthority.Footprint.finish_succeeds hready hs hc hd hheld hframe
  simp only [cycleActions,List.append_assoc,List.singleton_append]
  apply acquisition_cps ctx state node demands (.finish node demands::tail) frame post hr hs hd ha
  iintro ⟨Hcontrol,Hheld,Hframe⟩
  iapply step_script_wp ctx granted (ByteAuthority.retired granted node) (.finish node demands) tail
    iprop(heldPoints node demands ∗ frame) iprop(freePoints demands ∗ frame) post hfinish ?_ hcont $$ [$Hcontrol $Hheld $Hframe]
  iintro ⟨Hheap,Hcontrol,Hheld,Hframe⟩
  imod finish_update granted node demands hheld hframe $$ [$Hheap $Hcontrol $Hheld] with ⟨Hheap,Hcontrol,Hfree⟩
  imodintro
  iframe Hheap Hcontrol Hfree Hframe

theorem inventory_cycle_all_cps [GS] (ctx : Context) (coupled : Bridge.State) (locations : List Location)
    (node : Unified.ControlNode) (tail : List Action) (frame : IProp GF) (post : Except ByteAuthority.Error State → IProp GF)
    (hb : ∀ loc mode, ByteAuthority.Uses ctx.candidate node loc mode → loc ∈ locations)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories coupled.done node)
    (hcont : allPoints (ByteAuthority.Footprint.initialized {coupled with done := fun n => coupled.done n ∨ n = node} locations) ∗ frame ⊢
      WP (script ctx tail) {{ value, post value }}) :
    allPoints (ByteAuthority.Footprint.initialized coupled locations) ∗ frame ⊢
      WP (script ctx (cycleActions node (ByteAuthority.Footprint.inventory ctx.candidate node locations) ++ tail)) {{ value, post value }} := by
  let state := ByteAuthority.Footprint.initialized coupled locations
  let next := ByteAuthority.Footprint.initialized {coupled with done := fun n => coupled.done n ∨ n = node} locations
  let demands := ByteAuthority.Footprint.inventory ctx.candidate node locations
  let restore : IProp GF := iprop(freePoints demands -∗ [∗map] k ↦ value ∈ delete (store state) ByteAuthority.controlKey, pointsTo k (.own 1) value)
  have hd := ByteAuthority.Footprint.inventory_distinct ctx.candidate node locations
  have ha := ByteAuthority.Footprint.inventory_available coupled ctx.candidate node locations
  have hp := ByteAuthority.Footprint.initialized_available coupled locations
  iintro ⟨Hall,Hframe⟩
  icases allPoints_parts state $$ Hall with ⟨Hcontrol,Hrest⟩
  icases map_freePoints_accessor demands _ hd ?_ $$ Hrest with ⟨Hfree,Hreturn⟩
  · intro demand hm
    rw [get?_delete_ne (Ne.symm (ByteAuthority.byte_key_not_control demand.location)),store_byte,ha demand hm]
    rfl
  have hcycle := cycle_cps ctx state node demands tail iprop(restore ∗ frame) post
    (ByteAuthority.Footprint.available_pool_supported hp) (ByteAuthority.available_pool_active hp) hr
    (ByteAuthority.Footprint.inventory_sound _ _ _) (ByteAuthority.Footprint.inventory_covers hb) hd ha
  have he : ByteAuthority.retired (ByteAuthority.Footprint.granted state node demands) node = next :=
    ByteAuthority.Footprint.inventory_cycle_endpoint hb hr
  rw [he] at hcycle
  iapply hcycle ?_ $$ [$Hcontrol $Hfree $Hreturn $Hframe]
  iintro ⟨Hcontrol,Hfree,Hreturn,Hframe⟩
  ihave Hrest := Hreturn $$ Hfree
  have hf : delete (store state) ByteAuthority.controlKey = delete (store next) ByteAuthority.controlKey :=
    store_frame_eq state next rfl
  have hreframe : iprop([∗map] k ↦ value ∈ delete (store state) ByteAuthority.controlKey, pointsTo k (.own 1) value) ⊢
      iprop([∗map] k ↦ value ∈ delete (store next) ByteAuthority.controlKey, pointsTo k (.own 1) value) := by rw [hf]
  ihave Hrest := hreframe $$ Hrest
  ihave Hall : allPoints next $$ [Hcontrol Hrest]
  · iapply (allPoints_parts next).2 $$ [$Hcontrol $Hrest]
  iapply hcont $$ [$Hall $Hframe]

def sourceActions (ctx : Context) (locations : List Location) (nodes : List Unified.ControlNode) : List Action :=
  nodes.flatMap (fun node => cycleActions node (ByteAuthority.Footprint.inventory ctx.candidate node locations))

theorem source_run (ctx : Context) (locations : List Location) (protocol : Ptx.Async.State)
    (hb : ByteAuthority.Footprint.Bounded ctx.candidate locations) {before after nodes}
    (ho : ByteAuthority.Footprint.Ordered ctx.block ctx.candidate ctx.histories before nodes after) :
    IrisExecution.run (transition ctx) (sourceActions ctx locations nodes) (ByteAuthority.Footprint.initialized ⟨protocol,before⟩ locations) =
      .ok (ByteAuthority.Footprint.initialized ⟨protocol,after⟩ locations) := by
  induction ho with
  | nil => rfl
  | @cons before after node rest hr tail ih =>
    simp only [sourceActions,List.flatMap_cons,run_append]
    rw [inventory_cycle_run ctx ⟨protocol,before⟩ locations node (hb node) hr]
    exact ih

theorem source_cps [GS] (ctx : Context) (locations : List Location) (protocol : Ptx.Async.State)
    (hb : ByteAuthority.Footprint.Bounded ctx.candidate locations) {before after nodes}
    (ho : ByteAuthority.Footprint.Ordered ctx.block ctx.candidate ctx.histories before nodes after)
    (tail : List Action) (frame : IProp GF) (post : Except ByteAuthority.Error State → IProp GF)
    (hcont : allPoints (ByteAuthority.Footprint.initialized ⟨protocol,after⟩ locations) ∗ frame ⊢
      WP (script ctx tail) {{ value, post value }}) :
    allPoints (ByteAuthority.Footprint.initialized ⟨protocol,before⟩ locations) ∗ frame ⊢
      WP (script ctx (sourceActions ctx locations nodes ++ tail)) {{ value, post value }} := by
  induction ho with
  | nil => exact hcont
  | @cons before after node rest hr order ih =>
    simp only [sourceActions,List.flatMap_cons,List.append_assoc]
    apply inventory_cycle_all_cps ctx ⟨protocol,before⟩ locations node _ frame post (hb node) hr
    exact ih hcont

theorem script_nil_all_wp [GS] (ctx : Context) (state : State) (frame : IProp GF) :
    allPoints state ∗ frame ⊢ WP (script ctx []) {{ value, ⌜value = .ok state⌝ ∗ allPoints state ∗ frame }} := by
  iintro ⟨Hall,Hframe⟩
  icases allPoints_parts state $$ Hall with ⟨Hcontrol,Hrest⟩
  ihave Hwp := script_nil_wp ctx state
    iprop(([∗map] k ↦ value ∈ delete (store state) ByteAuthority.controlKey, pointsTo k (.own 1) value) ∗ frame)
    $$ [$Hcontrol $Hrest $Hframe]
  iapply wp_mono ?_ $$ Hwp
  intro value
  iintro ⟨%hv,Hcontrol,Hrest,Hframe⟩
  isplit
  · ipureintro; exact hv
  isplitl [Hcontrol Hrest]
  · iapply (allPoints_parts state).2 $$ [$Hcontrol $Hrest]
  · iexact Hframe

theorem source_wp [GS] (ctx : Context) (locations : List Location) (protocol : Ptx.Async.State)
    (hb : ByteAuthority.Footprint.Bounded ctx.candidate locations) {before after nodes}
    (ho : ByteAuthority.Footprint.Ordered ctx.block ctx.candidate ctx.histories before nodes after) (frame : IProp GF) :
    allPoints (ByteAuthority.Footprint.initialized ⟨protocol,before⟩ locations) ∗ frame ⊢
      WP (script ctx (sourceActions ctx locations nodes))
      {{ value, ⌜value = .ok (ByteAuthority.Footprint.initialized ⟨protocol,after⟩ locations)⌝ ∗
        allPoints (ByteAuthority.Footprint.initialized ⟨protocol,after⟩ locations) ∗ frame }} := by
  have hw := source_cps ctx locations protocol hb ho [] frame _ (script_nil_all_wp ctx _ frame)
  simpa only [List.append_nil] using hw

theorem source_adequate (ctx : Context) (locations : List Location) (protocol : Ptx.Async.State)
    (hb : ByteAuthority.Footprint.Bounded ctx.candidate locations) {before after nodes}
    (ho : ByteAuthority.Footprint.Ordered ctx.block ctx.candidate ctx.histories before nodes after) :
    adequate .NotStuck (script ctx (sourceActions ctx locations nodes))
      (ByteAuthority.Footprint.initialized ⟨protocol,before⟩ locations)
      (fun value _ => value = .ok (ByteAuthority.Footprint.initialized ⟨protocol,after⟩ locations)) := by
  apply heap_adequacy
  intro _
  iintro Hall
  ihave Hwp := source_wp ctx locations protocol hb ho iprop(True) $$ [$Hall]
  iapply wp_mono ?_ $$ Hwp
  intro value
  iintro ⟨%hv,Hall,Hframe⟩
  ipureintro; exact hv

theorem reached_native_witness (ctx : Context) (locations : List Location) (protocol : Ptx.Async.State)
    (hb : ByteAuthority.Footprint.Bounded ctx.candidate locations) {done}
    (hr : Reached ctx.block ctx.candidate ctx.histories done) :
    ∃ nodes, ByteAuthority.Footprint.Ordered ctx.block ctx.candidate ctx.histories (fun _ => False) nodes done ∧
      IrisExecution.run (transition ctx) (sourceActions ctx locations nodes)
        (ByteAuthority.Footprint.initialized ⟨protocol,fun _ => False⟩ locations) =
        .ok (ByteAuthority.Footprint.initialized ⟨protocol,done⟩ locations) ∧
      adequate .NotStuck (script ctx (sourceActions ctx locations nodes))
        (ByteAuthority.Footprint.initialized ⟨protocol,fun _ => False⟩ locations)
        (fun value _ => value = .ok (ByteAuthority.Footprint.initialized ⟨protocol,done⟩ locations)) := by
  obtain ⟨nodes,ho⟩ := ByteAuthority.Footprint.reached_ordered hr
  exact ⟨nodes,ho,source_run ctx locations protocol hb ho,source_adequate ctx locations protocol hb ho⟩

end
end Ptx.ByteAuthorityHeap
