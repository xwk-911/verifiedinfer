import Ptx.Kernels.HopperDoubleBufferRegions
import Ptx.Tests.HopperProgress

/-! Source-derived region/mode coverage, public preparation and lifetime guards.
The allocation map is a checked model layout, not a CUDA allocation certificate;
the abstract copy's Nat cell values are not interpreted as tensor bytes. -/
namespace Ptx.HopperRegionLoanTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section

abbrev family := HopperProgressTests.family
abbrev candidate := HopperProgressTests.candidate
abbrev histories := HopperProgressTests.histories
abbrev source := HopperProgressTests.source
abbrev nativeWork := HopperProgressTests.nativeWork
abbrev tmaWork (a b) (tile : Fin 3) := Work.tma ((family a b).copyAId tile)

def nativePrepared : Ptx.Async.State := {
  streams := [⟨2,0,[.use 0,.use 1],[]⟩]
  buffers := [⟨17,true,[⟨⟨0,1⟩,.read⟩]⟩,⟨17,true,[⟨⟨0,2⟩,.read⟩]⟩]
  events := [⟨2,⟨0,2⟩⟩,⟨1,⟨0,1⟩⟩,⟨0,⟨0,0⟩⟩]
}
def tmaPrepared : Ptx.Async.State := {
  streams := [⟨2,0,[.use 0,.copy 1 2],[]⟩]
  buffers := [⟨0,true,[⟨⟨0,1⟩,.read⟩]⟩,⟨17,true,[⟨⟨0,2⟩,.read⟩]⟩,⟨0,true,[⟨⟨0,2⟩,.write⟩]⟩]
  events := [⟨2,⟨0,2⟩⟩,⟨1,⟨0,1⟩⟩,⟨0,⟨0,0⟩⟩]
}

theorem native_public_preparation : Ptx.Async.run (Ptx.Async.initial 1 [17,17])
    [.record 0 0,.use 0 0,.record 0 1,.use 0 1,.record 0 2] = .ok nativePrepared := by decide
theorem tma_public_preparation : Ptx.Async.run (Ptx.Async.initial 1 [0,17,0])
    [.record 0 0,.use 0 0,.record 0 1,.copy 0 1 2,.record 0 2] = .ok tmaPrepared := by decide

theorem native_prepared_valid : Ptx.Async.Invariant nativePrepared :=
  Ptx.Async.steps_invariant (Ptx.Async.initial_invariant 1 [17,17]) (Ptx.Async.run_sound native_public_preparation)
theorem tma_prepared_valid : Ptx.Async.Invariant tmaPrepared :=
  Ptx.Async.steps_invariant (Ptx.Async.initial_invariant 1 [0,17,0]) (Ptx.Async.run_sound tma_public_preparation)

theorem native_prepared_borrowed (work tile) : Regions.Borrowed (nativeBindings work tile) nativePrepared := by
  simp [Regions.Borrowed,nativeBindings,Ptx.Async.Holds,nativePrepared]

theorem tma_prepared_borrowed (work tiles tile) : Regions.Borrowed (tmaABindings work tiles tile) tmaPrepared := by
  simp [Regions.Borrowed,tmaABindings,Ptx.Async.Holds,tmaPrepared]

theorem prepared_region_faithful {resolve candidate histories cluster} {protocol : Ptx.Async.State}
    (hz : ∀ (sid : Nat) (st : Ptx.Async.Stream), protocol.streams[sid]? = some st → st.completed = 0) (work : Work) :
    Bridge.Faithful resolve candidate histories cluster (regionPlan work) ⟨protocol,fun _ => False⟩ := by
  apply Bridge.prepared_faithful hz
  intro ticket actual hm
  simp only [regionPlan] at hm
  split at hm
  · rename_i ht
    rcases ht with rfl | rfl <;> decide
  · cases hm

theorem native_initial_faithful (a b) (tile : Fin 3) :
    Bridge.Faithful Tma.localShared (candidate a b) (histories a b) dataCluster (regionPlan (nativeWork a b tile))
      ⟨nativePrepared,fun _ => False⟩ := by
  apply prepared_region_faithful
  intro sid st hg
  cases sid with
  | zero => simp only [nativePrepared,List.getElem?_cons_zero,Option.some.injEq] at hg; subst st; rfl
  | succ sid => simp [nativePrepared] at hg

theorem tma_initial_faithful (a b) (tile : Fin 3) :
    Bridge.Faithful Tma.localShared (candidate a b) (histories a b) dataCluster (regionPlan (tmaWork a b tile))
      ⟨tmaPrepared,fun _ => False⟩ := by
  apply prepared_region_faithful
  intro sid st hg
  cases sid with
  | zero => simp only [tmaPrepared,List.getElem?_cons_zero,Option.some.injEq] at hg; subst st; rfl
  | succ sid => simp [tmaPrepared] at hg

theorem native_region_reclaim_guard (a b) (tile : Fin 3) {next target region control node loc mode}
    (hs : Bridge.Steps HopperStage.block Tma.localShared (candidate a b) (histories a b) dataCluster (regionPlan (nativeWork a b tile))
      ⟨nativePrepared,fun _ => False⟩ next)
    (hu : Use Tma.localShared Access.globalDescriptor (candidate a b) (nativeWork a b tile) control node loc mode)
    (hp : ¬next.done control) (ht : nativeLayout tile target = some region) (hl : region.Contains loc) :
    Ptx.Async.reclaim next.protocol target = .error .outstandingLoan :=
  Regions.pending_region_reclaim_rejected (native_layout_separated tile) (native_bindings_mapped _ _)
    (native_region_coverage (family a b) (source a b) tile tile.isLt)
    (Regions.borrowed_steps (native_prepared_borrowed _ _) hs)
    (Bridge.steps_faithful (native_initial_faithful a b tile) hs) (Bridge.steps_reached Reached.empty hs) rfl hu hp ht hl

theorem tma_region_reclaim_guard (a b) (tile : Fin 3) {next target region control node loc mode}
    (hs : Bridge.Steps HopperStage.block Tma.localShared (candidate a b) (histories a b) dataCluster (regionPlan (tmaWork a b tile))
      ⟨tmaPrepared,fun _ => False⟩ next)
    (hu : Use Tma.localShared Access.globalDescriptor (candidate a b) (tmaWork a b tile) control node loc mode)
    (hp : ¬next.done control) (ht : tmaALayout 3 tile target = some region) (hl : region.Contains loc) :
    Ptx.Async.reclaim next.protocol target = .error .outstandingLoan := by
  have hd := retry_data_descriptors a b 3 HopperRetryDataMemoryTests.schedule (by decide) (by decide)
  exact Regions.pending_region_reclaim_rejected (tma_a_layout_separated 3 tile) (tma_a_bindings_mapped _ _ _)
    (tma_a_region_coverage (family a b) (source a b) hd (by decide) tile tile.isLt)
    (Regions.borrowed_steps (tma_prepared_borrowed _ _ _) hs)
    (Bridge.steps_faithful (tma_initial_faithful a b tile) hs) (Bridge.steps_reached Reached.empty hs) rfl hu hp ht hl

theorem aliased_regions_rejected (tile : Nat) :
    ¬Regions.Separated (fun bid => [regionA tile,regionA tile][bid]?) := by
  intro hsep
  have hmem : (regionA tile).Contains (regionA tile).base := ⟨rfl,Nat.le_refl _,by dsimp [regionA]; omega⟩
  exact hsep 0 1 _ _ rfl rfl (by decide) _ hmem hmem

theorem undersized_region_rejected (work tile) :
    ¬Regions.Mapped (fun bid => [({base := (regionA tile).base,bytes := 1} : Regions.Region),regionB tile][bid]?)
      (regionPlan work) (nativeBindings work tile) := by
  intro hm
  have h := (hm ⟨work,⟨0,1⟩,0,.read,regionA tile⟩ (by simp [nativeBindings])).1
  have hh := congrArg (fun value => value.map Regions.Region.bytes) h
  simp [regionA] at hh

theorem missing_write_permission_rejected (a b) (tile : Fin 3) :
    ¬Regions.Covers Tma.localShared Access.globalDescriptor (candidate a b) (fun work => work = tmaWork a b tile)
      ((tmaABindings (tmaWork a b tile) 3 tile).map (fun binding => {binding with mode := .read})) := by
  intro hc
  have hd := retry_data_descriptors a b 3 HopperRetryDataMemoryTests.schedule (by decide) (by decide)
  have hl := retry_transfer_a_location (family a b) (source a b) hd tile tile.isLt (0 : Fin 2048)
  have hu := source_tma_write_use (descriptor := Access.globalDescriptor) (source a b) hl
  obtain ⟨binding,hmem,_,hmode,_⟩ := hc _ _ _ _ _ rfl hu
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp hmem
  cases hmode

theorem omitted_descriptor_rejected (a b) (tile : Fin 3) :
    ¬Regions.Covers Tma.localShared Access.globalDescriptor (candidate a b) (fun work => work = tmaWork a b tile)
      (tmaABindings (tmaWork a b tile) 3 tile).tail := by
  intro hc
  have hu := HopperCompletionBridgeTests.actual_descriptor_use a b tile 0
  obtain ⟨binding,hmem,_,_,hregion⟩ := hc _ _ _ _ _ rfl hu
  simp only [tmaABindings,List.tail_cons,List.mem_cons,List.not_mem_nil,or_false] at hmem
  rcases hmem with rfl | rfl
  · have hh := hregion.2.1
    norm_num [regionInputA,Access.globalDescriptor,Location.add] at hh
  · have hh := hregion.1
    simp [regionA,Access.globalDescriptor,Location.add] at hh

def nativeFirst : Ptx.Async.State := {nativePrepared with streams := [⟨2,1,[.use 1],[]⟩]}
def nativeComplete : Ptx.Async.State := {nativePrepared with streams := [⟨2,2,[],[]⟩]}
def nativeReturned : Ptx.Async.State := {nativeComplete with buffers := [⟨17,true,[]⟩,⟨17,true,[]⟩]}
def nativeReused : Ptx.Async.State := {nativeReturned with buffers := [⟨99,true,[]⟩,⟨17,true,[]⟩]}
def tmaFirst : Ptx.Async.State := {tmaPrepared with streams := [⟨2,1,[.copy 1 2],[]⟩]}
def tmaComplete : Ptx.Async.State := {tmaPrepared with
  streams := [⟨2,2,[],[]⟩]
  buffers := [⟨0,true,[⟨⟨0,1⟩,.read⟩]⟩,⟨17,true,[⟨⟨0,2⟩,.read⟩]⟩,⟨17,true,[⟨⟨0,2⟩,.write⟩]⟩]}
def tmaReturned : Ptx.Async.State := {tmaComplete with buffers := [⟨0,true,[]⟩,⟨17,true,[]⟩,⟨17,true,[]⟩]}
def tmaReused : Ptx.Async.State := {tmaReturned with buffers := [⟨0,true,[]⟩,⟨17,true,[]⟩,⟨99,true,[]⟩]}

theorem native_complete_region_run (a b) (tile : Fin 3) :
    Bridge.Steps HopperStage.block Tma.localShared (candidate a b) (histories a b) dataCluster (regionPlan (nativeWork a b tile))
      ⟨nativePrepared,fun _ => False⟩ ⟨nativeReused,Present (candidate a b)⟩ := by
  have hc := HopperProgressTests.actual_native_complete a b tile
  apply Bridge.steps_trans (Bridge.prefix_execution nativePrepared (HopperProgressTests.actual_full_prefix a b))
  refine .next (.device (sid := 0) (st := ⟨2,0,[.use 0,.use 1],[]⟩) ?_ (next := nativeFirst) ?_ ?_) ?_
  · change Ptx.Async.getStream nativePrepared 0 = .ok _; decide
  · change Ptx.Async.deviceStep nativePrepared 0 = .ok nativeFirst; decide
  · intro actual hm; have he : nativeWork a b tile = actual := by simpa [regionPlan] using hm
    subst actual; exact hc
  · refine .next (.device (sid := 0) (st := ⟨2,1,[.use 1],[]⟩) ?_ (next := nativeComplete) ?_ ?_) ?_
    · change Ptx.Async.getStream nativeFirst 0 = .ok _; decide
    · change Ptx.Async.deviceStep nativeFirst 0 = .ok nativeComplete; decide
    · intro actual hm; have he : nativeWork a b tile = actual := by simpa [regionPlan] using hm
      subst actual; exact hc
    · refine .next (.host (.acquire 2) (next := nativeReturned) ?_) (.next (.host (.write 0 99) ?_) (.refl _))
      · change Ptx.Async.await nativeComplete 2 = .ok nativeReturned; decide
      · change Ptx.Async.hostWrite nativeReturned 0 99 = .ok nativeReused; decide

theorem tma_complete_region_run (a b) (tile : Fin 3) :
    Bridge.Steps HopperStage.block Tma.localShared (candidate a b) (histories a b) dataCluster (regionPlan (tmaWork a b tile))
      ⟨tmaPrepared,fun _ => False⟩ ⟨tmaReused,Present (candidate a b)⟩ := by
  have hc := HopperProgressTests.actual_tma_complete a b tile
  apply Bridge.steps_trans (Bridge.prefix_execution tmaPrepared (HopperProgressTests.actual_full_prefix a b))
  refine .next (.device (sid := 0) (st := ⟨2,0,[.use 0,.copy 1 2],[]⟩) ?_ (next := tmaFirst) ?_ ?_) ?_
  · change Ptx.Async.getStream tmaPrepared 0 = .ok _; decide
  · change Ptx.Async.deviceStep tmaPrepared 0 = .ok tmaFirst; decide
  · intro actual hm; have he : tmaWork a b tile = actual := by simpa [regionPlan] using hm
    subst actual; exact hc
  · refine .next (.device (sid := 0) (st := ⟨2,1,[.copy 1 2],[]⟩) ?_ (next := tmaComplete) ?_ ?_) ?_
    · change Ptx.Async.getStream tmaFirst 0 = .ok _; decide
    · change Ptx.Async.deviceStep tmaFirst 0 = .ok tmaComplete; decide
    · intro actual hm; have he : tmaWork a b tile = actual := by simpa [regionPlan] using hm
      subst actual; exact hc
    · refine .next (.host (.acquire 2) (next := tmaReturned) ?_) (.next (.host (.write 2 99) ?_) (.refl _))
      · change Ptx.Async.await tmaComplete 2 = .ok tmaReturned; decide
      · change Ptx.Async.hostWrite tmaReturned 2 99 = .ok tmaReused; decide

end
end Ptx.HopperRegionLoanTests
