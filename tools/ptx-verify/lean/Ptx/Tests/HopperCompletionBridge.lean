import Ptx.Hopper.CompletionBridge
import Ptx.Tests.HopperRetryDataMemory
import Ptx.Kernels.HopperDoubleBufferRetryArbitraryObservations

/-! Actual source-derived accesses on the independently admitted data GEMM
fixture, plus prepared-plan loan/counter regressions. Rank cuts test structural
completion obligations only; they are not asserted to be reachable GPU prefixes.
No physical allocation or CUDA-runtime correspondence is assumed or concluded.
-/
namespace Ptx.HopperCompletionBridgeTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section

abbrev family := HopperRetryDataMemoryTests.family
abbrev candidate := HopperRetryDataMemoryTests.candidate
abbrev source := HopperRetryDataMemoryTests.source
abbrev histories (a : TileA) (b : TileB) := retryHistories (family a b)
abbrev nativeWork (a : TileA) (b : TileB) (tile : Fin 3) := Work.native ((family a b).mmaId tile 0)

theorem actual_native_use (a : TileA) (b : TileB) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    Use Tma.localShared Access.globalDescriptor (candidate a b) (nativeWork a b tile)
      (.operand ((family a b).mmaId tile 0) operand) (retryNativeRead (family a b) tile operand)
      (retryNativeLocation (family a b) tile operand) .read :=
  .nativeRead (Unified.collective_representative (familyCollective (family a b) (source a b) tile tile.isLt))

theorem actual_descriptor_use (a : TileA) (b : TileB) (tile : Fin 3) (offset : Fin 128) :
    Use Tma.localShared Access.globalDescriptor (candidate a b) (.tma ((family a b).copyAId tile))
      (.base (.descriptor ((family a b).copyAId tile))) (.base (.tma (.descriptor ((family a b).copyAId tile))))
      ((Access.globalDescriptor ((family a b).copyAId tile).issue.thread 4096).add offset.val) .read := by
  have hc := family_copy_a_at (family a b) (source a b) tile tile.isLt
  have hu := Use.descriptor (resolve := Tma.localShared) (descriptor := Access.globalDescriptor) hc offset.isLt
  simpa only [reply_copy_a_descriptor_address] using hu

theorem actual_source_read_use (a : TileA) (b : TileB) (id offset loc)
    (hl : Tma.readLocation (candidate a b).view id offset = some loc) :
    Use Tma.localShared Access.globalDescriptor (candidate a b) (.tma id) (.base (.read id offset)) (.base (.tma (.read id offset))) loc .read :=
  source_tma_read_use (source a b) hl

theorem actual_source_write_use (a : TileA) (b : TileB) (id offset loc)
    (hl : Tma.writeLocation Tma.localShared (candidate a b).view id offset = some loc) :
    Use Tma.localShared Access.globalDescriptor (candidate a b) (.tma id) (.base (.write id offset)) (.base (.tma (.write id offset))) loc .write :=
  source_tma_write_use (source a b) hl

theorem native_completion_certificate (a : TileA) (b : TileB) (tile : Fin 3) (lane : Wgmma.Lane) (done : Cut)
    (hd : done (.base (.source ((family a b).nativeWaitId tile lane)))) :
    Completed Tma.localShared (candidate a b) (histories a b) dataCluster done (nativeWork a b tile) :=
  .native (retry_native_completed (family a b) (source a b) (by decide) tile tile.isLt lane) hd

theorem tma_completion_certificate (a : TileA) (b : TileB) (tile : Fin 3) (lane : Wgmma.Lane) (done : Cut)
    (hdone : done (.base (.source ((family a b).waitId tile lane)))) :
    Completed Tma.localShared (candidate a b) (histories a b) dataCluster done (.tma ((family a b).copyAId tile)) := by
  have hc := family_copy_a_at (family a b) (source a b) tile tile.isLt
  have hd := (retry_data_descriptors a b 3 HopperRetryDataMemoryTests.schedule (by decide) (by decide)) _ _ hc
  rw [reply_copy_a_descriptor_address] at hd
  have hv : (replyCopyA 3 ((family a b).replies 0) ((family a b).schedules 0) tile).descriptor = aView 65536 3 := by
    simpa only [dataMaps,ite_true,show ¬(4096 = 4224) from by decide,ite_false,Option.some.injEq] using hd.symm
  have hp : 0 < (replyCopyA 3 ((family a b).replies 0) ((family a b).schedules 0) tile).descriptor.bytes := by rw [hv]; decide
  have he := HopperRetryDataMemoryTests.positive_joint_components a b
  exact .tma hc hp (arbitrary_histories_completion_observations (family a b) (by decide) he.1 he.2.1 tile tile.isLt lane).1 hdone

theorem rank_cut_before_native_use_rejects_completion (a : TileA) (b : TileB) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    ¬Completed Tma.localShared (candidate a b) (histories a b) dataCluster
      (fun node => retryUnifiedRank (family a b) node < retryUnifiedRank (family a b) (.operand ((family a b).mmaId tile 0) operand))
      (nativeWork a b tile) :=
  pending_use_not_completed
    (rank_cut_closed _ (fun _ _ => retry_unified_edge_order (family a b) (by decide) (by decide) (source a b)) _)
    (actual_native_use a b tile operand) (Nat.lt_irrefl _)

def loan : Ptx.Async.Loan := ⟨⟨0,1⟩,.read⟩
def prepared : Ptx.Async.State := {
  streams := [{issued := 1,queue := [.use 0]}]
  buffers := [{value := 17,loans := [loan]}]
  events := [⟨0,⟨0,0⟩⟩,⟨1,⟨0,1⟩⟩]
}
def plan (work : Work) : Bridge.Plan := fun ticket => if ticket = ⟨0,1⟩ then some work else none
def start : Bridge.State := ⟨prepared,fun _ => False⟩
def afterOld : Ptx.Async.State := prepared

theorem prepared_plan_faithful (a : TileA) (b : TileB) (work : Work) :
    Bridge.Faithful Tma.localShared (candidate a b) (histories a b) dataCluster (plan work) start := by
  apply Bridge.prepared_faithful
  · intro sid st hg
    cases sid with
    | zero => simp only [prepared,List.getElem?_cons_zero,Option.some.injEq] at hg; subst st; rfl
    | succ sid => simp [prepared] at hg
  · intro ticket work hm
    simp only [plan] at hm
    split at hm
    · subst ticket; decide
    · cases hm

theorem native_pending_blocks_current_acquire (a : TileA) (b : TileB) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    ∀ next, Ptx.Async.await prepared 1 ≠ .ok next :=
  Bridge.pending_use_blocks_acquire (block := HopperStage.block) (frontier := ⟨0,1⟩) (prepared_plan_faithful a b (nativeWork a b tile)) Reached.empty
    (by decide) (ticket := ⟨0,1⟩) (by decide) (by simp [plan]) (actual_native_use a b tile operand) (fun h => h)

theorem descriptor_pending_blocks_current_acquire (a : TileA) (b : TileB) (tile : Fin 3) (offset : Fin 128) :
    ∀ next, Ptx.Async.await prepared 1 ≠ .ok next :=
  Bridge.pending_use_blocks_acquire (block := HopperStage.block) (frontier := ⟨0,1⟩) (prepared_plan_faithful a b (.tma ((family a b).copyAId tile))) Reached.empty
    (by decide) (ticket := ⟨0,1⟩) (by decide) (by simp [plan]) (actual_descriptor_use a b tile offset) (fun h => h)

theorem old_event_can_be_acquired : Ptx.Async.await prepared 0 = .ok afterOld := by decide
theorem old_event_keeps_future_loan : Ptx.Async.getBuffer afterOld 0 = .ok ⟨17,true,[loan]⟩ := by decide

theorem pending_native_use_keeps_loan_after_old_event (a : TileA) (b : TileB) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    loan ∈ ((⟨17,true,[loan]⟩ : Ptx.Async.Buffer).loans) :=
  Bridge.pending_use_keeps_loan (block := HopperStage.block) (before := ⟨17,true,[loan]⟩)
    (prepared_plan_faithful a b (nativeWork a b tile)) Reached.empty old_event_can_be_acquired
    (bid := 0) (by decide) old_event_keeps_future_loan (by decide) (by simp [plan,loan])
    (actual_native_use a b tile operand) (fun h => h)

theorem reclaim_after_old_event_rejected : Ptx.Async.reclaim afterOld 0 = .error .outstandingLoan := by decide
theorem write_after_old_event_rejected : Ptx.Async.hostWrite afterOld 0 99 = .error .outstandingLoan := by decide

theorem abstract_counter_alone_would_advance : ∃ next, Ptx.Async.deviceStep prepared 0 = .ok next := by
  exact ⟨{prepared with streams := [{issued := 1,completed := 1}]},by decide⟩

theorem pending_native_rejects_device_completion_guard (a : TileA) (b : TileB) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    ¬(∀ work, plan (nativeWork a b tile) ⟨0,1⟩ = some work →
      Completed Tma.localShared (candidate a b) (histories a b) dataCluster start.done work) := by
  intro h
  exact pending_use_not_completed (reached_valid (Reached.empty (block := HopperStage.block))).1
    (actual_native_use a b tile operand) (fun h => h) (h _ (by simp [plan]))

end
end Ptx.HopperCompletionBridgeTests
