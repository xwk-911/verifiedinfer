import Ptx.Kernels.HopperDoubleBufferProgress
import Ptx.Tests.HopperCompletionBridge

/-! Complete coupled positive runs on the admitted data GEMM family. The
prepared abstract buffers are logical lifetime clients, not claims of physical
allocation/command or scalar-value/byte-map correspondence. -/
namespace Ptx.HopperProgressTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section

abbrev family := HopperCompletionBridgeTests.family
abbrev candidate := HopperCompletionBridgeTests.candidate
abbrev histories := HopperCompletionBridgeTests.histories
abbrev source := HopperCompletionBridgeTests.source
abbrev nativeWork := HopperCompletionBridgeTests.nativeWork
abbrev prepared := HopperCompletionBridgeTests.prepared
abbrev plan := HopperCompletionBridgeTests.plan
abbrev start := HopperCompletionBridgeTests.start

theorem actual_full_prefix (a : TileA) (b : TileB) : Reached HopperStage.block (candidate a b) (histories a b) (Present (candidate a b)) :=
  retry_data_full_prefix a b 3 HopperRetryDataMemoryTests.schedule (by decide) (by decide)

def beforeNative (a : TileA) (b : TileB) (tile : Fin 3) (operand : Wgmma.OperandByte) : Cut := fun node =>
  Present (candidate a b) node ∧ retryUnifiedRank (family a b) node < retryUnifiedRank (family a b) (.operand ((family a b).mmaId tile 0) operand)

theorem actual_native_cut_reached (a : TileA) (b : TileB) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    Reached HopperStage.block (candidate a b) (histories a b) (beforeNative a b tile operand) := by
  have he := HopperRetryDataMemoryTests.positive_joint_components a b
  exact retry_family_rank_prefix (family a b) (by decide) (by decide) he.1.source he.1.histories_valid _

theorem unfinished_native_in_reachable_cut (a : TileA) (b : TileB) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    ¬Completed Tma.localShared (candidate a b) (histories a b) dataCluster (beforeNative a b tile operand) (nativeWork a b tile) :=
  pending_use_not_completed (reached_valid (actual_native_cut_reached a b tile operand)).1
    (HopperCompletionBridgeTests.actual_native_use a b tile operand) (fun h => Nat.lt_irrefl _ h.2)

theorem actual_native_complete (a : TileA) (b : TileB) (tile : Fin 3) :
    Completed Tma.localShared (candidate a b) (histories a b) dataCluster (Present (candidate a b)) (nativeWork a b tile) := by
  apply HopperCompletionBridgeTests.native_completion_certificate a b tile (0 : Wgmma.Lane)
  simp only [Present,Tma.Present,Hopper.Candidate.Present,Unified.view_eventAt,
    family_native_wait_at (family a b) (source a b) (by decide) tile tile.isLt 0,Option.map_some,Option.isSome_some]

theorem actual_tma_complete (a : TileA) (b : TileB) (tile : Fin 3) :
    Completed Tma.localShared (candidate a b) (histories a b) dataCluster (Present (candidate a b)) (.tma ((family a b).copyAId tile)) := by
  apply HopperCompletionBridgeTests.tma_completion_certificate a b tile (0 : Wgmma.Lane)
  simp only [Present,Tma.Present,Hopper.Candidate.Present,Unified.view_eventAt,
    family_wait_at (family a b) (source a b) tile tile.isLt 0,Option.map_some,Option.isSome_some]

def completedProtocol : Ptx.Async.State := {prepared with streams := [{issued := 1,completed := 1}]}
def acquiredProtocol : Ptx.Async.State := {completedProtocol with buffers := [{value := 17}]}
def reclaimedProtocol : Ptx.Async.State := {acquiredProtocol with buffers := [{value := 17,alive := false}]}

theorem protocol_device_succeeds : Ptx.Async.deviceStep prepared 0 = .ok completedProtocol := by decide
theorem protocol_acquire_succeeds : Ptx.Async.await completedProtocol 1 = .ok acquiredProtocol := by decide
theorem protocol_reclaim_succeeds : Ptx.Async.reclaim acquiredProtocol 0 = .ok reclaimedProtocol := by decide

theorem coupled_complete_and_reclaim {a b work}
    (hc : Completed Tma.localShared (candidate a b) (histories a b) dataCluster (Present (candidate a b)) work) :
    Bridge.Steps HopperStage.block Tma.localShared (candidate a b) (histories a b) dataCluster (plan work)
      start ⟨reclaimedProtocol,Present (candidate a b)⟩ := by
  apply Bridge.steps_trans (Bridge.prefix_execution prepared (actual_full_prefix a b))
  refine .next (.device (sid := 0) (st := ⟨1,0,[.use 0],[]⟩)
    (by change Ptx.Async.getStream prepared 0 = .ok ⟨1,0,[.use 0],[]⟩; decide) protocol_device_succeeds ?_) ?_
  · intro actual hm
    have heq : work = actual := by simpa only [plan,HopperCompletionBridgeTests.plan,ite_true,Option.some.injEq] using hm
    subst actual
    exact hc
  · exact .next (.host (.acquire 1) protocol_acquire_succeeds)
      (.next (.host (.reclaim 0) protocol_reclaim_succeeds) (.refl _))

theorem native_coupled_reclaim_run (a : TileA) (b : TileB) (tile : Fin 3) :
    Bridge.Steps HopperStage.block Tma.localShared (candidate a b) (histories a b) dataCluster (plan (nativeWork a b tile))
      start ⟨reclaimedProtocol,Present (candidate a b)⟩ := coupled_complete_and_reclaim (actual_native_complete a b tile)

theorem tma_coupled_reclaim_run (a : TileA) (b : TileB) (tile : Fin 3) :
    Bridge.Steps HopperStage.block Tma.localShared (candidate a b) (histories a b) dataCluster (plan (.tma ((family a b).copyAId tile)))
      start ⟨reclaimedProtocol,Present (candidate a b)⟩ := coupled_complete_and_reclaim (actual_tma_complete a b tile)

theorem native_run_faithful (a : TileA) (b : TileB) (tile : Fin 3) :
    Bridge.Faithful Tma.localShared (candidate a b) (histories a b) dataCluster (plan (nativeWork a b tile))
      ⟨reclaimedProtocol,Present (candidate a b)⟩ :=
  Bridge.steps_faithful (HopperCompletionBridgeTests.prepared_plan_faithful a b (nativeWork a b tile)) (native_coupled_reclaim_run a b tile)

theorem prepared_protocol_invariant : Ptx.Async.Invariant prepared := by
  let issued := {prepared with events := prepared.events.reverse}
  have hrun : Ptx.Async.run (Ptx.Async.initial 1 [17]) [.record 0 0,.use 0 0,.record 0 1] = .ok issued := by decide
  have hi := Ptx.Async.steps_invariant (Ptx.Async.initial_invariant 1 [17]) (Ptx.Async.run_sound hrun)
  exact Ptx.Async.invariant_extend hi rfl (by intro bid b hb; exact ⟨b,hb,rfl,fun _ h => h⟩)

theorem native_run_protocol_invariant (a : TileA) (b : TileB) (tile : Fin 3) : Ptx.Async.Invariant reclaimedProtocol :=
  Bridge.steps_protocol_invariant prepared_protocol_invariant (native_coupled_reclaim_run a b tile)

theorem reclaimed_buffer_has_no_loans : reclaimedProtocol.buffers = [⟨17,false,[]⟩] := by decide

def ghost : Unified.ControlNode := .base (.source ⟨⟨.zero,.zero⟩,0⟩)

theorem ghost_prefix_rejected :
    ¬Reached HopperStage.block (⟨[]⟩ : Unified.Candidate) (fun _ => []) (fun node => node = ghost) := by
  intro hr
  have hp := (reached_valid hr).2 ghost rfl
  simp [ghost,Present,Tma.Present,Hopper.Candidate.Present,Unified.view_eventAt,
    Unified.Candidate.eventAt,Unified.Candidate.traceAt] at hp

end
end Ptx.HopperProgressTests
