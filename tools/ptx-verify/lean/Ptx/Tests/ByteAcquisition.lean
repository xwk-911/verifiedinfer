import Ptx.Iris.ByteAcquisition
import Ptx.Tests.ByteRetirement

/-! Complete available→claim→retire lifetimes for actual source nodes. This
still proves authority metadata, not GPU byte-value or runtime refinement. -/
namespace Ptx.ByteAcquisitionTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
open Ptx.ByteRetirementTests
noncomputable section

def barrierStart (slot : Stage) : ByteAuthority.State :=
  ⟨(barrierHeld slot).coupled,ByteAuthority.Footprint.pool (barrierDemands slot)⟩
def barrierEnd (slot : Stage) := ByteAuthority.retired (ByteAuthority.Footprint.granted (barrierStart slot) (barrierNode slot) (barrierDemands slot)) (barrierNode slot)

theorem barrier_pool_allocates_every_byte (slot : Stage) : ByteAuthority.Footprint.Available (barrierStart slot) (barrierDemands slot) :=
  ByteAuthority.Footprint.pool_available _ _
theorem barrier_pool_initially_available (slot : Stage) :
    ∀ k owner, get? (barrierStart slot).bytes k = some owner → owner = .available := ByteAuthority.Footprint.pool_owners_available _

theorem actual_barrier_acquisition_succeeds (slot : Stage) :
    ByteAuthority.Footprint.acquire HopperStage.block ByteAuthorityTests.candidate zeroHistories (barrierNode slot) (barrierDemands slot) (barrierStart slot) =
      .ok (ByteAuthority.Footprint.granted (barrierStart slot) (barrierNode slot) (barrierDemands slot)) :=
  ByteAuthority.Footprint.acquire_succeeds (ByteAuthorityTests.actual_rank_cut_ready slot) (barrier_footprint_sound slot) (barrier_distinct slot) (barrier_pool_allocates_every_byte slot)

theorem actual_barrier_cycle_run (slot : Stage) :
    IrisExecution.run (ByteAuthorityHeap.transition ByteAuthorityTests.ctx) (ByteAuthorityHeap.cycleActions (barrierNode slot) (barrierDemands slot))
      (barrierStart slot) = .ok (barrierEnd slot) := by
  rw [ByteAuthorityHeap.cycle_run]
  exact ByteAuthority.Footprint.cycle_succeeds (barrier_pool_initially_available slot) (ByteAuthorityTests.actual_rank_cut_ready slot)
    (barrier_footprint_sound slot) (barrier_footprint_complete slot) (barrier_distinct slot) (barrier_pool_allocates_every_byte slot)

theorem barrier_cycle_is_nine_actions (slot : Stage) :
    (ByteAuthorityHeap.cycleActions (barrierNode slot) (barrierDemands slot)).length = 9 := by
  simp [ByteAuthorityHeap.cycleActions,ByteAuthorityHeap.acquisitionActions,barrierDemands,ByteAuthority.Footprint.span]

theorem barrier_cycle_restores_pool (slot : Stage) : (barrierEnd slot).bytes = (barrierStart slot).bytes :=
  ByteAuthority.Footprint.finished_bytes_restore (barrier_pool_initially_available slot) (ByteAuthorityTests.actual_rank_cut_ready slot)
    (barrier_footprint_sound slot) (barrier_footprint_complete slot) (barrier_distinct slot) (barrier_pool_allocates_every_byte slot)

theorem no_source_advance_during_acquisition (slot : Stage) :
    (ByteAuthority.Footprint.granted (barrierStart slot) (barrierNode slot) (barrierDemands slot)).coupled = (barrierStart slot).coupled :=
  ByteAuthority.Footprint.granted_coupled _ _ _

theorem source_node_completes_only_at_end (slot : Stage) : (barrierEnd slot).coupled.done (barrierNode slot) := Or.inr rfl

theorem barrier_cycle_has_actual_permission_steps (slot : Stage) :
    ByteAuthority.Steps HopperStage.block ByteAuthorityTests.candidate zeroHistories dataCluster (fun _ => none) (barrierStart slot) (barrierEnd slot) :=
  ByteAuthority.Footprint.cycle_steps ((ByteAuthorityHeap.cycle_run ByteAuthorityTests.ctx (barrierNode slot) (barrierDemands slot)
    (barrierStart slot)).symm.trans (actual_barrier_cycle_run slot))

theorem barrier_cycle_projects_to_source (slot : Stage) :
    Bridge.Steps HopperStage.block Tma.localShared ByteAuthorityTests.candidate zeroHistories dataCluster (fun _ => none)
      (barrierStart slot).coupled (barrierEnd slot).coupled := ByteAuthority.steps_projects (barrier_cycle_has_actual_permission_steps slot)

theorem barrier_cycle_native_iris_wp [ByteAuthorityHeap.GS] (slot : Stage) (frame : IProp ByteAuthorityHeap.GF) :
    ByteAuthorityHeap.control (barrierStart slot) ∗ ByteAuthorityHeap.freePoints (barrierDemands slot) ∗ frame ⊢
      WP (ByteAuthorityHeap.script ByteAuthorityTests.ctx (ByteAuthorityHeap.cycleActions (barrierNode slot) (barrierDemands slot)))
        {{ value, ⌜value = .ok (barrierEnd slot)⌝ ∗ ByteAuthorityHeap.control (barrierEnd slot) ∗ ByteAuthorityHeap.freePoints (barrierDemands slot) ∗ frame }} :=
  ByteAuthorityHeap.cycle_wp_available ByteAuthorityTests.ctx _ _ _ frame (barrier_pool_initially_available slot)
    (ByteAuthorityTests.actual_rank_cut_ready slot) (barrier_footprint_sound slot) (barrier_footprint_complete slot)
    (barrier_distinct slot) (barrier_pool_allocates_every_byte slot)

theorem barrier_cycle_closed_adequate (slot : Stage) :
    adequate .NotStuck (ByteAuthorityHeap.script ByteAuthorityTests.ctx (ByteAuthorityHeap.cycleActions (barrierNode slot) (barrierDemands slot)))
      (barrierStart slot) (fun value _ => value = .ok (barrierEnd slot)) :=
  ByteAuthorityHeap.cycle_adequate ByteAuthorityTests.ctx _ _ _
    (ByteAuthority.Footprint.available_pool_supported (barrier_pool_initially_available slot))
    (ByteAuthority.available_pool_active (barrier_pool_initially_available slot))
    (ByteAuthorityTests.actual_rank_cut_ready slot) (barrier_footprint_sound slot) (barrier_footprint_complete slot)
    (barrier_distinct slot) (barrier_pool_allocates_every_byte slot)

theorem duplicate_request_cannot_acquire (ctx : ByteAuthorityHeap.Context) (state : ByteAuthority.State) (node : Unified.ControlNode)
    (demand : ByteAuthority.Footprint.Demand) :
    ∀ next, ByteAuthority.Footprint.acquire ctx.block ctx.candidate ctx.histories node [demand,demand] state ≠ .ok next := by
  intro next hs
  have hd := ByteAuthority.Footprint.acquire_requires_distinct hs
  simp [ByteAuthority.Footprint.Distinct,ByteAuthority.Footprint.keys] at hd

def missingStart (slot : Stage) : ByteAuthority.State :=
  {barrierStart slot with bytes := ByteAuthority.Footprint.pool (ByteAuthority.Footprint.span (dataGate slot) 7 .write)}

theorem missing_last_byte_cannot_acquire (slot : Stage) :
    ∀ next, ByteAuthority.Footprint.acquire HopperStage.block ByteAuthorityTests.candidate zeroHistories (barrierNode slot) (barrierDemands slot) (missingStart slot) ≠ .ok next := by
  intro next hs
  have ha := ByteAuthority.Footprint.acquire_requires_available hs
  have hl := ha ⟨(dataGate slot).add 7,.write⟩ (ByteAuthority.Footprint.span_member _ _ _ ⟨7,by decide⟩)
  have hn : ByteAuthority.key ((dataGate slot).add 7) ∉ ByteAuthority.Footprint.keys (ByteAuthority.Footprint.span (dataGate slot) 7 .write) := by
    intro hm
    obtain ⟨demand,hm,he⟩ := List.mem_map.mp hm
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp hm
    have hloc := ByteAuthority.key_injective he
    have haddr := congrArg Location.address hloc
    change (dataGate slot).address+index.val = (dataGate slot).address+7 at haddr
    have hindex := Nat.add_left_cancel haddr
    have hi := index.isLt
    omega
  change get? (ByteAuthority.Footprint.pool (ByteAuthority.Footprint.span (dataGate slot) 7 .write)) (ByteAuthority.key ((dataGate slot).add 7)) = some .available at hl
  rw [ByteAuthority.Footprint.pool_lookup] at hl
  simp only [hn,ite_false] at hl
  cases hl

theorem missing_last_byte_script_cannot_succeed (slot : Stage) :
    ∀ next, IrisExecution.run (ByteAuthorityHeap.transition ByteAuthorityTests.ctx)
      (ByteAuthorityHeap.acquisitionActions (barrierNode slot) (barrierDemands slot)) (missingStart slot) ≠ .ok next := by
  intro next hs
  rw [ByteAuthorityHeap.acquisition_run] at hs
  exact missing_last_byte_cannot_acquire slot next hs

def frameLocation : Location := ⟨.global,4096⟩
def framedStart (slot : Stage) : ByteAuthority.State :=
  {barrierStart slot with bytes := insert (barrierStart slot).bytes (ByteAuthority.key frameLocation) .available}
def framedEnd (slot : Stage) := ByteAuthority.retired (ByteAuthority.Footprint.granted (framedStart slot) (barrierNode slot) (barrierDemands slot)) (barrierNode slot)

theorem framed_pool_available (slot : Stage) : ∀ k owner, get? (framedStart slot).bytes k = some owner → owner = .available := by
  intro k owner hg
  change get? (insert (barrierStart slot).bytes (ByteAuthority.key frameLocation) .available) k = some owner at hg
  by_cases he : ByteAuthority.key frameLocation = k
  · simpa only [get?_insert_eq he,Option.some.injEq] using hg.symm
  · exact barrier_pool_initially_available slot k owner (by simpa only [get?_insert_ne he] using hg)

theorem framed_demands_available (slot : Stage) : ByteAuthority.Footprint.Available (framedStart slot) (barrierDemands slot) := by
  intro demand hm
  change get? (insert (barrierStart slot).bytes (ByteAuthority.key frameLocation) .available) (ByteAuthority.key demand.location) = some .available
  by_cases he : ByteAuthority.key frameLocation = ByteAuthority.key demand.location
  · simp [get?_insert,he]
  · rw [get?_insert_ne he]
    exact barrier_pool_allocates_every_byte slot demand hm

theorem framed_byte_preserved_in_actual_cycle (slot : Stage) :
    get? (framedEnd slot).bytes (ByteAuthority.key frameLocation) = some .available := by
  have hb := ByteAuthority.Footprint.finished_bytes_restore (framed_pool_available slot) (ByteAuthorityTests.actual_rank_cut_ready slot)
    (barrier_footprint_sound slot) (barrier_footprint_complete slot) (barrier_distinct slot) (framed_demands_available slot)
  change get? (ByteAuthority.retired (ByteAuthority.Footprint.granted (framedStart slot) (barrierNode slot) (barrierDemands slot)) (barrierNode slot)).bytes (ByteAuthority.key frameLocation) = some .available
  change (ByteAuthority.retired (ByteAuthority.Footprint.granted (framedStart slot) (barrierNode slot) (barrierDemands slot)) (barrierNode slot)).bytes = (framedStart slot).bytes at hb
  rw [hb]
  simp [framedStart,get?_insert]

theorem native_cycle_frames_extra_byte [ByteAuthorityHeap.GS] (slot : Stage) :
    ByteAuthorityHeap.control (framedStart slot) ∗ ByteAuthorityHeap.freePoints (barrierDemands slot) ∗
      ByteAuthorityHeap.byte frameLocation (.own 1) .available ⊢
      WP (ByteAuthorityHeap.script ByteAuthorityTests.ctx (ByteAuthorityHeap.cycleActions (barrierNode slot) (barrierDemands slot)))
        {{ value, ⌜value = .ok (framedEnd slot)⌝ ∗ ByteAuthorityHeap.control (framedEnd slot) ∗ ByteAuthorityHeap.freePoints (barrierDemands slot) ∗
          ByteAuthorityHeap.byte frameLocation (.own 1) .available }} :=
  ByteAuthorityHeap.cycle_wp_available ByteAuthorityTests.ctx _ _ _ _ (framed_pool_available slot)
    (ByteAuthorityTests.actual_rank_cut_ready slot) (barrier_footprint_sound slot) (barrier_footprint_complete slot)
    (barrier_distinct slot) (framed_demands_available slot)

-- Real unsplit atomic source used by the RMW authorization regression.
theorem rmw_rich_lookup : rmwCandidate.eventAt AtomicMemoryTests.event =
    some (.base (.ampere (.ordinary (.rmw .gpu AtomicMemoryTests.base (Scalar.atomicAddBytes 0 1))))) := by rfl

theorem rmw_ready_from_empty : ByteAuthority.Ready .one rmwCandidate (fun _ => []) (fun _ => False) rmwNode := by
  refine ⟨?_,by simp,?_⟩
  · simp [Present,Tma.Present,Hopper.Candidate.Present,rmwNode,actual_rmw_source_lookup]
  · intro before he
    rcases he with hb | ha | hr | hi | hf
    · cases before with
      | base before =>
        change Tma.ControlEdge rmwCandidate.view (fun _ => []) before (.source AtomicMemoryTests.event) at hb
        rcases hb with hp | hc | hi | hr
        · cases before with
          | source left => exact (Nat.not_lt_zero _ hp.2.2.2).elim
          | descriptor _ | read _ _ | write _ _ | notify _ => cases hp
        · cases before <;> simp [Tma.CTAControl,Hopper.CTAControl,Hopper.Candidate.ctaTag,actual_rmw_source_lookup] at hc
        · cases hi
        · obtain ⟨loc,left,hl,_⟩ := hr; cases hl
      | arrival event => cases hb
      | operand issue operand => cases hb
    · cases before <;> simp [Unified.NativeArrival,rmwNode] at ha
    · cases before <;> simp [Unified.NativeRendezvous,Unified.NativeSync,Unified.Candidate.nativeSignatureAt,rmwNode,rmw_rich_lookup,Wgmma.eventSignature,Wgmma.collective] at hr
    · cases before <;> simp [Unified.NativeIssue,rmwNode] at hi
    · cases before with
      | base before => cases hf
      | arrival event => cases hf
      | operand issue operand =>
        obtain ⟨mark,groups,keep,before,after,query,hw,_⟩ := Unified.completed_has_actual_wait hf
        rw [rmw_rich_lookup] at hw
        cases hw

theorem rmw_footprint_actual_write_modes : ByteAuthority.Footprint.Sound rmwCandidate rmwNode rmwDemands := by
  intro demand hm
  obtain ⟨offset,rfl⟩ := List.mem_ofFn.mp hm
  refine ⟨.kernel,.kernel (.write (value := if offset.val = 0 then .bits (byte 1) else .bits (byte 0)) actual_rmw_source_lookup ?_)⟩
  fin_cases offset <;> rfl

def rmwCtx : ByteAuthorityHeap.Context := {block := .one,candidate := rmwCandidate,histories := fun _ => [] }
def rmwStart : ByteAuthority.State := ⟨⟨Ptx.Async.initial 0 [],fun _ => False⟩,ByteAuthority.Footprint.pool rmwDemands⟩
def rmwEnd := ByteAuthority.retired (ByteAuthority.Footprint.granted rmwStart rmwNode rmwDemands) rmwNode

theorem actual_rmw_cycle_run :
    IrisExecution.run (ByteAuthorityHeap.transition rmwCtx) (ByteAuthorityHeap.cycleActions rmwNode rmwDemands) rmwStart = .ok rmwEnd := by
  rw [ByteAuthorityHeap.cycle_run]
  exact ByteAuthority.Footprint.cycle_succeeds (ByteAuthority.Footprint.pool_owners_available _) rmw_ready_from_empty
    rmw_footprint_actual_write_modes rmw_footprint_complete rmw_one_write_grant_per_byte (ByteAuthority.Footprint.pool_available _ _)

theorem actual_rmw_cycle_closed_adequate :
    adequate .NotStuck (ByteAuthorityHeap.script rmwCtx (ByteAuthorityHeap.cycleActions rmwNode rmwDemands)) rmwStart
      (fun value _ => value = .ok rmwEnd) :=
  ByteAuthorityHeap.cycle_adequate rmwCtx _ _ _
    (ByteAuthority.Footprint.available_pool_supported (ByteAuthority.Footprint.pool_owners_available _))
    (ByteAuthority.available_pool_active (ByteAuthority.Footprint.pool_owners_available _)) rmw_ready_from_empty
    rmw_footprint_actual_write_modes rmw_footprint_complete rmw_one_write_grant_per_byte (ByteAuthority.Footprint.pool_available _ _)

theorem rmw_cycle_is_five_actions : (ByteAuthorityHeap.cycleActions rmwNode rmwDemands).length = 5 := by
  simp [ByteAuthorityHeap.cycleActions,ByteAuthorityHeap.acquisitionActions,rmwDemands,ByteAuthority.Footprint.span]

theorem actual_rmw_cycle_restores_pool : rmwEnd.bytes = rmwStart.bytes :=
  ByteAuthority.Footprint.finished_bytes_restore (ByteAuthority.Footprint.pool_owners_available _) rmw_ready_from_empty
    rmw_footprint_actual_write_modes rmw_footprint_complete rmw_one_write_grant_per_byte (ByteAuthority.Footprint.pool_available _ _)

theorem completed_source_node_cannot_be_claimed_again :
    ByteAuthority.claim .one rmwCandidate (fun _ => []) ⟨rmwNode,AtomicMemoryTests.base,.write⟩ rmwEnd = .error .unready :=
  ByteAuthority.claim_done_rejected (Or.inr rfl)

end
end Ptx.ByteAcquisitionTests
