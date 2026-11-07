import Ptx.Iris.ByteRetirement
import Ptx.Hopper.ByteSourceFootprints
import Ptx.Tests.ByteAuthority
import Ptx.Tests.AtomicMemory

/-! Non-vacuous real RMW source trace and complete eight-byte mbarrier retirement.
Authority is metadata; this adds no GPU data-effect or runtime execution claim. -/
namespace Ptx.ByteRetirementTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section


-- A real source RMW, lifted through the existing Hopper/WGMMA interpreter.
def rmwCode : List Hopper.Instr := [.ampere (.scalar (.atomAddU32 "%r" {base := .imm 64} (.imm 1))),.ampere (.scalar (.integer .ret))]
def rmwTrace : Unified.ThreadTrace := {
  id := AtomicMemoryTests.id
  oracle := {base := {ampere := {scalar := fun _ => .integer 0,bytes := fun _ => [] },wait := fun _ => false}}
  count := 2
  final := {base := {scalar := {core := AtomicMemoryTests.trace.final}},ledger := {dirty := ["%r"] } }
  events := [.base (.ampere (.ordinary (.rmw .gpu AtomicMemoryTests.base (Scalar.atomicAddBytes 0 1))))]
}
def rmwCandidate : Unified.Candidate := ⟨[rmwTrace]⟩
def rmwNode : Unified.ControlNode := .base (.source AtomicMemoryTests.event)
def rmwDemands := ByteAuthority.Footprint.span AtomicMemoryTests.base 4 .write

theorem actual_rmw_source_run : Unified.Produced rmwCode [] .one rmwTrace := by rfl

theorem actual_rmw_source_lookup : rmwCandidate.view.eventAt AtomicMemoryTests.event =
    some (.ampere (.ordinary (.rmw .gpu AtomicMemoryTests.base (Scalar.atomicAddBytes 0 1)))) := by rfl

theorem full_write_authorizes_rmw_read : ByteAuthority.Authorizes .write .read := ByteAuthority.write_authorizes _
theorem full_write_authorizes_rmw_write : ByteAuthority.Authorizes .write .write := ByteAuthority.write_authorizes _
theorem read_authority_cannot_write : ¬ByteAuthority.Authorizes .read .write := ByteAuthority.read_cannot_authorize_write

theorem actual_rmw_first_byte_read : ByteAuthority.Uses rmwCandidate rmwNode AtomicMemoryTests.base .read :=
  ⟨.kernel,.kernel (.read actual_rmw_source_lookup (by rfl))⟩
theorem actual_rmw_first_byte_write : ByteAuthority.Uses rmwCandidate rmwNode AtomicMemoryTests.base .write :=
  ⟨.kernel,.kernel (.write actual_rmw_source_lookup (by rfl))⟩

theorem rmw_use_bounds {loc mode} (hu : ByteAuthority.Uses rmwCandidate rmwNode loc mode) :
    loc.space = .global ∧ 64 ≤ loc.address ∧ loc.address < 68 := by
  have hx := ByteAuthority.Footprint.ordinary_source_uses actual_rmw_source_lookup hu
  cases mode <;> obtain ⟨value,hv⟩ := hx
  all_goals
    have hb := Ptx.Event.payloadByte_bounds hv
    change AddressSpace.global = loc.space ∧ 64 ≤ loc.address ∧ loc.address < 64+4 at hb
    exact ⟨hb.1.symm,hb.2⟩

theorem rmw_footprint_complete : ByteAuthority.Footprint.Covers rmwCandidate rmwNode rmwDemands := by
  intro loc mode hu
  obtain ⟨hs,hlo,hhi⟩ := rmw_use_bounds hu
  let offset : Fin 4 := ⟨loc.address-64,by omega⟩
  refine ⟨⟨AtomicMemoryTests.base.add offset.val,.write⟩,ByteAuthority.Footprint.span_member _ _ _ offset,?_,ByteAuthority.write_authorizes _⟩
  cases loc with
  | mk space address =>
    simp only [AtomicMemoryTests.base,Location.add,Location.mk.injEq]
    refine ⟨hs.symm,?_⟩
    change 64 ≤ address at hlo
    change 64+(address-64) = address
    omega

theorem rmw_one_write_grant_per_byte : ByteAuthority.Footprint.Distinct rmwDemands := ByteAuthority.Footprint.span_distinct _ _ _

def rmwHeld : ByteAuthority.State := ⟨⟨Ptx.Async.initial 0 [],fun _ => False⟩,ByteAuthority.Footprint.holding rmwNode rmwDemands⟩
theorem rmw_all_demands_held : ByteAuthority.Footprint.Held rmwHeld rmwNode rmwDemands := ByteAuthority.Footprint.holding_held _ _ rmw_one_write_grant_per_byte

theorem rmw_read_and_write_both_authorized : ByteAuthority.AllHeld rmwCandidate rmwHeld rmwNode :=
  ByteAuthority.Footprint.all_held rmw_footprint_complete rmw_all_demands_held

theorem actual_rmw_source_complete : Unified.Complete rmwCandidate := by
  intro trace ht
  have heq : trace = rmwTrace := by simpa only [rmwCandidate,List.mem_singleton] using ht
  subst trace
  exact ⟨rfl,rfl⟩

def rmwReadDemands := ByteAuthority.Footprint.span AtomicMemoryTests.base 4 .read
def rmwReadHeld : ByteAuthority.State := ⟨⟨Ptx.Async.initial 0 [],fun _ => False⟩,ByteAuthority.Footprint.holding rmwNode rmwReadDemands⟩

theorem actual_rmw_read_only_authority_rejected : ¬ByteAuthority.AllHeld rmwCandidate rmwReadHeld rmwNode := by
  intro hall
  obtain ⟨granted,hg,ha⟩ := hall AtomicMemoryTests.base .write actual_rmw_first_byte_write
  have hr := ByteAuthority.Footprint.holding_held rmwNode rmwReadDemands (ByteAuthority.Footprint.span_distinct _ _ _)
    ⟨AtomicMemoryTests.base,.read⟩ (ByteAuthority.Footprint.span_member _ _ _ ⟨0,by decide⟩)
  change get? rmwReadHeld.bytes (ByteAuthority.key AtomicMemoryTests.base) = some (.held rmwNode .read) at hr
  have heq : granted = .read := (ByteAuthority.Owner.held.inj (Option.some.inj (hg.symm.trans hr))).2
  subst granted
  exact ByteAuthority.read_cannot_authorize_write ha

def barrierNode (slot : Stage) := ByteAuthorityTests.node slot
def barrierDemands (slot : Stage) := ByteAuthority.Footprint.span (dataGate slot) 8 .write
def barrierHeld (slot : Stage) : ByteAuthority.State :=
  ⟨⟨Ptx.Async.initial 0 [],ByteAuthorityTests.cut slot⟩,ByteAuthority.Footprint.holding (barrierNode slot) (barrierDemands slot)⟩

theorem barrier_source_lookup (slot : Stage) : ByteAuthorityTests.candidate.view.eventAt (dataInitId 0 slot) =
    some (.barrier ⟨dataGate slot,.init 1⟩) := Hopper.barrierAt_iff.mp (data_resource_init _ _ 0 slot)

theorem barrier_footprint_sound (slot : Stage) : ByteAuthority.Footprint.Sound ByteAuthorityTests.candidate (barrierNode slot) (barrierDemands slot) := by
  intro demand hm
  obtain ⟨offset,rfl⟩ := List.mem_ofFn.mp hm
  exact ByteAuthorityTests.actual_init_uses_storage slot offset

theorem barrier_footprint_complete (slot : Stage) : ByteAuthority.Footprint.Covers ByteAuthorityTests.candidate (barrierNode slot) (barrierDemands slot) := by
  intro loc mode hu
  obtain ⟨offset,ho,rfl,rfl⟩ := ByteAuthority.Footprint.resource_source_uses (barrier_source_lookup slot) hu
  exact ⟨⟨(dataGate slot).add offset,.write⟩,ByteAuthority.Footprint.span_member _ _ _ ⟨offset,ho⟩,rfl,ByteAuthority.authorizes_self _⟩

theorem barrier_distinct (slot : Stage) : ByteAuthority.Footprint.Distinct (barrierDemands slot) := ByteAuthority.Footprint.span_distinct _ _ _
theorem barrier_held (slot : Stage) : ByteAuthority.Footprint.Held (barrierHeld slot) (barrierNode slot) (barrierDemands slot) :=
  ByteAuthority.Footprint.holding_held _ _ (barrier_distinct slot)
theorem barrier_frame (slot : Stage) : ByteAuthority.Footprint.Frame (barrierHeld slot) (barrierNode slot) (barrierDemands slot) := ByteAuthority.Footprint.holding_frame _ _

theorem actual_barrier_finish_succeeds (slot : Stage) :
    ByteAuthority.Footprint.finish HopperStage.block ByteAuthorityTests.candidate zeroHistories (barrierNode slot) (barrierDemands slot) (barrierHeld slot) =
      .ok (ByteAuthority.retired (barrierHeld slot) (barrierNode slot)) :=
  ByteAuthority.Footprint.finish_succeeds (ByteAuthorityTests.actual_rank_cut_ready slot) (barrier_footprint_sound slot) (barrier_footprint_complete slot)
    (barrier_distinct slot) (barrier_held slot) (barrier_frame slot)

theorem missing_last_barrier_byte_not_covered (slot : Stage) :
    ¬ByteAuthority.Footprint.Covers ByteAuthorityTests.candidate (barrierNode slot) (ByteAuthority.Footprint.span (dataGate slot) 7 .write) := by
  intro hc
  obtain ⟨demand,hm,he,_⟩ := hc _ _ (ByteAuthorityTests.actual_init_uses_storage slot 7)
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp hm
  have ha := congrArg Location.address he
  change (dataGate slot).address + index.val = (dataGate slot).address + 7 at ha
  have hindex := Nat.add_left_cancel ha
  have hi := index.isLt
  omega

theorem missing_last_barrier_byte_finish_rejected (slot : Stage) :
    ByteAuthority.Footprint.finish HopperStage.block ByteAuthorityTests.candidate zeroHistories (barrierNode slot)
      (ByteAuthority.Footprint.span (dataGate slot) 7 .write) (barrierHeld slot) = .error .unavailable := by
  have hr : ByteAuthority.Ready HopperStage.block ByteAuthorityTests.candidate zeroHistories (barrierHeld slot).coupled.done (barrierNode slot) :=
    ByteAuthorityTests.actual_rank_cut_ready slot
  simp [ByteAuthority.Footprint.finish,hr,missing_last_barrier_byte_not_covered slot]

theorem barrier_finish_returns_all_actual_bytes (slot : Stage) (offset : Fin 8) :
    get? (ByteAuthority.retired (barrierHeld slot) (barrierNode slot)).bytes (ByteAuthority.key ((dataGate slot).add offset.val)) = some .available :=
  ByteAuthority.retire_returns_actual_byte (ByteAuthority.Footprint.all_held (barrier_footprint_complete slot) (barrier_held slot))
    (ByteAuthorityTests.actual_init_uses_storage slot offset)

theorem actual_barrier_finish_iris_wp [ByteAuthorityHeap.GS] (slot : Stage) :
    ByteAuthorityHeap.control (barrierHeld slot) ∗ ByteAuthorityHeap.heldPoints (barrierNode slot) (barrierDemands slot) ⊢
      WP (ByteAuthorityHeap.finishInvoke ByteAuthorityTests.ctx (barrierNode slot) (barrierDemands slot))
        {{ value, ⌜value = .ok (ByteAuthority.retired (barrierHeld slot) (barrierNode slot))⌝ ∗
          ByteAuthorityHeap.control (ByteAuthority.retired (barrierHeld slot) (barrierNode slot)) ∗ ByteAuthorityHeap.freePoints (barrierDemands slot) }} :=
  ByteAuthorityHeap.finish_local_wp ByteAuthorityTests.ctx _ _ _ (ByteAuthorityTests.actual_rank_cut_ready slot)
    (barrier_footprint_sound slot) (barrier_footprint_complete slot) (barrier_distinct slot) (barrier_held slot) (barrier_frame slot)

theorem actual_barrier_finish_closed_adequate (slot : Stage) :
    adequate .NotStuck (ByteAuthorityHeap.finishInvoke ByteAuthorityTests.ctx (barrierNode slot) (barrierDemands slot)) (barrierHeld slot)
      (fun value _ => value = .ok (ByteAuthority.retired (barrierHeld slot) (barrierNode slot))) :=
  ByteAuthorityHeap.finish_adequate ByteAuthorityTests.ctx _ _ _ (ByteAuthorityTests.actual_rank_cut_ready slot)
    (barrier_footprint_sound slot) (barrier_footprint_complete slot) (barrier_distinct slot) (barrier_held slot) (barrier_frame slot)

end
end Ptx.ByteRetirementTests
