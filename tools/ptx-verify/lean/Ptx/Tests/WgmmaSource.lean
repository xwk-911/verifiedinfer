import Ptx.Hopper.WgmmaCollective
import Ptx.Tests.WgmmaProtocol

/-! Actual generated, assembled source: all 128 local executions complete and
have identical source-derived WGMMA schedules. The matrix reply 16 is arbitrary
protocol-test data. Shared input arrays are uninitialized in this probe: it is
not an admitted memory/arithmetic witness or a verified GEMM kernel. -/
namespace Ptx.WgmmaSourceTests
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def ctx (lane : Fin 128) : Scalar.Context := {
  id := ⟨.zero,⟨lane.val,0,0⟩⟩
  params := [("OUT",8192)]
  block := ⟨128,1,1⟩
}
def oracle : Wgmma.Oracle := {WgmmaProtocolTests.oracle with matrix := fun _ _ => 16}
def result (lane : Fin 128) : Wgmma.State × List (SourceRun.Located Wgmma.Event) :=
  (Wgmma.runLocated (ctx lane) oracle Generated.wgmma_probe.program 16 {}).toOption.getD ({},[])
def expected : List Wgmma.SourceSignature := [
  ⟨10,⟨10,0,0⟩,.fence⟩,
  ⟨11,⟨11,1,0⟩,.mma 0 0 WgmmaProtocolTests.d.names 68720001024 68720001152 true⟩,
  ⟨12,⟨12,2,0⟩,.commit 0⟩,
  ⟨13,⟨13,3,0⟩,.wait 1 0⟩
]

theorem all_lanes_succeed : ∀ lane : Fin 128,
    (Wgmma.runLocated (ctx lane) oracle Generated.wgmma_probe.program 16 {}).toOption.isSome = true := by intro lane; rfl
theorem actual_source_run (lane : Fin 128) :
    Wgmma.runLocated (ctx lane) oracle Generated.wgmma_probe.program 16 {} = .ok (result lane) := by
  have hh := all_lanes_succeed lane
  cases hr : Wgmma.runLocated (ctx lane) oracle Generated.wgmma_probe.program 16 {} with
  | error fault => rw [hr] at hh; cases hh
  | ok value => simp only [result,hr]; rfl
theorem actual_plain_run (lane : Fin 128) :
    Wgmma.run (ctx lane) oracle Generated.wgmma_probe.program 16 {} =
      .ok ((result lane).1,(result lane).2.map SourceRun.Located.kind) :=
  Wgmma.run_located_erases_result (ctx := ctx lane) (oracle := oracle)
    (code := Generated.wgmma_probe.program) (n := 16) (s := {})
    (value := result lane) (actual_source_run lane)

theorem complete_metadata : ∀ lane : Fin 128,
    ((result lane).1.base.scalar.core.thread.status == .done) &&
      ((Wgmma.pending (result lane).1.ledger).length == 0) = true := by intro lane; rfl
theorem all_lanes_complete (lane : Fin 128) : Wgmma.Complete (result lane).1 := by
  exact Wgmma.complete_of_metadata (result lane).1 (complete_metadata lane)
theorem actual_schedule : ∀ lane : Fin 128, Wgmma.schedule (result lane).2 = expected := by
  intro lane
  change [⟨10,⟨10,0,lane.val/128⟩,.fence⟩,
    ⟨11,⟨11,1,lane.val/128⟩,.mma 0 0 WgmmaProtocolTests.d.names 68720001024 68720001152 true⟩,
    ⟨12,⟨12,2,lane.val/128⟩,.commit 0⟩,⟨13,⟨13,3,lane.val/128⟩,.wait 1 0⟩] = expected
  rw [Nat.div_eq_of_lt lane.isLt]
  rfl
theorem identical_warpgroup_schedule (left right : Fin 128) :
    Wgmma.schedule (result left).2 = Wgmma.schedule (result right).2 :=
  (actual_schedule left).trans (actual_schedule right).symm
theorem event_source_pcs : ∀ lane : Fin 128, (result lane).2.map SourceRun.Located.pc = [10,11,12,13,14] := by intro lane; rfl
theorem per_lane_metadata : ∀ lane : Fin 128,
    (result lane).1.ledger.calls.length = 1 ∧
    ((result lane).1.ledger.calls[0]?).map (fun call => call.lane) = some lane ∧
    ((result lane).1.ledger.calls[0]?).map (fun call => call.query) = some 0 ∧
    (result lane).1.base.scalar.core.queries = 2 ∧
    (result lane).1.ledger.groups = 1 ∧ (result lane).1.ledger.completed = 1 := by
  intro lane
  refine ⟨rfl,?_,rfl,rfl,rfl,rfl⟩
  apply congrArg some
  apply Fin.ext
  exact Nat.mod_eq_of_lt lane.isLt
theorem concrete_local_output : declarationLookup "%d0" (result 127).1.base.scalar.floats = some (.f32,16) := by rfl

end
end Ptx.WgmmaSourceTests
