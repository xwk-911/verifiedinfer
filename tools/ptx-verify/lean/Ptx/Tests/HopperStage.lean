import Ptx.Kernels.HopperStageOutput
import Ptx.Tests.WgmmaTensor

/-! Source-matched single-stage checks. This is not a full memory-admitted
GEMM case: initial-memory, resource and observer obligations remain open. -/
namespace Ptx.HopperStageTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels.HopperStage
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 50000

theorem source_metadata : count 0 = 47 ∧ count 127 = 41 ∧
    (mmaId 0).serial = 9 ∧ (mmaId 127).serial = 4 ∧
    (storeId 0 0).serial = 12 ∧ (storeId 127 3).serial = 10 := by decide
theorem query_identity (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    (calls a b 0).query = 5 ∧ (calls a b 127).query = 1 := by constructor <;> rfl
theorem payload_sizes : (copyA WgmmaTensorTests.nonuniformA).payload.length = 2048 ∧
    (copyB WgmmaTensorTests.nonuniformB).payload.length = 256 :=
  ⟨a_payload_length _,b_payload_length _⟩
theorem last_store_address : wrap 64 (outFinal 127+storeOffset 3) = 10236 := by decide
theorem nonuniform_last_store :
    (candidate WgmmaTensorTests.nonuniformA WgmmaTensorTests.nonuniformB).eventAt (storeId 127 3) =
      some (.base (.ampere (.ordinary (.write ⟨.global,10236⟩ (Symbolic.encode .f32 1472))))) := by
  rw [actual_candidate_store]
  norm_num [Wgmma.cCoord,Wgmma.matrixStep,WgmmaTensorTests.nonuniformA,
    WgmmaTensorTests.nonuniformB,Fin.sum_univ_succ]

end
end Ptx.HopperStageTests
