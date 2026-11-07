import Ptx.Generated.AmpereTiledMatmul
import Ptx.Ampere.MmaBlock
import Ptx.Ampere.MmaProtocolRules
import Ptx.Kernels.AmpereTiledSpec

/-! The actual tiled load/MMA source fragment and its independent accumulator
specification. Kernel proofs must still derive entry state/input representation
and phase ordering from complete source runs and memory agreement. -/
namespace Ptx.AmpereTiledMma
open Ptx.ISA Ptx.Ampere
noncomputable section

abbrev code := Generated.ampere_tiled_matmul.program

theorem fragment : MmaBlock.Fragment code 65 := by constructor <;> rfl

theorem matched_accumulation_step {launch c event call}
    (hm : MmaConditions code launch c) (he : c.eventAt event = some (.mmaReturn call))
    (a b : AmpereTiledSpec.Matrix) (tileRow tileCol step : Nat)
    (ha : ∀ entry other, SameMmaGroup c event call entry other → ∀ slot,
      other.inputs.a slot = Mma.packA (Mma.gatherA (AmpereTiledSpec.tileA a tileRow step)) (other.lane,slot))
    (hb : ∀ entry other, SameMmaGroup c event call entry other → ∀ slot,
      other.inputs.b slot = Mma.packB (Mma.gatherB (AmpereTiledSpec.tileB b tileCol step)) (other.lane,slot))
    (hc : ∀ entry other, SameMmaGroup c event call entry other → ∀ slot,
      other.inputs.c slot = Mma.gatherC (AmpereTiledSpec.tileC a b tileRow tileCol step) (other.lane,slot))
    (slot : Fin 4) :
    call.output slot = Mma.gatherC (AmpereTiledSpec.tileC a b tileRow tileCol (step+1)) (call.lane,slot) := by
  have hv := matched_mma_output hm he (AmpereTiledSpec.tileA a tileRow step)
    (AmpereTiledSpec.tileB b tileCol step) (AmpereTiledSpec.tileC a b tileRow tileCol step) ha hb hc slot
  rw [AmpereTiledSpec.mma_accumulation_step] at hv
  exact hv

end
end Ptx.AmpereTiledMma
