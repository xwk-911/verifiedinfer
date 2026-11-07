import Ptx.Kernels.HopperDoubleBufferSpec

/-! Shared launch context and represented zero-input replies for the actual
source. Reply shape is a local source condition; descriptor provenance,
resource histories and memory/tensor agreement remain separate admission. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000

def params (tiles : Nat) : Bindings := [("MAP_A",4096),("MAP_B",4224),("C",8192),("TILES",tiles)]
def ctx (tiles : Nat) (lane : Wgmma.Lane) : Scalar.Context := {HopperStage.ctx lane with params := params tiles}
def oracle (tiles : Nat) : Wgmma.Oracle := {
  base := {
    ampere := {scalar := fun _ => .integer 0,bytes := fun _ => []}
    wait := fun _ => true
    descriptor := fun query => if query = 0 ∨ (5 ≤ query ∧ (query-5)%7 = 0) then aView 65536 tiles else bView 131072 tiles
    tmaBytes := fun query => if query = 1 ∨ (6 ≤ query ∧ (query-6)%7 = 0)
      then HopperStage.aPayload (fun _ => 0) else HopperStage.bPayload (fun _ => 0)
  }
  operands := fun _ => Wgmma.payload (fun _ => 0) (fun _ => 0)
}

theorem oracle_payload_shape (tiles query : Nat) :
    ((oracle tiles).base.tmaBytes (query+1)).length = ((oracle tiles).base.descriptor query).bytes := by
  have he : (query+1 = 1 ∨ (6 ≤ query+1 ∧ (query+1-6)%7 = 0)) ↔
      (query = 0 ∨ (5 ≤ query ∧ (query-5)%7 = 0)) := by omega
  by_cases h : query = 0 ∨ (5 ≤ query ∧ (query-5)%7 = 0)
  · have h' := he.mpr h
    simp [oracle,h,h',HopperStage.a_payload_length,aView,Tma.Descriptor2D.bytes]
  · have h' : ¬(query+1 = 1 ∨ (6 ≤ query+1 ∧ (query+1-6)%7 = 0)) := fun hh => h (he.mp hh)
    simp [oracle,h,h',HopperStage.b_payload_length,bView,Tma.Descriptor2D.bytes]

end
end Ptx.Kernels.HopperDoubleBuffer
