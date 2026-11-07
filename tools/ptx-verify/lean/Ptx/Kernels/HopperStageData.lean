import Ptx.Generated.HopperGemmStage
import Ptx.Hopper.UnifiedStep
import Ptx.Hopper.WgmmaTensor
import Mathlib.Data.List.OfFn

/-! Independent source witnesses for the actual 47-instruction stage target.
The chosen tensor/byte replies are parameterized by arbitrary real A/B. This
is source/completion evidence only: resource, collective, RF/coherence/proxy,
allocation/lifetime and global observer admission must still be joined. No
claim equating these replies with launch.initial is made by this module. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def block : Dim3 := ⟨4,8,4⟩
def geometry : Geometry := ⟨.one,block⟩
def params : Bindings := [("MAP_A",4096),("MAP_B",4224),("C",8192)]
def tid (lane : Wgmma.Lane) : Dim3 := ⟨lane.val%4,(lane.val%32)/4,lane.val/32⟩
def ctx (lane : Wgmma.Lane) : Scalar.Context := {id := ⟨.zero,tid lane⟩,params := params,block := block}
def aView : Tma.Descriptor2D := ⟨65536,128,8,256,128,8,2⟩
def bView : Tma.Descriptor2D := ⟨69632,128,1,256,128,1,2⟩
def aPayload (a : Wgmma.ACoord → ℝ) : List Symbolic.Byte := List.ofFn (fun offset : Fin 2048 =>
  .realPart .f16 (a (Wgmma.aByteOwner offset).1) (Wgmma.aByteOwner offset).2.val)
def bPayload (b : Wgmma.BCoord → ℝ) : List Symbolic.Byte := List.ofFn (fun offset : Fin 256 =>
  .realPart .f16 (b (Wgmma.bByteOwner offset).1) (Wgmma.bByteOwner offset).2.val)
def oracle (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) : Wgmma.Oracle := {
  base := {
    ampere := {scalar := fun _ => .integer 0,bytes := fun _ => []}
    wait := fun _ => true
    descriptor := fun query => if query = 0 then aView else bView
    tmaBytes := fun query => if query = 1 then aPayload a else bPayload b
  }
  matrix := fun _ slot => Wgmma.results a b (fun _ => 0) (lane,slot)
  operands := fun _ => Wgmma.payload a b
}
def count (lane : Wgmma.Lane) : Nat := if lane.val = 0 then 47 else 41
theorem a_profile : Tma.Profile aView := by decide
theorem b_profile : Tma.Profile bView := by decide
theorem a_payload_length (a : Wgmma.ACoord → ℝ) : (aPayload a).length = 2048 := by simp only [aPayload,List.length_ofFn]
theorem b_payload_length (b : Wgmma.BCoord → ℝ) : (bPayload b).length = 256 := by simp only [bPayload,List.length_ofFn]

end
end Ptx.Kernels.HopperStage
