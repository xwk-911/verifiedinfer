import Ptx.Kernels.HopperStageTensor

/-! Remove machine-word wraps from the actual source address checkpoint,
using bounds from the physical 128-thread launch. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section

theorem wrap32_small {value : Nat} (h : value < 1024) : wrap 32 value = value :=
  Nat.mod_eq_of_lt (by omega)
theorem wrap64_small {value : Nat} (h : value < 16384) : wrap 64 value = value :=
  Nat.mod_eq_of_lt (by omega)
theorem coordinate_bounds (lane : Wgmma.Lane) : (tid lane).x < 4 ∧ (tid lane).y < 8 ∧ (tid lane).z < 4 := by
  have := lane.isLt
  dsimp [tid]
  omega
theorem row_first_value (lane : Wgmma.Lane) : rowFirst lane = 16*(tid lane).z := by
  have h := coordinate_bounds lane
  rw [rowFirst,(coordinate_words lane).2.2,wrap32_small (value := (tid lane).z) (by omega),wrap32_small (by omega)]
  omega
theorem row_final_value (lane : Wgmma.Lane) : rowFinal lane = 16*(tid lane).z+(tid lane).y := by
  have h := coordinate_bounds lane
  rw [rowFinal,row_first_value,(coordinate_words lane).2.1,
    wrap32_small (value := 16*(tid lane).z) (by omega),wrap32_small (value := (tid lane).y) (by omega),wrap32_small (by omega)]
theorem col_final_value (lane : Wgmma.Lane) : colFinal lane = 2*(tid lane).x := by
  have h := coordinate_bounds lane
  rw [colFinal,(coordinate_words lane).1,wrap32_small (value := (tid lane).x) (by omega),wrap32_small (by omega)]
  omega
theorem linear_first_value (lane : Wgmma.Lane) : linearFirst lane = 8*(16*(tid lane).z+(tid lane).y) := by
  have h := coordinate_bounds lane
  rw [linearFirst,row_final_value,wrap32_small (value := 16*(tid lane).z+(tid lane).y) (by omega),wrap32_small (by omega)]
  omega
theorem linear_final_value (lane : Wgmma.Lane) : linearFinal lane = 8*(16*(tid lane).z+(tid lane).y)+2*(tid lane).x := by
  have h := coordinate_bounds lane
  rw [linearFinal,linear_first_value,col_final_value,
    wrap32_small (value := 8*(16*(tid lane).z+(tid lane).y)) (by omega),
    wrap32_small (value := 2*(tid lane).x) (by omega),wrap32_small (by omega)]
theorem offset_final_value (lane : Wgmma.Lane) : offsetFinal lane = 4*(8*(16*(tid lane).z+(tid lane).y)+2*(tid lane).x) := by
  have h := coordinate_bounds lane
  rw [offsetFinal,linear_final_value,wrap32_small (by omega),wrap64_small (by omega)]
  omega
theorem out_final_value (lane : Wgmma.Lane) : outFinal lane = 8192+4*(8*(16*(tid lane).z+(tid lane).y)+2*(tid lane).x) := by
  have h := coordinate_bounds lane
  simp only [outFinal,offset_final_value,wrap64_small (value := 8192) (by omega)]
  rw [wrap64_small (value := 4*(8*(16*(tid lane).z+(tid lane).y)+2*(tid lane).x)) (by omega),wrap64_small (by omega)]

def storeOffset (slot : Wgmma.Slot) : Nat := 256*(slot.val/2)+4*(slot.val%2)
theorem actual_output_address (lane : Wgmma.Lane) (slot : Wgmma.Slot) :
    wrap 64 (outFinal lane+storeOffset slot) =
      8192+4*(8*(Wgmma.cCoord (lane,slot)).1.val+(Wgmma.cCoord (lane,slot)).2.val) := by
  have h := coordinate_bounds lane
  have hs := slot.isLt
  rw [out_final_value,wrap64_small (by dsimp [storeOffset]; omega)]
  dsimp [storeOffset,tid,Wgmma.cCoord]
  omega
theorem actual_output_bounds (lane : Wgmma.Lane) (slot : Wgmma.Slot) :
    8192 ≤ wrap 64 (outFinal lane+storeOffset slot) ∧
    wrap 64 (outFinal lane+storeOffset slot)+4 ≤ 10240 := by
  rw [actual_output_address]
  have := (Wgmma.cCoord (lane,slot)).1.isLt
  have := (Wgmma.cCoord (lane,slot)).2.isLt
  omega

end
end Ptx.Kernels.HopperStage
