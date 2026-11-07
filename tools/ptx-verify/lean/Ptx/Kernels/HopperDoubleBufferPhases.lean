import Ptx.Kernels.HopperDoubleBufferSpec

/-! Two-stage counter and parity invariants. These equations describe the
intended loop state and address bounds; linking them to every generated-source
iteration, including unsuccessful waits, remains an execution obligation. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper

def uses (tiles : Nat) (slot : Stage) : Nat := (tiles+1-slot.val)/2
def phaseZero (tile : Nat) : Nat := ((tile+1)/2)%2
def phaseOne (tile : Nat) : Nat := (tile/2)%2
def expectedParity (tile : Nat) : Nat := (tile/2)%2

theorem uses_split (tiles : Nat) : uses tiles 0+uses tiles 1 = tiles := by dsimp [uses]; omega
theorem selected_uses_before (tile : Nat) : uses tile (stage tile) = tile/2 := by dsimp [uses,stage]; omega
theorem selected_expected_parity (tile : Nat) :
    (if (stage tile).val = 0 then phaseZero tile else phaseOne tile) = expectedParity tile := by
  by_cases he : tile%2 = 0
  all_goals simp [stage,phaseZero,phaseOne,expectedParity,he]
  all_goals omega
theorem parity_flips_on_reuse (tile : Nat) : expectedParity (tile+2) = 1-expectedParity tile := by
  dsimp [expectedParity]
  omega
theorem even_phase_transition {tile} (he : tile%2 = 0) :
    phaseZero (tile+1) = 1-phaseZero tile ∧ phaseOne (tile+1) = phaseOne tile := by
  dsimp [phaseZero,phaseOne]
  omega
theorem odd_phase_transition {tile} (he : tile%2 ≠ 0) :
    phaseOne (tile+1) = 1-phaseOne tile ∧ phaseZero (tile+1) = phaseZero tile := by
  dsimp [phaseZero,phaseOne]
  omega
theorem selected_stage_toggles (tile : Nat) : (stage (tile+1)).val = 1-(stage tile).val := by dsimp [stage]; omega
theorem expected_parity_bounded (tile : Nat) : expectedParity tile < 2 := Nat.mod_lt _ (by decide)
theorem source_coordinate_small {tiles tile} (ht : tile < tiles) (hb : tiles ≤ 2^28) :
    8*tile < 2^31 ∧ Tma.signed32 (8*tile) = (8*tile : Nat) ∧ Tma.signed32 tile = (tile : Int) := by
  have h : 8*tile < 2^31 := by omega
  exact ⟨h,Tma.signed32_of_small h,Tma.signed32_of_small (by omega)⟩
theorem a_view_profile {base tiles} (ht : 0 < tiles) (hsize : 8*tiles ≤ 2^32)
    (hb : base < 2^64) (ha : base%16 = 0) : Tma.Profile (aView base tiles) := by
  dsimp [Tma.Profile,aView]
  norm_num
  exact ⟨by omega,hsize,hb,ha⟩
theorem b_view_profile {base tiles} (ht : 0 < tiles) (hsize : tiles ≤ 2^32)
    (hb : base < 2^64) (ha : base%16 = 0) : Tma.Profile (bView base tiles) := by
  dsimp [Tma.Profile,bView]
  norm_num
  exact ⟨ht,hsize,hb,ha⟩
theorem a_source_within_allocation {base tiles tile offset} (ht : tile < tiles) (ho : offset < 2048) :
    base ≤ base+2048*tile+offset ∧ base+2048*tile+offset < base+2048*tiles := by omega
theorem b_source_within_allocation {base tiles tile offset} (ht : tile < tiles) (ho : offset < 256) :
    base ≤ base+256*tile+offset ∧ base+256*tile+offset < base+256*tiles := by omega

end Ptx.Kernels.HopperDoubleBuffer
