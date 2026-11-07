import Ptx.Generated.HopperDoubleBufferGemm
import Ptx.Hopper.WgmmaTensor
import Ptx.Hopper.TmaPackedTiles
import Ptx.Kernels.HopperStageCollective

/-! Independent fixed-output-tile specification and two-stage layout.
The recursion specifies accumulation over all K slices, not execution traces.
Source-loop, memory/observer, allocation and hardware obligations are separate.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev Stage := Fin 2
def stage (tile : Nat) : Stage := ⟨tile%2,Nat.mod_lt _ (by decide)⟩
def barrierAddress (slot : Stage) : Nat := 8*slot.val
def aBase (slot : Stage) : Nat := 16+2304*slot.val
def bBase (slot : Stage) : Nat := 2064+2304*slot.val
def aDescriptor (slot : Stage) : Nat :=
  (Wgmma.MatrixDescriptor.mk ⟨aBase slot/16,by have := slot.isLt; dsimp [aBase]; omega⟩ 8 16).encode
def bDescriptor (slot : Stage) : Nat :=
  (Wgmma.MatrixDescriptor.mk ⟨bBase slot/16,by have := slot.isLt; dsimp [bBase]; omega⟩ 8 16).encode
def aView (base tiles : Nat) : Tma.Descriptor2D := ⟨base,128,8*tiles,256,128,8,2⟩
def bView (base tiles : Nat) : Tma.Descriptor2D := ⟨base,128,tiles,256,128,1,2⟩
def result (a : Nat → Wgmma.ACoord → ℝ) (b : Nat → Wgmma.BCoord → ℝ) : Nat → Wgmma.CCoord → ℝ
  | 0 => fun _ => 0
  | n+1 => Wgmma.matrixStep (a n) (b n) (result a b n)
def specification (a : Nat → Wgmma.ACoord → ℝ) (b : Nat → Wgmma.BCoord → ℝ) (tiles : Nat) (p : Wgmma.CCoord) : ℝ :=
  ∑ tile ∈ Finset.range tiles, ∑ k : Fin 16, a tile (p.1,k)*b tile (k,p.2)

theorem result_matches_specification (a b tiles p) : result a b tiles p = specification a b tiles p := by
  induction tiles with
  | zero => simp [result,specification]
  | succ n ih => simp only [result,Wgmma.matrixStep,ih,specification,Finset.sum_range_succ]
theorem stage_reuse_two_apart (tile : Nat) : stage (tile+2) = stage tile := by
  apply Fin.ext
  dsimp [stage]
  omega
theorem consecutive_stages_distinct (tile : Nat) : stage tile ≠ stage (tile+1) := by
  intro he
  have hh := congrArg Fin.val he
  dsimp [stage] at hh
  omega
theorem descriptor_profiles (slot : Stage) : Wgmma.MatrixDescriptor.Packed (aDescriptor slot) ∧ Wgmma.MatrixDescriptor.Packed (bDescriptor slot) := by
  fin_cases slot <;> decide
theorem descriptor_bases (slot : Stage) : (Wgmma.MatrixDescriptor.decode (aDescriptor slot)).base = aBase slot ∧
    (Wgmma.MatrixDescriptor.decode (bDescriptor slot)).base = bBase slot := by
  fin_cases slot <;> decide
theorem a_operand_address (slot : Stage) (p : Wgmma.ACoord) (byte : Fin 2) :
    Wgmma.aAddress (Wgmma.MatrixDescriptor.decode (aDescriptor slot)) p byte = aBase slot+(Wgmma.aOffset (p,byte)).val := by
  rw [Wgmma.packed_a_address (descriptor_profiles slot).1,(descriptor_bases slot).1]
theorem b_operand_address (slot : Stage) (p : Wgmma.BCoord) (byte : Fin 2) :
    Wgmma.bAddress (Wgmma.MatrixDescriptor.decode (bDescriptor slot)) p byte = bBase slot+(Wgmma.bOffset (p,byte)).val := by
  rw [Wgmma.packed_b_address (descriptor_profiles slot).2,(descriptor_bases slot).2]
theorem a_tile_source {base tiles tile offset} (ht : tile < tiles) (ho : offset < 2048) :
    Tma.sourceByte (aView base tiles) ⟨0,(8*tile : Nat)⟩ offset = some ⟨.global,base+2048*tile+offset⟩ :=
  Tma.packed_tile_source_byte base 8 tiles tile offset ht (by omega)
theorem b_tile_source {base tiles tile offset} (ht : tile < tiles) (ho : offset < 256) :
    Tma.sourceByte (bView base tiles) ⟨0,(tile : Nat)⟩ offset = some ⟨.global,base+256*tile+offset⟩ := by
  simpa only [bView,Nat.one_mul,Nat.mul_one] using Tma.packed_tile_source_byte base 1 tiles tile offset ht (by omega)
theorem stage_arena_bounds (slot : Stage) :
    barrierAddress slot+8 ≤ 16 ∧ 16 ≤ aBase slot ∧ aBase slot+2048 = bBase slot ∧ bBase slot+256 ≤ 4624 := by
  have := slot.isLt
  dsimp [barrierAddress,aBase,bBase]
  omega
theorem stage_arenas_disjoint {left right : Stage} (hne : left ≠ right) :
    bBase left+256 ≤ aBase right ∨ bBase right+256 ≤ aBase left := by
  have hl := left.isLt
  have hr := right.isLt
  have hv : left.val ≠ right.val := fun h => hne (Fin.ext h)
  dsimp [aBase,bBase]
  omega
theorem encoded_stage_constants : aDescriptor 0 = 68720001025 ∧ bDescriptor 0 = 68720001153 ∧
    aDescriptor 1 = 68720001169 ∧ bDescriptor 1 = 68720001297 := by decide

end
end Ptx.Kernels.HopperDoubleBuffer
