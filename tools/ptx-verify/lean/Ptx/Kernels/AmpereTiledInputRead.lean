import Ptx.Kernels.AmpereTiledProducer
import Ptx.Ampere.PackedMemory

/-! Force the two real halves of an actual packed shared read from represented
global A/B inputs. Copy ownership, publication and eligibility are derived. -/
namespace Ptx.AmpereTiledInputRead
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledGraph Ptx.AmpereTiledProducer
noncomputable section

def inputRow (id : ThreadId) (reg : Fin 6) : Nat := 16*id.cta.y+id.tid.y+8*(reg.val%2)
def inputCol (id : ThreadId) : Nat := 8*id.cta.x+id.tid.y
def inputK (id : ThreadId) (phase : Nat) (reg : Fin 6) (half : Fin 2) : Nat :=
  16*phase+2*id.tid.x+8*(if reg.val < 4 then reg.val/2 else reg.val-4)+half.val
def expected (a b : Matrix) (id : ThreadId) (phase : Nat) (reg : Fin 6) (half : Fin 2) : ℝ :=
  if reg.val < 4 then a (inputRow id reg) (inputK id phase reg half)
  else b (inputK id phase reg half) (inputCol id)

theorem input_bounds {cfg : Config} (h : Layout cfg) {id : ThreadId} (hv : id.Valid (geometry cfg))
    (ha : Active cfg) {phase : Nat} (hp : phase < cfg.k/16) (reg : Fin 6) (half : Fin 2) :
    inputK id phase reg half < cfg.k ∧ (if reg.val < 4 then inputRow id reg < cfg.m else inputCol id < cfg.n) := by
  have he := AmpereTiledGeometry.element_bounds h (ctx := {id := id,params := [],block := (geometry cfg).block}) hv ha
  dsimp only at he
  have hx : id.tid.x < 4 := hv.2.1
  have hi := reg.isLt
  have hh := half.isLt
  have hk := h.tiles.2.2
  dsimp [inputK,inputRow,inputCol]
  split <;> constructor <;> omega

theorem initial_half_byte {cfg launch candidate a b} (h : SourceInfo cfg launch candidate)
    (hi : Input cfg a b launch.initial) {id : ThreadId} (hv : id.Valid launch.geometry)
    {phase : Nat} (hp : phase < cfg.k/16) (reg : Fin 6) (half offset : Fin 2) :
    launch.initial ((inputBase cfg id phase reg).add (2*half.val+offset.val)) =
      .realPart .f16 (expected a b id phase reg half) offset.val := by
  have hv' : id.Valid (geometry cfg) := by simpa only [h.geometry] using hv
  have hb := input_bounds h.layout hv' h.active hp reg half
  have hlocA : (aLocation cfg (inputRow id reg) (16*phase+2*id.tid.x+8*(reg.val/2))).add (2*half.val+offset.val) =
      (aLocation cfg (inputRow id reg) (16*phase+2*id.tid.x+8*(reg.val/2)+half.val)).add offset.val := by
    simp [aLocation,Location.add]; ring
  have hlocB : (bLocation cfg (16*phase+2*id.tid.x+8*(reg.val-4)) (inputCol id)).add (2*half.val+offset.val) =
      (bLocation cfg (16*phase+2*id.tid.x+8*(reg.val-4)+half.val) (inputCol id)).add offset.val := by
    simp [bLocation,Location.add]; ring
  by_cases hr : reg.val < 4
  · simp only [inputBase,hr,ite_true,expected,inputRow,inputK] at *
    rw [hlocA]
    exact (hi h.active).1 _ _ hb.2 hb.1 offset.val offset.isLt
  · simp only [inputBase,hr,ite_false,expected,inputCol,inputK] at *
    rw [hlocB]
    exact (hi h.active).2 _ _ hb.1 hb.2 offset.val offset.isLt

theorem initial_half {cfg launch candidate a b} (h : SourceInfo cfg launch candidate)
    (hi : Input cfg a b launch.initial) {id : ThreadId} (hv : id.Valid launch.geometry)
    {phase : Nat} (hp : phase < cfg.k/16) (reg : Fin 6) (half : Fin 2) :
    launch.initial ((inputBase cfg id phase reg).add (2*half.val)) =
      .realPart .f16 (expected a b id phase reg half) 0 := by
  simpa only [Fin.val_zero,Nat.add_zero] using initial_half_byte h hi hv hp reg half 0

theorem packed_read_half {cfg launch candidate rf co a b} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co) (hi : Input cfg a b launch.initial)
    {id : ThreadId} (hv : id.Valid launch.geometry) {phase : Nat} (hp : phase < cfg.k/16)
    (reg : Fin 6) {pair : PackedF16}
    (he : candidate.eventAt ⟨id,17*phase+7+reg.val⟩ =
      some (.ordinary (.read (AmpereTiledInventory.readBase (context launch id) reg) pair.encode))) (half : Fin 2) :
    pair.half half = expected a b id phase reg half := by
  have hb := pair.half_byte (AmpereTiledInventory.readBase (context launch id) reg) half 0
  have hr : candidate.readByte (.thread ⟨id,17*phase+7+reg.val⟩)
      ((AmpereTiledInventory.readBase (context launch id) reg).add (2*half.val)) = some (.realPart .f16 (pair.half half) 0) := by
    simpa [Candidate.readByte,Candidate.memoryKind,he,Ptx.Event.Kind.readByte] using hb
  have hv' := read_input_byte h hm hv hp reg (⟨2*half.val,by have hh := half.isLt; omega⟩ : Fin 4) hr
  rw [initial_half h hi hv hp reg half] at hv'
  exact (Symbolic.Byte.realPart.inj hv').2.1

end
end Ptx.AmpereTiledInputRead
