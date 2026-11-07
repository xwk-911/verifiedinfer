import Ptx.Kernels.HopperDoubleBufferReplyQueries
import Ptx.Kernels.HopperDoubleBufferContext
import Ptx.Kernels.HopperDoubleBufferPhases

/-! Explicit arbitrary-real tile replies for a source witness. Matrix replies
are computed from the fixed WGMMA arithmetic and prior tile recurrence, rather
than supplied as a desired output premise. Source/byte/tensor admission must
still identify these replies with actual inputs before kernel correctness.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev TileA := Nat → Wgmma.ACoord → ℝ
abbrev TileB := Nat → Wgmma.BCoord → ℝ

def tileReply (a : TileA) (b : TileB) (tile : Nat) : Wgmma.Lane × Wgmma.Slot → ℝ :=
  Wgmma.results (a tile) (b tile) (Wgmma.gatherC (result a b tile))

def dataPayload (a : TileA) (b : TileB) (query : Nat) : List Symbolic.Byte :=
  if query = 1 ∨ (6 ≤ query ∧ (query-6)%7 = 0) then
    HopperStage.aPayload (a (aPayloadTile query))
  else HopperStage.bPayload (b (bPayloadTile query))

def dataBBase (tiles : Nat) : Nat := 65536+2048*tiles
def dataDescriptor (tiles query : Nat) : Tma.Descriptor2D :=
  if query = 0 ∨ (5 ≤ query ∧ (query-5)%7 = 0) then aView 65536 tiles else bView (dataBBase tiles) tiles

def dataOracle (a : TileA) (b : TileB) (tiles : Nat) (lane : Wgmma.Lane) : Wgmma.Oracle := {
  base := {(oracle tiles).base with tmaBytes := dataPayload a b,descriptor := dataDescriptor tiles}
  matrix := fun query slot => tileReply a b (nativeTile tiles (HopperStage.leader lane) query) (lane,slot)
  operands := fun query => Wgmma.payload (a (nativeTile tiles (HopperStage.leader lane) query)) (b (nativeTile tiles (HopperStage.leader lane) query))
}

theorem tile_reply_value (a : TileA) (b : TileB) (tile : Nat) (owner : Wgmma.Lane × Wgmma.Slot) :
    tileReply a b tile owner = result a b (tile+1) (Wgmma.cCoord owner) := by
  simp only [tileReply,Wgmma.results,Wgmma.scatter_gather_c,Wgmma.gatherC,result]

theorem data_oracle_payload_length (a b tiles lane query) :
    ((dataOracle a b tiles lane).base.tmaBytes query).length = ((oracle tiles).base.tmaBytes query).length := by
  by_cases h : query = 1 ∨ (6 ≤ query ∧ (query-6)%7 = 0)
  all_goals simp [dataOracle,dataPayload,oracle,h,HopperStage.a_payload_length,HopperStage.b_payload_length]

theorem data_descriptor_bytes (tiles query : Nat) :
    (dataDescriptor tiles query).bytes = ((oracle tiles).base.descriptor query).bytes := by
  by_cases h : query = 0 ∨ (5 ≤ query ∧ (query-5)%7 = 0)
  all_goals simp [dataDescriptor,oracle,h,aView,bView,Tma.Descriptor2D.bytes]

theorem data_oracle_payload_shape (a b tiles lane query) :
    ((dataOracle a b tiles lane).base.tmaBytes (query+1)).length = ((dataOracle a b tiles lane).base.descriptor query).bytes := by
  rw [data_oracle_payload_length]
  change ((oracle tiles).base.tmaBytes (query+1)).length = (dataDescriptor tiles query).bytes
  rw [data_descriptor_bytes]
  exact oracle_payload_shape tiles query

theorem data_oracle_loop_replies (a b tiles lane query tile) :
    LoopReplies (dataOracle a b tiles lane) query tile tiles 0 (HopperStage.leader lane) := by
  refine ⟨by intro i hi; omega,rfl,?_⟩
  intro _
  exact ⟨data_oracle_payload_shape a b tiles lane (query+1),by simpa [Nat.add_assoc] using data_oracle_payload_shape a b tiles lane (query+3)⟩

theorem data_oracle_native_matrix (a b tiles lane tile) (ht : tile < tiles) (slot : Wgmma.Slot) :
    (dataOracle a b tiles lane).matrix (nativeQuery tiles tile (HopperStage.leader lane)) slot =
      result a b (tile+1) (Wgmma.cCoord (lane,slot)) := by
  change tileReply a b (nativeTile tiles (HopperStage.leader lane) (nativeQuery tiles tile (HopperStage.leader lane))) (lane,slot) = _
  rw [native_tile_inverse tiles tile (HopperStage.leader lane) ht,tile_reply_value]

theorem data_oracle_native_operands (a b tiles lane tile) (ht : tile < tiles) (offset : Nat) :
    (dataOracle a b tiles lane).operands (nativeQuery tiles tile (HopperStage.leader lane)) offset =
      Wgmma.payload (a tile) (b tile) offset := by
  simp only [dataOracle,native_tile_inverse tiles tile (HopperStage.leader lane) ht]

theorem data_oracle_initial_a (a b tiles lane) :
    (dataOracle a b tiles lane).base.tmaBytes 1 = HopperStage.aPayload (a 0) := by rfl

theorem data_oracle_initial_b (a b tiles lane) :
    (dataOracle a b tiles lane).base.tmaBytes 3 = HopperStage.bPayload (b 0) := by rfl

theorem data_oracle_prefetch_a (a b tiles lane tile) :
    (dataOracle a b tiles lane).base.tmaBytes (6+7*tile) = HopperStage.aPayload (a (tile+1)) := by
  have h : 6 ≤ 6+7*tile ∧ (6+7*tile-6)%7 = 0 := by omega
  simp [dataOracle,dataPayload,h,(prefetch_payload_tiles tile).1]

theorem data_oracle_prefetch_b (a b tiles lane tile) :
    (dataOracle a b tiles lane).base.tmaBytes (8+7*tile) = HopperStage.bPayload (b (tile+1)) := by
  have h : ¬(8+7*tile = 1 ∨ (6 ≤ 8+7*tile ∧ (8+7*tile-6)%7 = 0)) := by omega
  simp [dataOracle,dataPayload,h,(prefetch_payload_tiles tile).2]

theorem data_input_regions_disjoint (tiles : Nat) : 65536+2048*tiles ≤ dataBBase tiles := Nat.le_refl _
theorem data_b_base_aligned (tiles : Nat) : dataBBase tiles % 16 = 0 := by dsimp [dataBBase]; omega
theorem data_input_address_bound (tiles : Nat) (hb : tiles ≤ 2^28) : dataBBase tiles+256*tiles < 2^64 := by
  dsimp [dataBBase]
  omega

theorem data_descriptor_profile (tiles query : Nat) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Tma.Profile (dataDescriptor tiles query) := by
  by_cases h : query = 0 ∨ (5 ≤ query ∧ (query-5)%7 = 0)
  · simp only [dataDescriptor,h,ite_true]
    exact a_view_profile ht (by omega) (by decide) (by decide)
  · simp only [dataDescriptor,h,ite_false]
    exact b_view_profile ht (by omega) (by have := data_input_address_bound tiles hb; omega) (data_b_base_aligned tiles)

theorem data_prefetch_a_view (tiles tile : Nat) : dataDescriptor tiles (5+7*tile) = aView 65536 tiles := by
  have h : 5 ≤ 5+7*tile ∧ (5+7*tile-5)%7 = 0 := by omega
  simp [dataDescriptor,h]

theorem data_prefetch_b_view (tiles tile : Nat) : dataDescriptor tiles (7+7*tile) = bView (dataBBase tiles) tiles := by
  have h : ¬(7+7*tile = 0 ∨ (5 ≤ 7+7*tile ∧ (7+7*tile-5)%7 = 0)) := by omega
  rw [dataDescriptor,if_neg h]

end
end Ptx.Kernels.HopperDoubleBuffer
