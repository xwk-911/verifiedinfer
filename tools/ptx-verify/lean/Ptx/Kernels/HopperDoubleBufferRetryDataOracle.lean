import Ptx.Kernels.HopperDoubleBufferRetryDataQueries

/-! Independent arbitrary-real data replies for finite heterogeneous retries.
Only pure Nat query metadata selects tiles. Matrix outputs are computed from
the input recurrence; no desired result or memory execution is assumed. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def retryDataNativeTile (tiles : Nat) (schedules : Wgmma.Lane → Nat → Nat) (lane : Wgmma.Lane) (query : Nat) : Nat :=
  if h : ∃ tile, tile < tiles ∧ retryDataNativeQuery tiles schedules lane tile = query then Classical.choose h else 0
def retryDataCopyTile (tiles : Nat) (schedules : Wgmma.Lane → Nat → Nat) (part : Fin 2) (query : Nat) : Nat :=
  if h : ∃ tile, tile < tiles ∧ retryDataCopyQuery tiles schedules tile part = query then Classical.choose h else 0
def retryDataDescriptor (tiles : Nat) (schedules : Wgmma.Lane → Nat → Nat) (query : Nat) : Tma.Descriptor2D :=
  if ∃ tile, tile < tiles ∧ retryDataCopyQuery tiles schedules tile 0 = query then aView 65536 tiles else bView (dataBBase tiles) tiles
def retryDataPayload (a : TileA) (b : TileB) (tiles : Nat) (schedules : Wgmma.Lane → Nat → Nat) (query : Nat) : List Symbolic.Byte :=
  if ∃ tile, tile < tiles ∧ retryDataCopyQuery tiles schedules tile 0 = query-1 then
    HopperStage.aPayload (a (retryDataCopyTile tiles schedules 0 (query-1)))
  else HopperStage.bPayload (b (retryDataCopyTile tiles schedules 1 (query-1)))
def retryDataOracle (a : TileA) (b : TileB) (tiles : Nat) (schedules : Wgmma.Lane → Nat → Nat) (lane : Wgmma.Lane) : Wgmma.Oracle := {
  base := {(oracle tiles).base with
    wait := fun query => if ∃ tile, tile < tiles ∧ retryDataWaitQuery tiles schedules lane tile = query then true else false
    descriptor := retryDataDescriptor tiles schedules,tmaBytes := retryDataPayload a b tiles schedules}
  matrix := fun query slot => tileReply a b (retryDataNativeTile tiles schedules lane query) (lane,slot)
  operands := fun query => Wgmma.payload (a (retryDataNativeTile tiles schedules lane query)) (b (retryDataNativeTile tiles schedules lane query))
}

theorem retry_data_native_tile_value (tiles schedules lane tile) (ht : tile < tiles) :
    retryDataNativeTile tiles schedules lane (retryDataNativeQuery tiles schedules lane tile) = tile := by
  have hx : ∃ t, t < tiles ∧ retryDataNativeQuery tiles schedules lane t = retryDataNativeQuery tiles schedules lane tile := ⟨tile,ht,rfl⟩
  rw [retryDataNativeTile,dite_eq_left hx]
  exact (retry_data_native_query_strict tiles schedules lane).injective (Classical.choose_spec hx).2

theorem retry_data_copy_tile_value (tiles schedules tile) (ht : tile < tiles) (part : Fin 2) :
    retryDataCopyTile tiles schedules part (retryDataCopyQuery tiles schedules tile part) = tile := by
  have hx : ∃ t, t < tiles ∧ retryDataCopyQuery tiles schedules t part = retryDataCopyQuery tiles schedules tile part := ⟨tile,ht,rfl⟩
  rw [retryDataCopyTile,dite_eq_left hx]
  exact (retry_data_copy_query_identity (Classical.choose_spec hx).2).1

theorem retry_data_copy_b_not_a (tiles schedules tile) :
    ¬∃ t, t < tiles ∧ retryDataCopyQuery tiles schedules t 0 = retryDataCopyQuery tiles schedules tile 1 := by
  rintro ⟨t,_,he⟩
  have hh := congrArg Fin.val (retry_data_copy_query_identity he).2
  omega

theorem retry_data_descriptor_a (tiles schedules tile) (ht : tile < tiles) :
    retryDataDescriptor tiles schedules (retryDataCopyQuery tiles schedules tile 0) = aView 65536 tiles := by
  rw [retryDataDescriptor,ite_eq_left ⟨tile,ht,rfl⟩]

theorem retry_data_descriptor_b (tiles schedules tile) :
    retryDataDescriptor tiles schedules (retryDataCopyQuery tiles schedules tile 1) = bView (dataBBase tiles) tiles := by
  rw [retryDataDescriptor,ite_eq_right (retry_data_copy_b_not_a tiles schedules tile)]

theorem retry_data_payload_a (a b tiles schedules tile) (ht : tile < tiles) :
    (retryDataOracle a b tiles schedules 0).base.tmaBytes (retryDataCopyQuery tiles schedules tile 0+1) = HopperStage.aPayload (a tile) := by
  have h : ∃ t, t < tiles ∧ retryDataCopyQuery tiles schedules t 0 = retryDataCopyQuery tiles schedules tile 0 := ⟨tile,ht,rfl⟩
  simp only [retryDataOracle,retryDataPayload,Nat.add_sub_cancel,ite_eq_left h,retry_data_copy_tile_value tiles schedules tile ht 0]

theorem retry_data_payload_b (a b tiles schedules tile) (ht : tile < tiles) :
    (retryDataOracle a b tiles schedules 0).base.tmaBytes (retryDataCopyQuery tiles schedules tile 1+1) = HopperStage.bPayload (b tile) := by
  simp only [retryDataOracle,retryDataPayload,Nat.add_sub_cancel,ite_eq_right (retry_data_copy_b_not_a tiles schedules tile),retry_data_copy_tile_value tiles schedules tile ht 1]

theorem retry_data_payload_shape (a b tiles schedules lane query) :
    ((retryDataOracle a b tiles schedules lane).base.tmaBytes (query+1)).length =
      ((retryDataOracle a b tiles schedules lane).base.descriptor query).bytes := by
  by_cases h : ∃ tile, tile < tiles ∧ retryDataCopyQuery tiles schedules tile 0 = query
  all_goals simp only [retryDataOracle,retryDataPayload,retryDataDescriptor,Nat.add_sub_cancel,h,ite_true,ite_false,
    HopperStage.a_payload_length,HopperStage.b_payload_length,aView,bView,Tma.Descriptor2D.bytes]

theorem retry_data_failed_wait (a b tiles schedules lane tile attempt) (ha : attempt < schedules lane tile) :
    (retryDataOracle a b tiles schedules lane).base.wait (retryDataQuery tiles schedules lane tile+attempt) = false := by
  have hn : ¬∃ other, other < tiles ∧ retryDataWaitQuery tiles schedules lane other = retryDataQuery tiles schedules lane tile+attempt := by
    rintro ⟨other,_,he⟩
    exact retry_data_failed_not_success tiles schedules lane tile attempt ha other he.symm
  simp only [retryDataOracle,ite_eq_right hn]

theorem retry_data_successful_wait (a b tiles schedules lane tile) (ht : tile < tiles) :
    (retryDataOracle a b tiles schedules lane).base.wait (retryDataWaitQuery tiles schedules lane tile) = true := by
  have h : ∃ t, t < tiles ∧ retryDataWaitQuery tiles schedules lane t = retryDataWaitQuery tiles schedules lane tile := ⟨tile,ht,rfl⟩
  simp only [retryDataOracle,ite_eq_left h]

theorem retry_data_loop_replies (a b tiles schedules lane tile) (ht : tile < tiles) :
    LoopReplies (retryDataOracle a b tiles schedules lane) (retryDataQuery tiles schedules lane tile)
      tile tiles (schedules lane tile) (HopperStage.leader lane) := by
  refine ⟨fun i hi => retry_data_failed_wait a b tiles schedules lane tile i hi,retry_data_successful_wait a b tiles schedules lane tile ht,?_⟩
  intro _
  constructor
  · simpa only [retryDataWaitQuery,Nat.add_assoc] using retry_data_payload_shape a b tiles schedules lane (retryDataWaitQuery tiles schedules lane tile+1)
  · simpa only [retryDataWaitQuery,Nat.add_assoc] using retry_data_payload_shape a b tiles schedules lane (retryDataWaitQuery tiles schedules lane tile+3)

theorem retry_data_native_matrix (a b tiles schedules lane tile) (ht : tile < tiles) (slot : Wgmma.Slot) :
    (retryDataOracle a b tiles schedules lane).matrix (retryDataNativeQuery tiles schedules lane tile) slot =
      result a b (tile+1) (Wgmma.cCoord (lane,slot)) := by
  simp only [retryDataOracle,retry_data_native_tile_value tiles schedules lane tile ht,tile_reply_value]

theorem retry_data_native_operands (a b tiles schedules lane tile) (ht : tile < tiles) (offset : Nat) :
    (retryDataOracle a b tiles schedules lane).operands (retryDataNativeQuery tiles schedules lane tile) offset = Wgmma.payload (a tile) (b tile) offset := by
  simp only [retryDataOracle,retry_data_native_tile_value tiles schedules lane tile ht]

def retryDataCandidate (a : TileA) (b : TileB) (tiles : Nat) (schedules : Wgmma.Lane → Nat → Nat) : Unified.Candidate :=
  replyCandidate tiles (retryDataOracle a b tiles schedules) schedules
def retryDataFamily (a : TileA) (b : TileB) (tiles : Nat) (schedules : Wgmma.Lane → Nat → Nat) : ReplySourceFamily tiles (retryDataCandidate a b tiles schedules) := {
  replies := retryDataOracle a b tiles schedules,schedules := schedules,traces := replyTrace tiles (retryDataOracle a b tiles schedules) schedules
  members := fun lane => List.mem_ofFn.mpr ⟨lane,rfl⟩,ids := fun _ => rfl,oracles := fun _ => rfl,events := fun _ => rfl
}

theorem retry_data_source (a b tiles schedules initial) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Unified.WellFormed code (completeLaunch tiles initial) (retryDataCandidate a b tiles schedules) := by
  apply reply_candidate_well_formed _ _ _ _ ht hb
  · intro lane _
    exact ⟨retry_data_payload_shape a b tiles schedules lane 0,retry_data_payload_shape a b tiles schedules lane 2⟩
  · exact fun lane tile hi => retry_data_loop_replies a b tiles schedules lane tile hi

theorem retry_data_complete (a b tiles schedules) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Unified.Complete (retryDataCandidate a b tiles schedules) := reply_candidate_complete _ _ _ ht hb

end
end Ptx.Kernels.HopperDoubleBuffer
