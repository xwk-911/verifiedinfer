import Ptx.Kernels.HopperDoubleBufferDataCollective

/-! Source-indexed TMA copies for every K tile, including alternating reused
slots. The implicit writes carry the logical tensor bytes; no completion,
publication, RF/co or reuse legality is inferred from these issue facts. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def dataCopyQuery (tile : Nat) : Nat := if tile = 0 then 0 else 5+7*(tile-1)
def dataCopyA (a : TileA) (tiles tile : Nat) : TmaCopy :=
  ⟨4096,aView 65536 tiles,⟨0,8*tile⟩,aBase (stage tile),barrierAddress (stage tile),dataCopyQuery tile,HopperStage.aPayload (a tile)⟩
def dataCopyB (b : TileB) (tiles tile : Nat) : TmaCopy :=
  ⟨4224,bView (dataBBase tiles) tiles,⟨0,tile⟩,bBase (stage tile),barrierAddress (stage tile),dataCopyQuery tile+2,HopperStage.bPayload (b tile)⟩
def dataCopyAId (a : TileA) (b : TileB) (tiles tile : Nat) : Tma.CopyId :=
  ⟨⟨(ctx tiles 0).id,if tile = 0 then 6 else dataTileStart a b tiles (tile-1) 0+2⟩⟩
def dataCopyBId (a : TileA) (b : TileB) (tiles tile : Nat) : Tma.CopyId :=
  ⟨⟨(ctx tiles 0).id,if tile = 0 then 7 else dataTileStart a b tiles (tile-1) 0+3⟩⟩
def dataExpectId (a : TileA) (b : TileB) (tiles tile : Nat) : Ptx.Event.EventId :=
  ⟨(ctx tiles 0).id,if tile = 0 then 5 else dataTileStart a b tiles (tile-1) 0+1⟩

theorem data_prefetch_query (a b tiles tile) (ht : tile < tiles) :
    (prefetchGuardState (headerState (dataCheckpoint a b tiles 0 tile).1 tile 0) tile tiles true).base.scalar.core.queries = 5+7*tile := by
  rw [prefetchGuardState_queries,headerState_queries,data_checkpoint_query,loop_query_before_tile tiles tile _ ht]
  change 4+7*tile+0+1 = 5+7*tile
  omega

theorem data_prefetch_copy_a (a b tiles tile) (ht : tile+1 < tiles) (hb : tiles ≤ 2^28) :
    prefetchACopy (dataOracle a b tiles 0)
      (prefetchGuardState (headerState (dataCheckpoint a b tiles 0 tile).1 tile 0) tile tiles true)
      (stage (tile+1)) (tile+1) 4096 = dataCopyA a tiles (tile+1) := by
  rw [prefetchACopy,data_prefetch_query a b tiles tile (by omega)]
  change (⟨4096,dataDescriptor tiles (5+7*tile),⟨0,Tma.signed32 (8*(tile+1))⟩,
    aBase (stage (tile+1)),barrierAddress (stage (tile+1)),5+7*tile,
    (dataOracle a b tiles 0).base.tmaBytes (5+7*tile+1)⟩ : TmaCopy) = _
  rw [show 5+7*tile+1 = 6+7*tile by omega,data_oracle_prefetch_a,data_prefetch_a_view,
    (source_coordinate_small ht hb).2.1]
  simp [dataCopyA,dataCopyQuery]

theorem data_prefetch_copy_b (a b tiles tile) (ht : tile+1 < tiles) (hb : tiles ≤ 2^28) :
    prefetchBCopy (dataOracle a b tiles 0)
      (prefetchGuardState (headerState (dataCheckpoint a b tiles 0 tile).1 tile 0) tile tiles true)
      (stage (tile+1)) (tile+1) 4224 = dataCopyB b tiles (tile+1) := by
  rw [prefetchBCopy,data_prefetch_query a b tiles tile (by omega)]
  change (⟨4224,dataDescriptor tiles (5+7*tile+2),⟨0,Tma.signed32 (tile+1)⟩,
    bBase (stage (tile+1)),barrierAddress (stage (tile+1)),5+7*tile+2,
    (dataOracle a b tiles 0).base.tmaBytes (5+7*tile+3)⟩ : TmaCopy) = _
  rw [show 5+7*tile+2 = 7+7*tile by omega,show 5+7*tile+3 = 8+7*tile by omega,
    data_oracle_prefetch_b,data_prefetch_b_view,(source_coordinate_small ht hb).2.2]
  simp [dataCopyB,dataCopyQuery]
  omega

theorem data_iteration_copy_a_at (a b tiles tile) (ht : tile+1 < tiles) (hb : tiles ≤ 2^28) :
    (dataIterationEvents a b tiles tile 0)[2]? = some (.base (.tmaIssue (dataCopyA a tiles (tile+1)))) := by
  have hn : needsPrefetch tile tiles (HopperStage.leader 0) := ⟨ht,rfl⟩
  simp only [dataIterationEvents,iterationEvents,List.replicate_zero,List.nil_append,preludeEvents,ite_eq_left hn,
    prefetchTransferEvents,List.cons_append,List.nil_append,List.getElem?_cons_succ,List.getElem?_cons_zero]
  rw [show HopperStage.leader 0 = true from rfl,data_prefetch_copy_a a b tiles tile ht hb]

theorem data_iteration_copy_b_at (a b tiles tile) (ht : tile+1 < tiles) (hb : tiles ≤ 2^28) :
    (dataIterationEvents a b tiles tile 0)[3]? = some (.base (.tmaIssue (dataCopyB b tiles (tile+1)))) := by
  have hn : needsPrefetch tile tiles (HopperStage.leader 0) := ⟨ht,rfl⟩
  simp only [dataIterationEvents,iterationEvents,List.replicate_zero,List.nil_append,preludeEvents,ite_eq_left hn,
    prefetchTransferEvents,List.cons_append,List.nil_append,List.getElem?_cons_succ,List.getElem?_cons_zero]
  rw [show HopperStage.leader 0 = true from rfl,data_prefetch_copy_b a b tiles tile ht hb]

theorem data_initial_event_at (a b tiles) (ht : 0 < tiles) (index : Nat) (event : Wgmma.Event)
    (he : (dataInitialEvents a b tiles 0)[index]? = some event) :
    (dataCompleteCandidate a b tiles).eventAt ⟨(ctx tiles 0).id,index⟩ = some event := by
  change (dataCompleteCandidate a b tiles).eventAt ⟨(dataCompleteTrace a b tiles 0).id,index⟩ = _
  rw [Unified.eventAt_of_member (data_source_ids_unique a b tiles) (List.mem_ofFn.mpr ⟨(0 : Wgmma.Lane),rfl⟩)]
  have hi := (List.getElem?_eq_some_iff.mp he).1
  change (dataCompleteEvents a b tiles 0)[index]? = _
  simp only [dataCompleteEvents,dataPreOutputEvents,Nat.ne_of_gt ht,ite_false,dataKernelLoopEvents]
  change ((dataInitialEvents a b tiles 0++_)++_)[index]? = _
  rw [List.getElem?_append_left (by simp only [List.length_append]; omega),List.getElem?_append_left hi]
  exact he

theorem data_source_copy_a (a b tiles tile) (ht : tile < tiles) (hb : tiles ≤ 2^28) :
    Tma.copyAt (dataCompleteCandidate a b tiles).view (dataCopyAId a b tiles tile) = some (dataCopyA a tiles tile) := by
  apply Tma.copyAt_iff.mpr
  apply Unified.view_tma_iff.mpr
  cases tile with
  | zero => exact data_initial_event_at a b tiles (by omega) 6 _ (by rfl)
  | succ tile =>
    change (dataCompleteCandidate a b tiles).eventAt ⟨(dataCompleteTrace a b tiles 0).id,dataTileStart a b tiles tile 0+2⟩ = _
    rw [Unified.eventAt_of_member (data_source_ids_unique a b tiles) (List.mem_ofFn.mpr ⟨(0 : Wgmma.Lane),rfl⟩)]
    exact data_complete_iteration_at a b tiles tile 0 (by omega) 2 _ (data_iteration_copy_a_at a b tiles tile ht hb)

theorem data_source_copy_b (a b tiles tile) (ht : tile < tiles) (hb : tiles ≤ 2^28) :
    Tma.copyAt (dataCompleteCandidate a b tiles).view (dataCopyBId a b tiles tile) = some (dataCopyB b tiles tile) := by
  apply Tma.copyAt_iff.mpr
  apply Unified.view_tma_iff.mpr
  cases tile with
  | zero => exact data_initial_event_at a b tiles (by omega) 7 _ (by rfl)
  | succ tile =>
    change (dataCompleteCandidate a b tiles).eventAt ⟨(dataCompleteTrace a b tiles 0).id,dataTileStart a b tiles tile 0+3⟩ = _
    rw [Unified.eventAt_of_member (data_source_ids_unique a b tiles) (List.mem_ofFn.mpr ⟨(0 : Wgmma.Lane),rfl⟩)]
    exact data_complete_iteration_at a b tiles tile 0 (by omega) 3 _ (data_iteration_copy_b_at a b tiles tile ht hb)

theorem data_source_expect (a b tiles tile) (ht : tile < tiles) :
    (dataCompleteCandidate a b tiles).eventAt (dataExpectId a b tiles tile) =
      some (.base (.barrier ⟨⟨.shared .zero,barrierAddress (stage tile)⟩,.arriveExpectTx 2304⟩)) := by
  cases tile with
  | zero => exact data_initial_event_at a b tiles (by omega) 5 _ (by rfl)
  | succ tile =>
    change (dataCompleteCandidate a b tiles).eventAt ⟨(dataCompleteTrace a b tiles 0).id,dataTileStart a b tiles tile 0+1⟩ = _
    rw [Unified.eventAt_of_member (data_source_ids_unique a b tiles) (List.mem_ofFn.mpr ⟨(0 : Wgmma.Lane),rfl⟩)]
    apply data_complete_iteration_at a b tiles tile 0 (by omega) 1
    have hn : needsPrefetch tile tiles (HopperStage.leader 0) := ⟨ht,rfl⟩
    simp only [dataIterationEvents,iterationEvents,List.replicate_zero,List.nil_append,preludeEvents,ite_eq_left hn,
      prefetchTransferEvents,List.cons_append,List.nil_append,List.getElem?_cons_succ,List.getElem?_cons_zero]
    rfl

theorem data_source_notification_a (a b tiles tile) (ht : tile < tiles) (hb : tiles ≤ 2^28) :
    Tma.notification Tma.localShared (dataCompleteCandidate a b tiles).view (dataCopyAId a b tiles tile) =
      some ⟨⟨.shared .zero,barrierAddress (stage tile)⟩,.completeTx 2048⟩ := by
  rw [Tma.notification,data_source_copy_a a b tiles tile ht hb]
  rfl

theorem data_source_notification_b (a b tiles tile) (ht : tile < tiles) (hb : tiles ≤ 2^28) :
    Tma.notification Tma.localShared (dataCompleteCandidate a b tiles).view (dataCopyBId a b tiles tile) =
      some ⟨⟨.shared .zero,barrierAddress (stage tile)⟩,.completeTx 256⟩ := by
  rw [Tma.notification,data_source_copy_b a b tiles tile ht hb]
  rfl

theorem data_transfer_a_byte (a b tiles tile) (ht : tile < tiles) (hb : tiles ≤ 2^28) (offset : Fin 2048) :
    Tma.transferByte (dataCompleteCandidate a b tiles).view (dataCopyAId a b tiles tile) offset.val =
      some (dataSharedTile a b tile ⟨.shared .zero,aBase (stage tile)+offset.val⟩) := by
  rw [Tma.transferByte,data_source_copy_a a b tiles tile ht hb]
  change (HopperStage.aPayload (a tile))[offset.val]? = _
  have hp := HopperStage.transfer_a_payload (a tile) (b tile) offset
  simpa only [dataSharedTile,HopperStage.transferView,Wgmma.tileMemory,Nat.add_sub_cancel_left] using hp

theorem data_transfer_b_byte (a b tiles tile) (ht : tile < tiles) (hb : tiles ≤ 2^28) (offset : Fin 256) :
    Tma.transferByte (dataCompleteCandidate a b tiles).view (dataCopyBId a b tiles tile) offset.val =
      some (dataSharedTile a b tile ⟨.shared .zero,bBase (stage tile)+offset.val⟩) := by
  rw [Tma.transferByte,data_source_copy_b a b tiles tile ht hb]
  change (HopperStage.bPayload (b tile))[offset.val]? = _
  have hp := HopperStage.transfer_b_payload (a tile) (b tile) offset
  have hs : bBase (stage tile)+offset.val-aBase (stage tile) = 2048+offset.val := by dsimp [aBase,bBase]; omega
  have hs0 : 2064+offset.val-16 = 2048+offset.val := by omega
  simpa only [dataSharedTile,HopperStage.transferView,Wgmma.tileMemory,hs,hs0] using hp

theorem data_transfer_a_location (a b tiles tile) (ht : tile < tiles) (hb : tiles ≤ 2^28) (offset : Fin 2048) :
    Tma.writeLocation Tma.localShared (dataCompleteCandidate a b tiles).view (dataCopyAId a b tiles tile) offset.val =
      some ⟨.shared .zero,aBase (stage tile)+offset.val⟩ := by
  rw [Tma.writeLocation,data_source_copy_a a b tiles tile ht hb]
  change (if offset.val < 2048 then some ((Tma.localShared (dataCopyAId a b tiles tile).issue.thread (aBase (stage tile))).add offset.val) else none) = _
  rw [ite_eq_left offset.isLt]
  rfl

theorem data_transfer_b_location (a b tiles tile) (ht : tile < tiles) (hb : tiles ≤ 2^28) (offset : Fin 256) :
    Tma.writeLocation Tma.localShared (dataCompleteCandidate a b tiles).view (dataCopyBId a b tiles tile) offset.val =
      some ⟨.shared .zero,bBase (stage tile)+offset.val⟩ := by
  rw [Tma.writeLocation,data_source_copy_b a b tiles tile ht hb]
  change (if offset.val < 256 then some ((Tma.localShared (dataCopyBId a b tiles tile).issue.thread (bBase (stage tile))).add offset.val) else none) = _
  rw [ite_eq_left offset.isLt]
  rfl

theorem data_operand_a_transfer (a b tiles tile lane) (ht : tile < tiles) (hb : tiles ≤ 2^28)
    (p : Wgmma.ACoord) (byte : Fin 2) :
    Tma.writeLocation Tma.localShared (dataCompleteCandidate a b tiles).view (dataCopyAId a b tiles tile) (Wgmma.aOffset (p,byte)).val =
        some (Wgmma.operandLocation .zero (dataIterationCall a b tiles tile lane) (.a p byte)) ∧
      Tma.transferByte (dataCompleteCandidate a b tiles).view (dataCopyAId a b tiles tile) (Wgmma.aOffset (p,byte)).val =
        some ((dataIterationCall a b tiles tile lane).operandBytes (Wgmma.OperandByte.a p byte).index) := by
  have hl : Wgmma.operandLocation .zero (dataIterationCall a b tiles tile lane) (.a p byte) =
      ⟨.shared .zero,aBase (stage tile)+(Wgmma.aOffset (p,byte)).val⟩ := by
    simp only [Wgmma.operandLocation,data_call_a,a_operand_address]
  constructor
  · rw [hl]
    exact data_transfer_a_location a b tiles tile ht hb _
  · rw [data_transfer_a_byte a b tiles tile ht hb]
    have hv := data_call_agreement a b tiles tile lane ht (.a p byte)
    rw [hl] at hv
    exact congrArg some hv.symm

theorem data_operand_b_transfer (a b tiles tile lane) (ht : tile < tiles) (hb : tiles ≤ 2^28)
    (p : Wgmma.BCoord) (byte : Fin 2) :
    Tma.writeLocation Tma.localShared (dataCompleteCandidate a b tiles).view (dataCopyBId a b tiles tile) (Wgmma.bOffset (p,byte)).val =
        some (Wgmma.operandLocation .zero (dataIterationCall a b tiles tile lane) (.b p byte)) ∧
      Tma.transferByte (dataCompleteCandidate a b tiles).view (dataCopyBId a b tiles tile) (Wgmma.bOffset (p,byte)).val =
        some ((dataIterationCall a b tiles tile lane).operandBytes (Wgmma.OperandByte.b p byte).index) := by
  have hl : Wgmma.operandLocation .zero (dataIterationCall a b tiles tile lane) (.b p byte) =
      ⟨.shared .zero,bBase (stage tile)+(Wgmma.bOffset (p,byte)).val⟩ := by
    simp only [Wgmma.operandLocation,data_call_b,b_operand_address]
  constructor
  · rw [hl]
    exact data_transfer_b_location a b tiles tile ht hb _
  · rw [data_transfer_b_byte a b tiles tile ht hb]
    have hv := data_call_agreement a b tiles tile lane ht (.b p byte)
    rw [hl] at hv
    exact congrArg some hv.symm

end
end Ptx.Kernels.HopperDoubleBuffer
