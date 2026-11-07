import Ptx.Kernels.HopperDoubleBufferDataCalls

/-! Exact source-event indices for each tile. These identify rich source
events, without asserting resource completion, memory visibility or admission. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def dataIterationEvents (a : TileA) (b : TileB) (tiles tile : Nat) (lane : Wgmma.Lane) : List Wgmma.Event :=
  iterationEvents (ctx tiles lane) (dataOracle a b tiles lane) (dataCheckpoint a b tiles lane tile).1
    tile tiles 0 (HopperStage.leader lane) 4096 4224 (dataCheckpoint a b tiles lane tile).2

def dataInitialEvents (a : TileA) (b : TileB) (tiles : Nat) (lane : Wgmma.Lane) : List Wgmma.Event :=
  initializationEvents (HopperStage.leader lane)++dataInitialCopies a b tiles (HopperStage.leader lane)

def dataTileStart (a : TileA) (b : TileB) (tiles tile : Nat) (lane : Wgmma.Lane) : Nat :=
  (dataInitialEvents a b tiles lane).length+(dataLoopEvents a b tiles lane tile).length

def dataPreludeLength (tiles tile : Nat) (lane : Wgmma.Lane) : Nat :=
  if needsPrefetch tile tiles (HopperStage.leader lane) then 3 else 0

def dataMmaIndex (a : TileA) (b : TileB) (tiles tile : Nat) (lane : Wgmma.Lane) : Nat :=
  dataTileStart a b tiles tile lane+(dataPreludeLength tiles tile lane+2)

def dataMmaId (a : TileA) (b : TileB) (tiles tile : Nat) (lane : Wgmma.Lane) : Ptx.Event.EventId :=
  ⟨(ctx tiles lane).id,dataMmaIndex a b tiles tile lane⟩

theorem data_prelude_length (a b tiles tile lane) :
    (preludeEvents (ctx tiles lane) (dataOracle a b tiles lane)
      (headerState (dataCheckpoint a b tiles lane tile).1 tile 0) tile tiles (HopperStage.leader lane) 4096 4224).length =
      dataPreludeLength tiles tile lane := by
  by_cases h : needsPrefetch tile tiles (HopperStage.leader lane) <;>
    simp [preludeEvents,dataPreludeLength,h,prefetchTransferEvents]

theorem data_iteration_length (a b tiles tile lane) :
    (dataIterationEvents a b tiles tile lane).length = dataPreludeLength tiles tile lane+7 := by
  simp only [dataIterationEvents,iterationEvents,List.length_append,List.length_replicate,
    List.length_cons,List.length_nil,computeEvents,advanceEvents,data_prelude_length]
  omega

theorem data_iteration_mma_at (a b tiles tile lane) :
    (dataIterationEvents a b tiles tile lane)[dataPreludeLength tiles tile lane+2]? =
      some (.mma (dataIterationMark a b tiles tile lane) (dataIterationCall a b tiles tile lane)) := by
  simp only [dataIterationEvents,iterationEvents,List.replicate_zero,List.nil_append,List.append_assoc]
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_cons,List.length_nil]
  rw [List.getElem?_append_right (by rw [data_prelude_length]; omega)]
  rw [data_prelude_length]
  have he : dataPreludeLength tiles tile lane+2-1-dataPreludeLength tiles tile lane = 1 := by omega
  rw [he]
  rfl

theorem data_iteration_wait_at (a b tiles tile lane) :
    (dataIterationEvents a b tiles tile lane)[0]? =
      some (waitEvent (ctx tiles lane) (barrierAddress (stage tile)) (expectedParity tile) true) := by
  simp [dataIterationEvents,iterationEvents]

theorem data_initial_length (a b tiles lane) :
    (dataInitialEvents a b tiles lane).length = if HopperStage.leader lane then 8 else 2 := by
  cases h : HopperStage.leader lane <;> simp [dataInitialEvents,initializationEvents,dataInitialCopies,h]

theorem data_loop_prefix_length (a b tiles lane n) (hn : n < tiles) :
    (dataLoopEvents a b tiles lane n).length = if HopperStage.leader lane then 10*n else 7*n := by
  induction n with
  | zero => simp [dataLoopEvents,loopEvents]
  | succ n ih =>
    have hi := ih (by omega)
    have he : dataLoopEvents a b tiles lane (n+1) = dataLoopEvents a b tiles lane n++dataIterationEvents a b tiles n lane := by
      simp only [dataLoopEvents,loopEvents,dataIterationEvents,dataCheckpoint,Nat.zero_add,zeroRetries]
    rw [he,List.length_append,hi,data_iteration_length]
    have hp : n+1 < tiles := hn
    cases hl : HopperStage.leader lane <;> simp [dataPreludeLength,needsPrefetch,hl,hp] <;> omega

theorem data_tile_start_value (a b tiles tile lane) (ht : tile < tiles) :
    dataTileStart a b tiles tile lane = if HopperStage.leader lane then 8+10*tile else 2+7*tile := by
  rw [dataTileStart,data_initial_length,data_loop_prefix_length a b tiles lane tile ht]
  cases HopperStage.leader lane <;> rfl

theorem data_mma_index_value (a b tiles tile lane) (ht : tile < tiles) :
    dataMmaIndex a b tiles tile lane =
      if HopperStage.leader lane then (if tile+1 < tiles then 13+10*tile else 10+10*tile) else 4+7*tile := by
  rw [dataMmaIndex,data_tile_start_value a b tiles tile lane ht]
  cases hl : HopperStage.leader lane <;> by_cases hp : tile+1 < tiles <;>
    simp [dataPreludeLength,needsPrefetch,hl,hp] <;> omega

theorem data_loop_index_retained (a b tiles lane) (m n index : Nat) (hle : m ≤ n) (event : Wgmma.Event)
    (he : (dataLoopEvents a b tiles lane m)[index]? = some event) :
    (dataLoopEvents a b tiles lane n)[index]? = some event := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    simpa only [hm] using he
  | succ n ih =>
    by_cases hm : m = n+1
    · simpa only [hm] using he
    · have hold := ih (by omega)
      have hi := (List.getElem?_eq_some_iff.mp hold).1
      unfold dataLoopEvents at hi
      simp only [dataLoopEvents,loopEvents]
      rw [List.getElem?_append_left hi]
      exact hold

theorem data_complete_iteration_at (a b tiles tile lane) (ht : tile < tiles) (index : Nat) (event : Wgmma.Event)
    (he : (dataIterationEvents a b tiles tile lane)[index]? = some event) :
    (dataCompleteEvents a b tiles lane)[dataTileStart a b tiles tile lane+index]? = some event := by
  have hs : (dataLoopEvents a b tiles lane (tile+1))[(dataLoopEvents a b tiles lane tile).length+index]? = some event := by
    simp only [dataLoopEvents,loopEvents,Nat.zero_add]
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    exact he
  have hf := data_loop_index_retained a b tiles lane (tile+1) tiles _ (by omega) event hs
  have hi := (List.getElem?_eq_some_iff.mp hf).1
  have hpos : tiles ≠ 0 := by omega
  simp only [dataCompleteEvents,dataPreOutputEvents,hpos,ite_false,dataKernelLoopEvents]
  change ((dataInitialEvents a b tiles lane++dataLoopEvents a b tiles lane tiles)++_)[dataTileStart a b tiles tile lane+index]? = _
  rw [List.getElem?_append_left (by simp only [List.length_append]; unfold dataTileStart; omega)]
  rw [List.getElem?_append_right (by unfold dataTileStart; omega)]
  simpa only [dataTileStart,Nat.add_assoc,Nat.add_sub_cancel_left] using hf

theorem data_complete_mma_at (a b tiles tile lane) (ht : tile < tiles) :
    (dataCompleteEvents a b tiles lane)[dataMmaIndex a b tiles tile lane]? =
      some (.mma (dataIterationMark a b tiles tile lane) (dataIterationCall a b tiles tile lane)) :=
  data_complete_iteration_at a b tiles tile lane ht _ _ (data_iteration_mma_at a b tiles tile lane)

theorem data_candidate_mma_at (a b tiles tile lane) (ht : tile < tiles) :
    (dataCompleteCandidate a b tiles).eventAt (dataMmaId a b tiles tile lane) =
      some (.mma (dataIterationMark a b tiles tile lane) (dataIterationCall a b tiles tile lane)) := by
  change (dataCompleteCandidate a b tiles).eventAt ⟨(dataCompleteTrace a b tiles lane).id,dataMmaIndex a b tiles tile lane⟩ = _
  rw [Unified.eventAt_of_member (data_source_ids_unique a b tiles)
    (List.mem_ofFn.mpr ⟨lane,rfl⟩)]
  exact data_complete_mma_at a b tiles tile lane ht

theorem data_candidate_wait_at (a b tiles tile lane) (ht : tile < tiles) :
    (dataCompleteCandidate a b tiles).eventAt ⟨(ctx tiles lane).id,dataTileStart a b tiles tile lane⟩ =
      some (waitEvent (ctx tiles lane) (barrierAddress (stage tile)) (expectedParity tile) true) := by
  change (dataCompleteCandidate a b tiles).eventAt ⟨(dataCompleteTrace a b tiles lane).id,dataTileStart a b tiles tile lane⟩ = _
  rw [Unified.eventAt_of_member (data_source_ids_unique a b tiles) (List.mem_ofFn.mpr ⟨lane,rfl⟩)]
  simpa only [Nat.add_zero,dataCompleteTrace] using data_complete_iteration_at a b tiles tile lane ht 0 _ (data_iteration_wait_at a b tiles tile lane)

end
end Ptx.Kernels.HopperDoubleBuffer
