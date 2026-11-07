import Ptx.Kernels.HopperDoubleBufferTmaInputs
import Ptx.Kernels.HopperDoubleBufferProtocol
import Ptx.Hopper.TmaObservation

/-! Actual source IDs of each barrier's initialization, waits and invalidation.
These endpoint facts alone do not admit a resource history or memory graph. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def dataInitId (tiles : Nat) (slot : Stage) : Ptx.Event.EventId := ⟨(ctx tiles 0).id,slot.val⟩
def dataWaitId (a : TileA) (b : TileB) (tiles tile : Nat) (lane : Wgmma.Lane) : Ptx.Event.EventId :=
  ⟨(ctx tiles lane).id,dataTileStart a b tiles tile lane⟩
def dataInvalId (a : TileA) (b : TileB) (tiles : Nat) (slot : Stage) : Ptx.Event.EventId :=
  ⟨(ctx tiles 0).id,(dataPreOutputEvents a b tiles 0).length+6+slot.val⟩
def dataGate (slot : Stage) : Location := ⟨.shared .zero,barrierAddress slot⟩

theorem data_complete_initialization_at (a b tiles lane) (index : Nat) (event : Wgmma.Event)
    (he : (initializationEvents (HopperStage.leader lane))[index]? = some event) :
    (dataCompleteCandidate a b tiles).eventAt ⟨(ctx tiles lane).id,index⟩ = some event := by
  change (dataCompleteCandidate a b tiles).eventAt ⟨(dataCompleteTrace a b tiles lane).id,index⟩ = _
  rw [Unified.eventAt_of_member (data_source_ids_unique a b tiles) (List.mem_ofFn.mpr ⟨lane,rfl⟩)]
  have hi := (List.getElem?_eq_some_iff.mp he).1
  change (dataCompleteEvents a b tiles lane)[index]? = _
  by_cases ht : tiles = 0
  · simp only [dataCompleteEvents,dataPreOutputEvents,ht,ite_true]
    rw [List.getElem?_append_left hi]
    exact he
  · simp only [dataCompleteEvents,dataPreOutputEvents,ht,ite_false,dataKernelLoopEvents,List.append_assoc]
    rw [List.getElem?_append_left hi]
    exact he

theorem data_source_init (a b tiles slot) :
    (dataCompleteCandidate a b tiles).eventAt (dataInitId tiles slot) =
      some (.base (.barrier ⟨dataGate slot,.init 1⟩)) := by
  apply data_complete_initialization_at a b tiles 0 slot.val
  fin_cases slot <;> rfl

theorem data_source_inval (a b tiles slot) :
    (dataCompleteCandidate a b tiles).eventAt (dataInvalId a b tiles slot) =
      some (.base (.barrier ⟨dataGate slot,.inval⟩)) := by
  change (dataCompleteCandidate a b tiles).eventAt
    ⟨(dataCompleteTrace a b tiles 0).id,(dataPreOutputEvents a b tiles 0).length+6+slot.val⟩ = _
  rw [Unified.eventAt_of_member (data_source_ids_unique a b tiles) (List.mem_ofFn.mpr ⟨(0 : Wgmma.Lane),rfl⟩)]
  change (dataCompleteEvents a b tiles 0)[(dataPreOutputEvents a b tiles 0).length+6+slot.val]? = _
  rw [dataCompleteEvents,List.getElem?_append_right (by omega)]
  have he : (dataPreOutputEvents a b tiles 0).length+6+slot.val-(dataPreOutputEvents a b tiles 0).length = 6+slot.val := by omega
  rw [he]
  fin_cases slot <;> rfl

theorem data_resource_init (a b tiles slot) :
    Tma.resourceAt Tma.localShared (dataCompleteCandidate a b tiles).view (.source (dataInitId tiles slot)) =
      some ⟨dataGate slot,.init 1⟩ := by
  apply Hopper.barrierAt_iff.mpr
  exact Unified.view_barrier_iff.mpr (data_source_init a b tiles slot)

theorem data_resource_inval (a b tiles slot) :
    Tma.resourceAt Tma.localShared (dataCompleteCandidate a b tiles).view (.source (dataInvalId a b tiles slot)) =
      some ⟨dataGate slot,.inval⟩ := by
  apply Hopper.barrierAt_iff.mpr
  exact Unified.view_barrier_iff.mpr (data_source_inval a b tiles slot)

theorem data_resource_wait (a b tiles tile lane) (ht : tile < tiles) :
    Tma.resourceAt Tma.localShared (dataCompleteCandidate a b tiles).view (.source (dataWaitId a b tiles tile lane)) =
      some ⟨dataGate (stage tile),.tryWaitParity (expectedParity tile) true⟩ := by
  apply Hopper.barrierAt_iff.mpr
  apply Unified.view_barrier_iff.mpr
  exact data_candidate_wait_at a b tiles tile lane ht

def stageTile (slot : Stage) (phase : Nat) : Nat := 2*phase+slot.val

theorem stage_tile_slot (slot phase) : stage (stageTile slot phase) = slot := by
  apply Fin.ext
  have := slot.isLt
  dsimp [stage,stageTile]
  omega
theorem stage_tile_phase (slot phase) : expectedParity (stageTile slot phase) = phase%2 := by
  have := slot.isLt
  dsimp [expectedParity,stageTile]
  omega
theorem stage_tile_in_range (tiles slot phase) : stageTile slot phase < tiles ↔ phase < uses tiles slot := by
  have := slot.isLt
  dsimp [stageTile,uses]
  omega

end
end Ptx.Kernels.HopperDoubleBuffer
