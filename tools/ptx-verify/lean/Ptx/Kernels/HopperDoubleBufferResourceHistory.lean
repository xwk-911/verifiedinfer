import Ptx.Kernels.HopperDoubleBufferResourceEndpoints

/-! Repeated histories with actual source and implicit-notification identities.
Protocol execution and entry soundness are proved independently. Uniqueness,
exhaustiveness and source order are separate requirements of HistoryValid. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def dataPhaseEntries (a : TileA) (b : TileB) (tiles : Nat) (slot : Stage) (phase : Nat) : List Tma.Entry :=
  let tile := stageTile slot phase
  [⟨.source (dataExpectId a b tiles tile),.arriveExpectTx 2304⟩,
   ⟨.notification (dataCopyAId a b tiles tile),.completeTx 2048⟩,
   ⟨.notification (dataCopyBId a b tiles tile),.completeTx 256⟩]++
  List.ofFn (fun lane : Wgmma.Lane => (⟨.source (dataWaitId a b tiles tile lane),.tryWaitParity (phase%2) true⟩ : Tma.Entry))

def dataPhases (a : TileA) (b : TileB) (tiles : Nat) (slot : Stage) : Nat → List Tma.Entry
  | 0 => []
  | n+1 => dataPhases a b tiles slot n++dataPhaseEntries a b tiles slot n

def dataResourceHistory (a : TileA) (b : TileB) (tiles : Nat) (slot : Stage) : List Tma.Entry :=
  [⟨.source (dataInitId tiles slot),.init 1⟩]++dataPhases a b tiles slot (uses tiles slot)++
    [⟨.source (dataInvalId a b tiles slot),.inval⟩]

theorem data_phase_operations (a b tiles slot phase) :
    (dataPhaseEntries a b tiles slot phase).map Tma.Entry.operation = phaseOperations phase := by
  simp [dataPhaseEntries,phaseOperations]

theorem data_phases_operations (a b tiles slot n) :
    (dataPhases a b tiles slot n).map Tma.Entry.operation = phases n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dataPhases,List.map_append,ih,data_phase_operations,phases]

theorem data_history_operations (a b tiles slot) :
    (dataResourceHistory a b tiles slot).map Tma.Entry.operation = stageProtocol (uses tiles slot) := by
  simp only [dataResourceHistory,List.map_append,List.map_cons,List.map_nil,data_phases_operations,stageProtocol]

theorem data_history_protocol (a b tiles slot) :
    Mbarrier.run none ((dataResourceHistory a b tiles slot).map Tma.Entry.operation) = some none := by
  rw [data_history_operations]
  exact full_stage_protocol _

theorem data_phase_entry_sound (a b tiles slot phase) (hp : phase < uses tiles slot) (hb : tiles ≤ 2^28)
    (entry : Tma.Entry) (he : entry ∈ dataPhaseEntries a b tiles slot phase) :
    Tma.resourceAt Tma.localShared (dataCompleteCandidate a b tiles).view entry.origin =
      some ⟨dataGate slot,entry.operation⟩ := by
  have ht := (stage_tile_in_range tiles slot phase).mpr hp
  simp only [dataPhaseEntries,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with (rfl | rfl | rfl) | he
  · apply Hopper.barrierAt_iff.mpr
    apply Unified.view_barrier_iff.mpr
    simpa only [stage_tile_slot,dataGate] using data_source_expect a b tiles (stageTile slot phase) ht
  · simpa only [Tma.resourceAt,stage_tile_slot,dataGate] using data_source_notification_a a b tiles (stageTile slot phase) ht hb
  · simpa only [Tma.resourceAt,stage_tile_slot,dataGate] using data_source_notification_b a b tiles (stageTile slot phase) ht hb
  · obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp he
    simpa only [stage_tile_slot,stage_tile_phase] using data_resource_wait a b tiles (stageTile slot phase) lane ht

theorem data_phases_entry (a b tiles slot n) (entry : Tma.Entry) :
    entry ∈ dataPhases a b tiles slot n ↔ ∃ phase < n, entry ∈ dataPhaseEntries a b tiles slot phase := by
  induction n with
  | zero => simp [dataPhases]
  | succ n ih =>
    rw [dataPhases,List.mem_append,ih]
    constructor
    · rintro (⟨phase,hp,he⟩ | he)
      · exact ⟨phase,by omega,he⟩
      · exact ⟨n,by omega,he⟩
    · rintro ⟨phase,hp,he⟩
      by_cases hn : phase = n
      · exact Or.inr (by simpa only [hn] using he)
      · exact Or.inl ⟨phase,by omega,he⟩

theorem data_history_entry_sound (a b tiles slot) (hb : tiles ≤ 2^28)
    (entry : Tma.Entry) (he : entry ∈ dataResourceHistory a b tiles slot) :
    Tma.resourceAt Tma.localShared (dataCompleteCandidate a b tiles).view entry.origin =
      some ⟨dataGate slot,entry.operation⟩ := by
  simp only [dataResourceHistory,List.mem_append,List.mem_singleton] at he
  rcases he with (rfl | he) | rfl
  · exact data_resource_init a b tiles slot
  · obtain ⟨phase,hp,he⟩ := (data_phases_entry a b tiles slot _ entry).mp he
    exact data_phase_entry_sound a b tiles slot phase hp hb entry he
  · exact data_resource_inval a b tiles slot

theorem data_history_in_inventory (a b tiles slot) (hb : tiles ≤ 2^28) :
    ∀ entry ∈ dataResourceHistory a b tiles slot,
      entry ∈ Tma.inventory Tma.localShared (dataCompleteCandidate a b tiles).view (dataGate slot) := by
  intro entry he
  exact Tma.inventory_iff.mpr (data_history_entry_sound a b tiles slot hb entry he)

theorem data_phase_entries_length (a b tiles slot phase) : (dataPhaseEntries a b tiles slot phase).length = 131 := by
  simp [dataPhaseEntries]

theorem data_phases_length (a b tiles slot n) : (dataPhases a b tiles slot n).length = 131*n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dataPhases,List.length_append,ih,data_phase_entries_length]; omega

theorem data_history_length (a b tiles slot) : (dataResourceHistory a b tiles slot).length = 2+131*uses tiles slot := by
  simp only [dataResourceHistory,List.length_append,List.length_cons,List.length_nil,data_phases_length]
  omega

end
end Ptx.Kernels.HopperDoubleBuffer
