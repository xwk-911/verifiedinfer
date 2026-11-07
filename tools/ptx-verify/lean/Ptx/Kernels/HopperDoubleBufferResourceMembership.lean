import Ptx.Kernels.HopperDoubleBufferResourceTraceCases

/-! Every classified resource origin belongs to its stage history, including
all actual notification sources. Inventory permutations are proved separately. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem data_gate_injective : Function.Injective dataGate := by
  intro left right he
  have ha := congrArg Location.address he
  apply Fin.ext
  dsimp [dataGate,barrierAddress] at ha
  omega

theorem stage_tile_index (tile : Nat) : stageTile (stage tile) (tile/2) = tile := by
  dsimp [stageTile,stage]
  omega

theorem tile_phase_in_range (tiles tile) (ht : tile < tiles) : tile/2 < uses tiles (stage tile) := by
  apply (stage_tile_in_range tiles (stage tile) (tile/2)).mp
  rwa [stage_tile_index]

theorem data_phase_member_history (a b tiles slot phase) (hp : phase < uses tiles slot)
    (entry : Tma.Entry) (he : entry ∈ dataPhaseEntries a b tiles slot phase) :
    entry ∈ dataResourceHistory a b tiles slot := by
  have hm := (data_phases_entry a b tiles slot _ entry).mpr ⟨phase,hp,he⟩
  exact List.mem_append_left _ (List.mem_append_right _ hm)

theorem data_init_member_history (a b tiles slot) :
    (⟨.source (dataInitId tiles slot),.init 1⟩ : Tma.Entry) ∈ dataResourceHistory a b tiles slot := by
  simp [dataResourceHistory]

theorem data_inval_member_history (a b tiles slot) :
    (⟨.source (dataInvalId a b tiles slot),.inval⟩ : Tma.Entry) ∈ dataResourceHistory a b tiles slot := by
  simp [dataResourceHistory]

theorem data_expect_member_history (a b tiles tile) (ht : tile < tiles) :
    (⟨.source (dataExpectId a b tiles tile),.arriveExpectTx 2304⟩ : Tma.Entry) ∈ dataResourceHistory a b tiles (stage tile) := by
  apply data_phase_member_history a b tiles (stage tile) (tile/2) (tile_phase_in_range tiles tile ht)
  simp [dataPhaseEntries,stage_tile_index]

theorem data_copy_a_member_history (a b tiles tile) (ht : tile < tiles) :
    (⟨.notification (dataCopyAId a b tiles tile),.completeTx 2048⟩ : Tma.Entry) ∈ dataResourceHistory a b tiles (stage tile) := by
  apply data_phase_member_history a b tiles (stage tile) (tile/2) (tile_phase_in_range tiles tile ht)
  simp [dataPhaseEntries,stage_tile_index]

theorem data_copy_b_member_history (a b tiles tile) (ht : tile < tiles) :
    (⟨.notification (dataCopyBId a b tiles tile),.completeTx 256⟩ : Tma.Entry) ∈ dataResourceHistory a b tiles (stage tile) := by
  apply data_phase_member_history a b tiles (stage tile) (tile/2) (tile_phase_in_range tiles tile ht)
  simp [dataPhaseEntries,stage_tile_index]

theorem data_wait_member_history (a b tiles tile lane) (ht : tile < tiles) :
    (⟨.source (dataWaitId a b tiles tile lane),.tryWaitParity (expectedParity tile) true⟩ : Tma.Entry) ∈
      dataResourceHistory a b tiles (stage tile) := by
  apply data_phase_member_history a b tiles (stage tile) (tile/2) (tile_phase_in_range tiles tile ht)
  simp only [dataPhaseEntries,stage_tile_index]
  exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨lane,rfl⟩)

theorem data_actual_resource_in_history (a b tiles) (hb : tiles ≤ 2^28) (origin : Tma.Origin) (event : BarrierEvent)
    (he : Tma.resourceAt Tma.localShared (dataCompleteCandidate a b tiles).view origin = some event) :
    ∃ slot, event.location = dataGate slot ∧
      (⟨origin,event.operation⟩ : Tma.Entry) ∈ dataResourceHistory a b tiles slot := by
  cases origin with
  | source id =>
    have hh := Unified.view_barrier_iff.mp (Hopper.barrierAt_iff.mp he)
    have hc := data_candidate_resource_case a b tiles hb id (.base (.barrier event)) hh rfl
    cases hc with
    | init slot => exact ⟨slot,rfl,data_init_member_history a b tiles slot⟩
    | inval slot => exact ⟨slot,rfl,data_inval_member_history a b tiles slot⟩
    | expect tile ht => exact ⟨stage tile,rfl,data_expect_member_history a b tiles tile ht⟩
    | wait tile lane ht => exact ⟨stage tile,rfl,data_wait_member_history a b tiles tile lane ht⟩
  | notification id =>
    cases id with
    | mk issue =>
      obtain ⟨copy,hcopy,_,_⟩ := Tma.notification_has_actual_copy he
      have hh := Unified.view_tma_iff.mp (Tma.copyAt_iff.mp hcopy)
      have hc := data_candidate_resource_case a b tiles hb issue (.base (.tmaIssue copy)) hh rfl
      cases hc with
      | copyA tile ht =>
        change Tma.notification Tma.localShared (dataCompleteCandidate a b tiles).view (dataCopyAId a b tiles tile) = some event at he
        have hv := data_source_notification_a a b tiles tile ht hb
        have hresult := Option.some.inj (he.symm.trans hv)
        subst event
        exact ⟨stage tile,rfl,data_copy_a_member_history a b tiles tile ht⟩
      | copyB tile ht =>
        change Tma.notification Tma.localShared (dataCompleteCandidate a b tiles).view (dataCopyBId a b tiles tile) = some event at he
        have hv := data_source_notification_b a b tiles tile ht hb
        have hresult := Option.some.inj (he.symm.trans hv)
        subst event
        exact ⟨stage tile,rfl,data_copy_b_member_history a b tiles tile ht⟩

end
end Ptx.Kernels.HopperDoubleBuffer
