import Ptx.Kernels.HopperDoubleBufferResourceMembership
import Ptx.Hopper.TmaInventoryUnique

/-! Exhaustive source-matched mbarrier/TMA histories for the repeated source
witness. History admission is not combined control/memory/observer admission. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem data_inventory_in_history (a b tiles slot) (hb : tiles ≤ 2^28)
    (entry : Tma.Entry) (he : entry ∈ Tma.inventory Tma.localShared (dataCompleteCandidate a b tiles).view (dataGate slot)) :
    entry ∈ dataResourceHistory a b tiles slot := by
  cases entry with
  | mk origin op =>
    obtain ⟨actual,hloc,hm⟩ := data_actual_resource_in_history a b tiles hb origin ⟨dataGate slot,op⟩ (Tma.inventory_iff.mp he)
    have hs : slot = actual := data_gate_injective hloc
    cases hs
    exact hm

theorem data_inventory_unique (a b tiles) (loc : Location) :
    (Tma.inventory Tma.localShared (dataCompleteCandidate a b tiles).view loc).Nodup := by
  apply Tma.inventory_unique
  simpa only [Unified.Candidate.view,List.map_map,Function.comp_def,Unified.ThreadTrace.view] using data_source_ids_unique a b tiles

theorem data_history_exhaustive (a b tiles slot) (hb : tiles ≤ 2^28) :
    (dataResourceHistory a b tiles slot).Perm
      (Tma.inventory Tma.localShared (dataCompleteCandidate a b tiles).view (dataGate slot)) := by
  apply (List.perm_ext_iff_of_nodup
    (List.Nodup.of_map Tma.Entry.origin (data_history_origins_unique a b tiles slot))
    (data_inventory_unique a b tiles (dataGate slot))).mpr
  intro entry
  exact ⟨data_history_in_inventory a b tiles slot hb entry,data_inventory_in_history a b tiles slot hb entry⟩

theorem data_stage_history_valid (a b tiles slot) (hb : tiles ≤ 2^28) :
    Tma.HistoryValid Tma.localShared (dataCompleteCandidate a b tiles).view (dataGate slot) (dataResourceHistory a b tiles slot) :=
  ⟨data_history_origins_unique a b tiles slot,data_history_exhaustive a b tiles slot hb,
    data_history_source_order a b tiles slot,⟨none,data_history_protocol a b tiles slot⟩⟩

theorem data_inventory_outside_gates (a b tiles) (hb : tiles ≤ 2^28) (loc : Location)
    (hout : ∀ slot, loc ≠ dataGate slot) :
    Tma.inventory Tma.localShared (dataCompleteCandidate a b tiles).view loc = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro entry he
  cases entry with
  | mk origin op =>
    obtain ⟨slot,hloc,_⟩ := data_actual_resource_in_history a b tiles hb origin ⟨loc,op⟩ (Tma.inventory_iff.mp he)
    exact hout slot hloc

def dataHistories (a : TileA) (b : TileB) (tiles : Nat) (loc : Location) : List Tma.Entry :=
  if loc = dataGate 0 then dataResourceHistory a b tiles 0 else
  if loc = dataGate 1 then dataResourceHistory a b tiles 1 else []

theorem data_histories_at_gate (a b tiles slot) : dataHistories a b tiles (dataGate slot) = dataResourceHistory a b tiles slot := by
  fin_cases slot <;> rfl

theorem data_all_histories_valid (a b tiles) (hb : tiles ≤ 2^28) (loc : Location) :
    Tma.HistoryValid Tma.localShared (dataCompleteCandidate a b tiles).view loc (dataHistories a b tiles loc) := by
  by_cases hzero : loc = dataGate 0
  · subst loc
    rw [data_histories_at_gate]
    exact data_stage_history_valid a b tiles 0 hb
  · by_cases hone : loc = dataGate 1
    · subst loc
      rw [data_histories_at_gate]
      exact data_stage_history_valid a b tiles 1 hb
    · have hout : ∀ slot, loc ≠ dataGate slot := by intro slot; fin_cases slot <;> assumption
      have hi := data_inventory_outside_gates a b tiles hb loc hout
      simp only [dataHistories,hzero,hone,ite_false]
      refine ⟨List.nodup_nil,?_,?_,⟨none,rfl⟩⟩
      · rw [hi]
      · simp [Tma.SourceOrder]

theorem data_inventory_length (a b tiles slot) (hb : tiles ≤ 2^28) :
    (Tma.inventory Tma.localShared (dataCompleteCandidate a b tiles).view (dataGate slot)).length = 2+131*uses tiles slot := by
  rw [← (data_history_exhaustive a b tiles slot hb).length_eq,data_history_length]

theorem data_completion_observation_a (a b tiles slot phase lane) (hb : tiles ≤ 2^28) (hp : phase < uses tiles slot) :
    ∃ copy parity before after,
      Tma.copyAt (dataCompleteCandidate a b tiles).view (dataCopyAId a b tiles (stageTile slot phase)) = some copy ∧
      dataGate slot = Tma.localShared (dataCopyAId a b tiles (stageTile slot phase)).issue.thread copy.barrier ∧
      (dataCompleteCandidate a b tiles).view.barrierAt (dataWaitId a b tiles (stageTile slot phase) lane) = some ⟨dataGate slot,.tryWaitParity parity true⟩ ∧
      Mbarrier.run none (((dataResourceHistory a b tiles slot).map Tma.Entry.operation).take (noticeAIndex phase)) = some (some before) ∧
      Mbarrier.run none (((dataResourceHistory a b tiles slot).map Tma.Entry.operation).take (phaseWaitIndex phase lane)) = some (some after) ∧
      Tma.lifetimeBefore (dataResourceHistory a b tiles slot) (noticeAIndex phase) =
        Tma.lifetimeBefore (dataResourceHistory a b tiles slot) (phaseWaitIndex phase lane) ∧
      before.phase+1 = after.phase ∧ 0 < after.phase ∧ parity%2 ≠ after.phase%2 :=
  Tma.observation_actual_phase (data_stage_history_valid a b tiles slot hb) (data_observe_a a b tiles slot phase hp lane)

end
end Ptx.Kernels.HopperDoubleBuffer
