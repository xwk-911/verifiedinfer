import Ptx.Kernels.HopperDoubleBufferRetryArrivalPrefixes

/-! Intended successful-wait phases for arbitrary admitted histories. The proof
combines actual CTA reuse bounds, source-ordered waits, lifetime monotonicity
and counted protocol state; it does not identify phases by parity alone. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def actualWaitIndex {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (histories : Location → List Tma.Entry) (tile : Nat) (lane : Wgmma.Lane) : Nat :=
  ((histories (dataGate (stage tile))).map Tma.Entry.origin).idxOf (.source (family.waitId tile lane))
def actualNoticeIndex {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (histories : Location → List Tma.Entry) (first : Bool) (tile : Nat) : Nat :=
  ((histories (dataGate (stage tile))).map Tma.Entry.origin).idxOf (.notification (accountedCopyId family first tile))

theorem arbitrary_history_wait_exact_phase {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (slot phase) (hp : phase < uses tiles slot) (lane : Wgmma.Lane) :
    ∃ state, Mbarrier.run none (((histories (dataGate slot)).map Tma.Entry.operation).take
      (actualWaitIndex family histories (stageTile slot phase) lane)) = some (some state) ∧ state.phase = phase+1 := by
  revert hp
  induction phase using Nat.strong_induction_on with
  | h phase ih =>
    intro hp
    have htile := (stage_tile_in_range tiles slot phase).mpr hp
    obtain ⟨state,hraw,_,_,_,_,hpositive,hparity⟩ := arbitrary_history_wait_accounting family ht hw hd hh (stageTile slot phase) htile lane
    have hr : Mbarrier.run none (((histories (dataGate slot)).map Tma.Entry.operation).take
        (actualWaitIndex family histories (stageTile slot phase) lane)) = some (some state) := by
      simpa only [actualWaitIndex,stage_tile_slot] using hraw
    have hdiv : stageTile slot phase/2 = phase := by
      have := slot.isLt
      dsimp only [stageTile]
      omega
    have hbound := arbitrary_history_wait_arrival_bound family ht hw hd hh hc (stageTile slot phase) htile lane
      (actualWaitIndex family histories (stageTile slot phase) lane) (Nat.le_succ _)
    have hcount : Mbarrier.arrivalCount (((histories (dataGate slot)).map Tma.Entry.operation).take
        (actualWaitIndex family histories (stageTile slot phase) lane)) ≤ phase+1 := by
      simpa only [stage_tile_slot,hdiv] using hbound
    have hpbound := (arbitrary_history_phase_count_bounds family ht hw hd hh slot _ state hr).1
    have hupper : state.phase ≤ phase+1 := by omega
    have hpar : phase%2 ≠ state.phase%2 := by
      simpa only [stage_tile_phase,Nat.mod_mod] using hparity
    have hexact : state.phase = phase+1 := by
      cases phase with
      | zero => omega
      | succ previous =>
        obtain ⟨before,hbefore,hbeforePhase⟩ := ih previous (by omega) (by omega)
        have horder := arbitrary_history_wait_before_wait family hw hh (stageTile slot previous) (stageTile slot (previous+1))
          (by dsimp only [stageTile]; omega) htile (by rw [stage_tile_slot,stage_tile_slot]) lane
        have hindex : actualWaitIndex family histories (stageTile slot previous) lane ≤
            actualWaitIndex family histories (stageTile slot (previous+1)) lane := by
          simpa only [actualWaitIndex,stage_tile_slot] using Nat.le_of_lt horder.2.2
        have hm := arbitrary_history_prefix_phase_mono family ht hw hd hh slot _ _ before state hindex hbefore hr
        omega
    exact ⟨state,hr,hexact⟩

theorem arbitrary_history_wait_state {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (tile : Nat) (hlt : tile < tiles) (lane : Wgmma.Lane) :
    ∃ state, Mbarrier.run none (((histories (dataGate (stage tile))).map Tma.Entry.operation).take
      (actualWaitIndex family histories tile lane)) = some (some state) ∧
      state.phase = tile/2+1 ∧ state.pending = 1 ∧ state.tx = 0 ∧
      Mbarrier.arrivalCount (((histories (dataGate (stage tile))).map Tma.Entry.operation).take
        (actualWaitIndex family histories tile lane)) = tile/2+1 ∧
      Tma.stampBefore (histories (dataGate (stage tile))) (actualWaitIndex family histories tile lane) = some ⟨1,tile/2+1⟩ := by
  obtain ⟨state,hr,hphase⟩ := arbitrary_history_wait_exact_phase family ht hw hd hh hc (stage tile) (tile/2)
    (tile_phase_in_range tiles tile hlt) lane
  rw [stage_tile_index] at hr
  obtain ⟨_,hpending,hbalance,_⟩ := arbitrary_history_prefix_accounting family ht hw hd hh (stage tile) _ state hr
  have hbound := arbitrary_history_wait_arrival_bound family ht hw hd hh hc tile hlt lane
    (actualWaitIndex family histories tile lane) (Nat.le_succ _)
  have hcount : Mbarrier.arrivalCount (((histories (dataGate (stage tile))).map Tma.Entry.operation).take
      (actualWaitIndex family histories tile lane)) = tile/2+1 := by omega
  have hready : state.pending = 1 := by omega
  have htx := arbitrary_prefix_settled_transactions_zero family ht hw hd hh hc (stage tile) _ state hr (hphase.trans hcount.symm)
  have hs := arbitrary_history_live_prefix_stamp family ht hw hd hh (stage tile) _ state hr
  rw [hphase] at hs
  exact ⟨state,hr,hphase,hready,htx,hcount,hs⟩

end
end Ptx.Kernels.HopperDoubleBuffer
