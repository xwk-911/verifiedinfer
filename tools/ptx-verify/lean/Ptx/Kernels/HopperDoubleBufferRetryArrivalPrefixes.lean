import Ptx.Kernels.HopperDoubleBufferRetryMatchedPrefixes
import Ptx.Hopper.MbarrierPhaseMonotone

/-! Actual arrival inventories bound arbitrary history prefixes. All-lane CTA
reuse control excludes later same-slot expects through the current wait. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem arbitrary_history_arrival_entry_case {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc)) (slot entry)
    (he : entry ∈ histories (dataGate slot)) (hop : Tma.isArrivalEntry entry = true) :
    ∃ tile, tile < tiles ∧ stage tile = slot ∧ entry = ⟨.source (family.expectId tile),.arriveExpectTx 2304⟩ := by
  have hp := (hh (dataGate slot)).exhaustive.trans (retry_history_exhaustive family ht hw hd slot).symm
  have hm := hp.mem_iff.mp he
  simp only [retryResourceHistory,List.mem_append,List.mem_singleton] at hm
  rcases hm with (rfl | hm) | rfl
  · simp [Tma.isArrivalEntry] at hop
  · obtain ⟨phase,hphase,hm⟩ := (retry_phases_entry family slot _ entry).mp hm
    have hc := retry_phase_entry_case family slot phase entry hm
    refine ⟨stageTile slot phase,(stage_tile_in_range tiles slot phase).mpr hphase,stage_tile_slot slot phase,?_⟩
    cases hc <;> simp_all [Tma.isArrivalEntry]
  · simp [Tma.isArrivalEntry] at hop

theorem arbitrary_prefix_arrival_count_bound {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc)) (slot cut limit)
    (hb : ∀ tile, tile < tiles → stage tile = slot →
      Tma.Origin.source (family.expectId tile) ∈ ((histories (dataGate slot)).take cut).map Tma.Entry.origin → tile/2 < limit) :
    Mbarrier.arrivalCount (((histories (dataGate slot)).map Tma.Entry.operation).take cut) ≤ limit := by
  rw [← List.map_take,← Tma.arrival_entries_count]
  have hu := ((List.Nodup.of_map Tma.Entry.origin (hh (dataGate slot)).unique).sublist (List.take_sublist cut _)).filter Tma.isArrivalEntry
  let bound := List.ofFn (fun phase : Fin limit => (⟨.source (family.expectId (stageTile slot phase)),.arriveExpectTx 2304⟩ : Tma.Entry))
  have hs : ((histories (dataGate slot)).take cut).filter Tma.isArrivalEntry ⊆ bound := by
    intro entry he
    obtain ⟨hmem,hop⟩ := List.mem_filter.mp he
    obtain ⟨tile,htile,hslot,rfl⟩ := arbitrary_history_arrival_entry_case family ht hw hd hh slot entry (List.mem_of_mem_take hmem) hop
    have hp := hb tile htile hslot (List.mem_map.mpr ⟨_,hmem,rfl⟩)
    apply List.mem_ofFn.mpr
    refine ⟨⟨tile/2,hp⟩,?_⟩
    have he : stageTile slot (tile/2) = tile := by rw [← hslot]; exact stage_tile_index tile
    simp only [he]
  have hlen := hu.length_le_of_subset hs
  simpa only [bound,List.length_ofFn] using hlen

theorem arbitrary_history_wait_arrival_bound {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (tile : Nat) (hlt : tile < tiles) (lane : Wgmma.Lane) (cut : Nat)
    (hcut : cut ≤ ((histories (dataGate (stage tile))).map Tma.Entry.origin).idxOf (.source (family.waitId tile lane))+1) :
    Mbarrier.arrivalCount (((histories (dataGate (stage tile))).map Tma.Entry.operation).take cut) ≤ tile/2+1 := by
  apply arbitrary_prefix_arrival_count_bound family ht hw hd hh (stage tile) cut (tile/2+1)
  intro next hn hs hp
  have hle : next ≤ tile := by
    by_contra hhigher
    have hnot := arbitrary_history_wait_prefix_excludes_later_expect family hw hh hc tile next (by omega) hn hs.symm lane cut hcut
    exact hnot hp
  omega

theorem arbitrary_history_wait_before_wait {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (left right : Nat) (hlt : left < right) (hr : right < tiles) (hs : stage left = stage right) (lane : Wgmma.Lane) :
    Tma.Before (histories (dataGate (stage right))) (.source (family.waitId left lane)) (.source (family.waitId right lane)) := by
  have ha := retry_wait_resource_at family hw left (by omega) lane
  rw [hs] at ha
  have hb := retry_wait_resource_at family hw right hr lane
  have hma := Tma.history_complete (hh _) ha
  have hmb := Tma.history_complete (hh _) hb
  refine ⟨List.mem_map.mpr ⟨_,hma,rfl⟩,List.mem_map.mpr ⟨_,hmb,rfl⟩,(hh _).ordered _ hma _ hmb ⟨rfl,?_⟩⟩
  exact reply_waits_separated tiles lane (family.replies lane) (family.schedules lane) left right _ _ hlt (Nat.le_refl _)

theorem arbitrary_history_prefix_phase_mono {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc)) (slot first last before after)
    (hl : first ≤ last)
    (hb : Mbarrier.run none (((histories (dataGate slot)).map Tma.Entry.operation).take first) = some (some before))
    (ha : Mbarrier.run none (((histories (dataGate slot)).map Tma.Entry.operation).take last) = some (some after)) : before.phase ≤ after.phase := by
  obtain ⟨hi,hu⟩ := arbitrary_history_accounting_inventory family ht hw hd hh slot
  obtain ⟨final,hr⟩ := (hh (dataGate slot)).protocol
  exact Mbarrier.single_initialization_phase_mono hi (fun op hop => (hu op hop).1) hr hl hb ha

end
end Ptx.Kernels.HopperDoubleBuffer
