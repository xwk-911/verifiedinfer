import Ptx.Kernels.HopperDoubleBufferControlCtaCases

/-! Exhaustive CTA classification of the complete rich source witness and
its Hopper view. The cases retain actual generation and source-event identity. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem data_loop_cta_case (a b tiles lane n) (hn : n ≤ tiles)
    (index : Nat) (event : Wgmma.Event) (arrival : Bool) (tag : Nat × Nat)
    (he : (dataLoopEvents a b tiles lane n)[index]? = some event) (htag : sourceCtaTag arrival event = some tag) :
    CtaSource a b tiles ⟨(ctx tiles lane).id,(dataInitialEvents a b tiles lane).length+index⟩ arrival tag := by
  induction n generalizing index with
  | zero => simp [dataLoopEvents,loopEvents] at he
  | succ n ih =>
    have hs : dataLoopEvents a b tiles lane (n+1) =
        dataLoopEvents a b tiles lane n++dataIterationEvents a b tiles n lane := by
      simp only [dataLoopEvents,loopEvents,dataIterationEvents,dataCheckpoint,Nat.zero_add,zeroRetries]
    by_cases hi : index < (dataLoopEvents a b tiles lane n).length
    · rw [hs,List.getElem?_append_left hi] at he
      exact ih (by omega) index he
    · rw [hs,List.getElem?_append_right (by omega)] at he
      have hc := data_iteration_cta_case a b tiles n lane (by omega)
        (index-(dataLoopEvents a b tiles lane n).length) event arrival tag he htag
      have hindex : dataTileStart a b tiles n lane+(index-(dataLoopEvents a b tiles lane n).length) =
          (dataInitialEvents a b tiles lane).length+index := by unfold dataTileStart; omega
      simpa only [hindex] using hc

theorem data_complete_cta_case (a b tiles lane) (index : Nat) (event : Wgmma.Event) (arrival : Bool) (tag : Nat × Nat)
    (he : (dataCompleteEvents a b tiles lane)[index]? = some event) (htag : sourceCtaTag arrival event = some tag) :
    CtaSource a b tiles ⟨(ctx tiles lane).id,index⟩ arrival tag := by
  by_cases hi : index < (dataPreOutputEvents a b tiles lane).length
  · rw [dataCompleteEvents,List.getElem?_append_left hi] at he
    by_cases hz : tiles = 0
    · simp only [dataPreOutputEvents,hz,ite_true] at he
      exact data_initialization_cta_case a b tiles lane index event arrival tag he htag
    · simp only [dataPreOutputEvents,hz,ite_false,dataKernelLoopEvents] at he
      change (dataInitialEvents a b tiles lane++dataLoopEvents a b tiles lane tiles)[index]? = some event at he
      by_cases hinitial : index < (dataInitialEvents a b tiles lane).length
      · rw [List.getElem?_append_left hinitial] at he
        exact data_initial_cta_case a b tiles lane index event arrival tag he htag
      · rw [List.getElem?_append_right (by omega)] at he
        have hc := data_loop_cta_case a b tiles lane tiles (Nat.le_refl _)
          (index-(dataInitialEvents a b tiles lane).length) event arrival tag he htag
        have hindex : (dataInitialEvents a b tiles lane).length+(index-(dataInitialEvents a b tiles lane).length) = index := by omega
        simpa only [hindex] using hc
  · rw [dataCompleteEvents,List.getElem?_append_right (by omega)] at he
    have hc := data_output_cta_case a b tiles lane (index-(dataPreOutputEvents a b tiles lane).length) event arrival tag he htag
    have hindex : (dataPreOutputEvents a b tiles lane).length+(index-(dataPreOutputEvents a b tiles lane).length) = index := by omega
    simpa only [hindex] using hc

theorem data_candidate_cta_case (a b tiles) (id : Ptx.Event.EventId) (event : Wgmma.Event) (arrival : Bool) (tag : Nat × Nat)
    (he : (dataCompleteCandidate a b tiles).eventAt id = some event) (htag : sourceCtaTag arrival event = some tag) :
    CtaSource a b tiles id arrival tag := by
  obtain ⟨trace,ht,hid,hget⟩ := Unified.eventAt_trace he
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
  cases id with
  | mk thread serial =>
    cases hid
    exact data_complete_cta_case a b tiles lane serial event arrival tag hget htag

theorem view_cta_source_tag {candidate : Unified.Candidate} {id arrival tag}
    (he : candidate.view.ctaTag arrival id = some tag) :
    ∃ event, candidate.eventAt id = some event ∧ sourceCtaTag arrival event = some tag := by
  unfold Hopper.Candidate.ctaTag at he
  rw [Unified.view_eventAt] at he
  cases hr : candidate.eventAt id with
  | none => simp only [hr,Option.map_none,Option.bind_none,reduceCtorEq] at he
  | some event =>
    refine ⟨event,rfl,?_⟩
    cases hv : Unified.eventView event <;>
      try {simpa only [hr,Option.map_some,Option.bind_some,sourceCtaTag,hv] using he}
    rename_i ampere
    cases ampere <;> try {simpa only [hr,Option.map_some,Option.bind_some,sourceCtaTag,hv] using he}
    rename_i ordinary
    cases ordinary <;> simpa only [hr,Option.map_some,Option.bind_some,sourceCtaTag,hv] using he

theorem data_view_cta_case (a b tiles) (id : Ptx.Event.EventId) (arrival : Bool) (tag : Nat × Nat)
    (he : (dataCompleteCandidate a b tiles).view.ctaTag arrival id = some tag) : CtaSource a b tiles id arrival tag := by
  obtain ⟨event,hget,htag⟩ := view_cta_source_tag he
  exact data_candidate_cta_case a b tiles id event arrival tag hget htag

end
end Ptx.Kernels.HopperDoubleBuffer
