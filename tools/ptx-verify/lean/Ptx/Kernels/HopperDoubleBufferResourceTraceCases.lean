import Ptx.Kernels.HopperDoubleBufferResourceCases

/-! Exhaustive indexed classification through actual initial, loop and return
trace pieces. Candidate-wide inventory admission is proved separately. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem data_initialization_resource_case (a b tiles lane) (index : Nat) (event : Wgmma.Event)
    (he : (initializationEvents (HopperStage.leader lane))[index]? = some event) (hr : isResourceEvent event = true) :
    DataResourceSource a b tiles ⟨(ctx tiles lane).id,index⟩ event := by
  have hi := (List.getElem?_eq_some_iff.mp he).1
  cases hl : HopperStage.leader lane
  · rw [hl] at he hi
    have hb : index < 2 := hi
    interval_cases index <;> cases he <;> cases hr
  · have hz : lane = 0 := (leader_iff_zero lane).mp hl
    subst lane
    have hb : index < 5 := hi
    interval_cases index
    · cases he; exact DataResourceSource.init 0
    · cases he; exact DataResourceSource.init 1
    all_goals cases he; cases hr

theorem data_initial_resource_case (a b tiles lane) (ht : 0 < tiles) (index : Nat) (event : Wgmma.Event)
    (he : (dataInitialEvents a b tiles lane)[index]? = some event) (hr : isResourceEvent event = true) :
    DataResourceSource a b tiles ⟨(ctx tiles lane).id,index⟩ event := by
  have hi := (List.getElem?_eq_some_iff.mp he).1
  rw [data_initial_length] at hi
  cases hl : HopperStage.leader lane
  · have hb : index < 2 := by simpa only [hl,Bool.false_eq_true,ite_false] using hi
    interval_cases index
    all_goals simp only [dataInitialEvents,hl,initializationEvents,dataInitialCopies,Bool.false_eq_true,ite_false,
      List.nil_append,List.append_nil,List.getElem?_cons_succ,List.getElem?_cons_zero] at he
    all_goals cases he; cases hr
  · have hz : lane = 0 := (leader_iff_zero lane).mp hl
    subst lane
    have hb : index < 8 := hi
    interval_cases index
    · cases he; exact DataResourceSource.init 0
    · cases he; exact DataResourceSource.init 1
    · cases he; cases hr
    · cases he; cases hr
    · cases he; cases hr
    · cases he; exact DataResourceSource.expect 0 ht
    · cases he; exact DataResourceSource.copyA 0 ht
    · cases he; exact DataResourceSource.copyB 0 ht

theorem data_loop_resource_case (a b tiles lane n) (hn : n ≤ tiles) (hb : tiles ≤ 2^28)
    (index : Nat) (event : Wgmma.Event)
    (he : (dataLoopEvents a b tiles lane n)[index]? = some event) (hr : isResourceEvent event = true) :
    DataResourceSource a b tiles ⟨(ctx tiles lane).id,(dataInitialEvents a b tiles lane).length+index⟩ event := by
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
      have hc := data_iteration_resource_case a b tiles n lane (by omega) hb
        (index-(dataLoopEvents a b tiles lane n).length) event he hr
      have hindex : dataTileStart a b tiles n lane+(index-(dataLoopEvents a b tiles lane n).length) =
          (dataInitialEvents a b tiles lane).length+index := by unfold dataTileStart; omega
      simpa only [hindex] using hc

theorem data_output_resource_case (a b tiles lane) (index : Nat) (event : Wgmma.Event)
    (he : (outputEvents (ctx tiles lane) (dataPreOutputState a b tiles lane) lane (HopperStage.leader lane)
      (fun slot => result a b tiles (Wgmma.cCoord (lane,slot))))[index]? = some event)
    (hr : isResourceEvent event = true) :
    DataResourceSource a b tiles ⟨(ctx tiles lane).id,(dataPreOutputEvents a b tiles lane).length+index⟩ event := by
  have hi := (List.getElem?_eq_some_iff.mp he).1
  cases hl : HopperStage.leader lane
  · have hb : index < 6 := by simpa only [outputEvents,returnEvents,hl,Bool.false_eq_true,ite_false,
        List.length_append,outputWriteEvents,List.length_cons,List.length_nil] using hi
    interval_cases index
    all_goals simp only [outputEvents,returnEvents,hl,Bool.false_eq_true,ite_false,outputWriteEvents,
      List.cons_append,List.nil_append,List.getElem?_cons_succ,List.getElem?_cons_zero] at he
    all_goals cases he; cases hr
  · have hz : lane = 0 := (leader_iff_zero lane).mp hl
    subst lane
    have hb : index < 8 := by simpa only [outputEvents,returnEvents,hl,ite_true,
        List.length_append,outputWriteEvents,List.length_cons,List.length_nil] using hi
    interval_cases index
    all_goals first
      | (cases he; exact DataResourceSource.inval 0)
      | (cases he; exact DataResourceSource.inval 1)
      | (simp only [outputEvents,returnEvents,hl,ite_true,outputWriteEvents,
          List.cons_append,List.nil_append,List.getElem?_cons_succ,List.getElem?_cons_zero] at he
         cases he
         cases hr)

theorem data_complete_resource_case (a b tiles lane) (hb : tiles ≤ 2^28) (index : Nat) (event : Wgmma.Event)
    (he : (dataCompleteEvents a b tiles lane)[index]? = some event) (hr : isResourceEvent event = true) :
    DataResourceSource a b tiles ⟨(ctx tiles lane).id,index⟩ event := by
  by_cases hi : index < (dataPreOutputEvents a b tiles lane).length
  · rw [dataCompleteEvents,List.getElem?_append_left hi] at he
    by_cases hz : tiles = 0
    · simp only [dataPreOutputEvents,hz,ite_true] at he
      exact data_initialization_resource_case a b tiles lane index event he hr
    · simp only [dataPreOutputEvents,hz,ite_false,dataKernelLoopEvents] at he
      change (dataInitialEvents a b tiles lane++dataLoopEvents a b tiles lane tiles)[index]? = some event at he
      by_cases hinitial : index < (dataInitialEvents a b tiles lane).length
      · rw [List.getElem?_append_left hinitial] at he
        exact data_initial_resource_case a b tiles lane (Nat.pos_of_ne_zero hz) index event he hr
      · rw [List.getElem?_append_right (by omega)] at he
        have hc := data_loop_resource_case a b tiles lane tiles (Nat.le_refl _) hb
          (index-(dataInitialEvents a b tiles lane).length) event he hr
        have hindex : (dataInitialEvents a b tiles lane).length+(index-(dataInitialEvents a b tiles lane).length) = index := by omega
        simpa only [hindex] using hc
  · rw [dataCompleteEvents,List.getElem?_append_right (by omega)] at he
    have hc := data_output_resource_case a b tiles lane (index-(dataPreOutputEvents a b tiles lane).length) event he hr
    have hindex : (dataPreOutputEvents a b tiles lane).length+(index-(dataPreOutputEvents a b tiles lane).length) = index := by omega
    simpa only [hindex] using hc

theorem data_candidate_resource_case (a b tiles) (hb : tiles ≤ 2^28) (id : Ptx.Event.EventId) (event : Wgmma.Event)
    (he : (dataCompleteCandidate a b tiles).eventAt id = some event) (hr : isResourceEvent event = true) :
    DataResourceSource a b tiles id event := by
  obtain ⟨trace,ht,hid,hget⟩ := Unified.eventAt_trace he
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
  cases id with
  | mk thread serial =>
    cases hid
    exact data_complete_resource_case a b tiles lane hb serial event hget hr

end
end Ptx.Kernels.HopperDoubleBuffer
