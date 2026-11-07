import Ptx.Kernels.HopperDoubleBufferNativeCases

/-! Exhaustive native-signature classification of the complete rich trace.
The zero-tile path and output suffix contain no native operations. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem data_loop_native_source (a b tiles lane n) (hn : n ≤ tiles)
    (index : Nat) (event : Wgmma.Event) (signature : Wgmma.SourceSignature)
    (he : (dataLoopEvents a b tiles lane n)[index]? = some event) (hs : dataAlignedSignature event = some signature) :
    NativeSource a b tiles ⟨(ctx tiles lane).id,(dataInitialEvents a b tiles lane).length+index⟩ signature := by
  induction n generalizing index with
  | zero => simp [dataLoopEvents,loopEvents] at he
  | succ n ih =>
    have hstep : dataLoopEvents a b tiles lane (n+1) = dataLoopEvents a b tiles lane n++dataIterationEvents a b tiles n lane := by
      simp only [dataLoopEvents,loopEvents,dataIterationEvents,dataCheckpoint,Nat.zero_add,zeroRetries]
    by_cases hi : index < (dataLoopEvents a b tiles lane n).length
    · rw [hstep,List.getElem?_append_left hi] at he
      exact ih (by omega) index he
    · rw [hstep,List.getElem?_append_right (by omega)] at he
      have hc := data_iteration_native_source a b tiles n lane (by omega)
        (index-(dataLoopEvents a b tiles lane n).length) event signature he hs
      have hindex : dataTileStart a b tiles n lane+(index-(dataLoopEvents a b tiles lane n).length) =
          (dataInitialEvents a b tiles lane).length+index := by unfold dataTileStart; omega
      simpa only [hindex] using hc

theorem data_complete_native_source (a b tiles lane)
    (index : Nat) (event : Wgmma.Event) (signature : Wgmma.SourceSignature)
    (he : (dataCompleteEvents a b tiles lane)[index]? = some event) (hs : dataAlignedSignature event = some signature) :
    NativeSource a b tiles ⟨(ctx tiles lane).id,index⟩ signature := by
  by_cases hi : index < (dataPreOutputEvents a b tiles lane).length
  · rw [dataCompleteEvents,List.getElem?_append_left hi] at he
    by_cases hz : tiles = 0
    · simp only [dataPreOutputEvents,hz,ite_true] at he
      exact (signature_absent_of_empty_schedule (data_initialization_schedule _) he hs).elim
    · simp only [dataPreOutputEvents,hz,ite_false,dataKernelLoopEvents] at he
      change (dataInitialEvents a b tiles lane++dataLoopEvents a b tiles lane tiles)[index]? = some event at he
      by_cases hinitial : index < (dataInitialEvents a b tiles lane).length
      · rw [List.getElem?_append_left hinitial] at he
        exact (signature_absent_of_empty_schedule (data_initial_schedule a b tiles lane) he hs).elim
      · rw [List.getElem?_append_right (by omega)] at he
        have hc := data_loop_native_source a b tiles lane tiles (Nat.le_refl _)
          (index-(dataInitialEvents a b tiles lane).length) event signature he hs
        have hindex : (dataInitialEvents a b tiles lane).length+(index-(dataInitialEvents a b tiles lane).length) = index := by omega
        simpa only [hindex] using hc
  · rw [dataCompleteEvents,List.getElem?_append_right (by omega)] at he
    exact (signature_absent_of_empty_schedule (data_output_schedule _ _ _ _ _) he hs).elim

theorem data_native_signature_shape {a b tiles id signature}
    (he : (dataCompleteCandidate a b tiles).nativeSignatureAt id = some signature) :
    ∃ tile lane index, tile < tiles ∧ id = dataNativeId a b tiles tile lane index ∧ signature = dataNativeSignature tile index := by
  obtain ⟨event,raw,hh,hs,ha⟩ := Unified.native_signature_actual he
  obtain ⟨trace,ht,hid,hget⟩ := Unified.eventAt_trace hh
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
  have haligned : dataAlignedSignature event = some signature := by rw [dataAlignedSignature,hs,Option.map_some,ha]
  have hc := data_complete_native_source a b tiles lane id.serial event signature hget haligned
  have hsame : (⟨(ctx tiles lane).id,id.serial⟩ : Ptx.Event.EventId) = id := by
    cases id with | mk thread serial => cases hid; rfl
  rw [hsame] at hc
  cases hc with
  | tile tile actual index ht => exact ⟨tile,actual,index,ht,rfl,rfl⟩

theorem data_native_signature_identity (left right : Nat) (li ri : Fin 4)
    (he : dataNativeSignature left li = dataNativeSignature right ri) : left = right ∧ li = ri := by
  have hs := congrArg (fun signature : Wgmma.SourceSignature => signature.mark.sequence) he
  rw [data_native_signature_sequence,data_native_signature_sequence] at hs
  have hl := li.isLt
  have hr := ri.isLt
  have ht : left = right := by omega
  refine ⟨ht,Fin.ext ?_⟩
  omega

theorem data_native_schedule_length (tiles) : (dataNativeSchedule tiles).length = 4*tiles := by
  induction tiles with
  | zero => rfl
  | succ n ih => simp only [dataNativeSchedule,List.length_append,ih,dataTileSchedule,List.length_cons,List.length_nil]; omega

end
end Ptx.Kernels.HopperDoubleBuffer
