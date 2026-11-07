import Ptx.Kernels.HopperDoubleBufferNativeSchedules

/-! Local native signature identities and exhaustive cases. Metadata is
projected from actual rich events; ordinary-event erasure placeholders cannot
supply native signatures. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def dataNativeId (a : TileA) (b : TileB) (tiles tile : Nat) (lane : Wgmma.Lane) (index : Fin 4) : Ptx.Event.EventId :=
  ⟨(ctx tiles lane).id,dataTileStart a b tiles tile lane+(dataPreludeLength tiles tile lane+1+index.val)⟩
def dataNativeSignature (tile : Nat) (index : Fin 4) : Wgmma.SourceSignature :=
  Wgmma.alignedSignature ((dataTileSchedule tile)[index.val]'(by change index.val < 4; exact index.isLt))
def dataAlignedSignature (event : Wgmma.Event) : Option Wgmma.SourceSignature :=
  (Wgmma.eventSignature event).map Wgmma.alignedSignature

theorem signature_absent_of_empty_schedule {events : List Wgmma.Event} (hn : Wgmma.eventSchedule events = [])
    {index : Nat} {event : Wgmma.Event} {signature : Wgmma.SourceSignature}
    (he : events[index]? = some event) (hs : dataAlignedSignature event = some signature) : False := by
  obtain ⟨raw,hr,_⟩ := Option.map_eq_some_iff.mp hs
  have hm : raw ∈ Wgmma.eventSchedule events := List.mem_filterMap.mpr ⟨event,List.mem_of_getElem? he,hr⟩
  rw [hn] at hm
  exact List.not_mem_nil hm

theorem data_compute_aligned_signature (a b tiles tile lane) (index : Fin 4) :
    ((computeEvents (ctx tiles lane) (dataOracle a b tiles lane)
      (preparedState (dataCheckpoint a b tiles lane tile).1 tile tiles 0 (HopperStage.leader lane))
      (aDescriptor (stage tile)) (bDescriptor (stage tile)) (dataCheckpoint a b tiles lane tile).2)[index.val]?).bind dataAlignedSignature =
        some (dataNativeSignature tile index) := by
  have hm := data_mark_value a b tiles tile lane
  change Wgmma.mark (ctx tiles lane) (computeFence _) = _ at hm
  fin_cases index <;> simp only [computeEvents,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.bind_some,dataAlignedSignature,Wgmma.eventSignature,Wgmma.collective,Option.map_some]
  all_goals first
    | (rw [data_prepared_mark]; rfl)
    | (rw [data_issued_mark,preparedState_groups,data_checkpoint_groups]; rfl)
    | (rw [data_committed_mark,preparedState_groups,data_checkpoint_groups]; rfl)
    | (rw [hm]; change some (Wgmma.alignedSignature ⟨_,_,.mma (dataIterationCall a b tiles tile lane).ordinal
        (dataIterationCall a b tiles tile lane).group (dataIterationCall a b tiles tile lane).d.names
        (dataIterationCall a b tiles tile lane).a (dataIterationCall a b tiles tile lane).b
        (dataIterationCall a b tiles tile lane).scaleD⟩) = _
       rw [data_call_ordinal,data_call_group,data_call_a,data_call_b]; rfl)

theorem data_iteration_signature_case (a b tiles tile lane) (index : Nat) (event : Wgmma.Event) (signature : Wgmma.SourceSignature)
    (he : (dataIterationEvents a b tiles tile lane)[index]? = some event) (hs : dataAlignedSignature event = some signature) :
    ∃ i : Fin 4, index = dataPreludeLength tiles tile lane+1+i.val ∧ signature = dataNativeSignature tile i := by
  simp only [dataIterationEvents,iterationEvents,List.replicate_zero,List.nil_append,List.append_assoc] at he
  by_cases hz : index = 0
  · subst index
    rw [List.getElem?_append_left (by simp)] at he
    simp only [List.getElem?_cons_zero] at he
    cases he
    cases hs
  · rw [List.getElem?_append_right (by simp; omega)] at he
    simp only [List.length_cons,List.length_nil] at he
    by_cases hp : index-1 < dataPreludeLength tiles tile lane
    · rw [List.getElem?_append_left (by rwa [data_prelude_length])] at he
      exact (signature_absent_of_empty_schedule (data_prelude_schedule _ _ _ _ _ _ _ _) he hs).elim
    · rw [List.getElem?_append_right (by rw [data_prelude_length]; omega),data_prelude_length] at he
      by_cases hc : index-1-dataPreludeLength tiles tile lane < 4
      · rw [List.getElem?_append_left (by change index-1-dataPreludeLength tiles tile lane < 4; exact hc)] at he
        let i : Fin 4 := ⟨index-1-dataPreludeLength tiles tile lane,hc⟩
        refine ⟨i,by dsimp only [i]; omega,?_⟩
        have hm := data_compute_aligned_signature a b tiles tile lane i
        change (_[index-1-dataPreludeLength tiles tile lane]?).bind dataAlignedSignature = _ at hm
        rw [he,Option.bind_some,hs] at hm
        exact Option.some.inj hm
      · rw [List.getElem?_append_right (by change 4 ≤ index-1-dataPreludeLength tiles tile lane; omega)] at he
        exact (signature_absent_of_empty_schedule (by rfl) he hs).elim

inductive NativeSource (a : TileA) (b : TileB) (tiles : Nat) : Ptx.Event.EventId → Wgmma.SourceSignature → Prop
  | tile (tile : Nat) (lane : Wgmma.Lane) (index : Fin 4) (ht : tile < tiles) :
      NativeSource a b tiles (dataNativeId a b tiles tile lane index) (dataNativeSignature tile index)

theorem data_iteration_native_source (a b tiles tile lane) (ht : tile < tiles)
    (index : Nat) (event : Wgmma.Event) (signature : Wgmma.SourceSignature)
    (he : (dataIterationEvents a b tiles tile lane)[index]? = some event) (hs : dataAlignedSignature event = some signature) :
    NativeSource a b tiles ⟨(ctx tiles lane).id,dataTileStart a b tiles tile lane+index⟩ signature := by
  obtain ⟨i,hi,rfl⟩ := data_iteration_signature_case a b tiles tile lane index event signature he hs
  rw [hi]
  exact NativeSource.tile tile lane i ht

theorem data_iteration_native_signature (a b tiles tile lane) (index : Fin 4) :
    ((dataIterationEvents a b tiles tile lane)[dataPreludeLength tiles tile lane+1+index.val]?).bind dataAlignedSignature =
      some (dataNativeSignature tile index) := by
  simp only [dataIterationEvents,iterationEvents,List.replicate_zero,List.nil_append,List.append_assoc]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_cons,List.length_nil]
  rw [List.getElem?_append_right (by rw [data_prelude_length]; omega),data_prelude_length]
  have hi : dataPreludeLength tiles tile lane+1+index.val-1-dataPreludeLength tiles tile lane = index.val := by omega
  rw [hi,List.getElem?_append_left (by change index.val < 4; exact index.isLt)]
  exact data_compute_aligned_signature a b tiles tile lane index

theorem data_actual_native_signature (a b tiles tile lane) (ht : tile < tiles) (index : Fin 4) :
    (dataCompleteCandidate a b tiles).nativeSignatureAt (dataNativeId a b tiles tile lane index) = some (dataNativeSignature tile index) := by
  obtain ⟨event,he,hs⟩ := Option.bind_eq_some_iff.mp (data_iteration_native_signature a b tiles tile lane index)
  change ((dataCompleteCandidate a b tiles).eventAt ⟨(ctx tiles lane).id,
    dataTileStart a b tiles tile lane+(dataPreludeLength tiles tile lane+1+index.val)⟩).bind dataAlignedSignature = _
  rw [data_candidate_iteration_event a b tiles tile lane ht _ event he,Option.bind_some]
  exact hs

theorem data_native_signature_sequence (tile) (index : Fin 4) :
    (dataNativeSignature tile index).mark.sequence = 4*tile+index.val := by
  fin_cases index <;> rfl

theorem data_native_signature_pc (tile) (index : Fin 4) : (dataNativeSignature tile index).pc = 76+index.val := by
  fin_cases index <;> rfl

end
end Ptx.Kernels.HopperDoubleBuffer
