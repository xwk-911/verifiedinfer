import Ptx.Kernels.HopperDoubleBufferNativeCompletion

/-! Reuse edges from an actual completed native operand read to every later
TMA write of its physical byte. Cross-lane order passes through the actual
generation-indexed CTA rendezvous. These components do not construct RF/co,
establish native control admission or admit a complete memory witness. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem data_candidate_iteration_event (a b tiles tile lane) (ht : tile < tiles) (index : Nat) (event : Wgmma.Event)
    (he : (dataIterationEvents a b tiles tile lane)[index]? = some event) :
    (dataCompleteCandidate a b tiles).eventAt ⟨(ctx tiles lane).id,dataTileStart a b tiles tile lane+index⟩ = some event := by
  change (dataCompleteCandidate a b tiles).eventAt ⟨(dataCompleteTrace a b tiles lane).id,_⟩ = _
  rw [Unified.eventAt_of_member (data_source_ids_unique a b tiles) (List.mem_ofFn.mpr ⟨lane,rfl⟩)]
  exact data_complete_iteration_at a b tiles tile lane ht index event he

def dataReuseCtaEvent (tile : Nat) (arrival : Bool) : Wgmma.Event :=
  .base (.ampere (.ordinary (if arrival then .barrierArrival 2 tile else .barrierReturn 2 tile)))

theorem data_iteration_reuse_cta_at (a b tiles tile lane) (arrival : Bool) :
    (dataIterationEvents a b tiles tile lane)[dataPreludeLength tiles tile lane+5+ctaOffset arrival]? =
      some (dataReuseCtaEvent tile arrival) := by
  simp only [dataIterationEvents,iterationEvents,List.replicate_zero,List.nil_append,List.append_assoc]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_cons,List.length_nil]
  rw [List.getElem?_append_right (by rw [data_prelude_length]; omega),data_prelude_length]
  have he : dataPreludeLength tiles tile lane+5+ctaOffset arrival-1-dataPreludeLength tiles tile lane = 4+ctaOffset arrival := by omega
  rw [he,List.getElem?_append_right (by change 4 ≤ 4+ctaOffset arrival; omega)]
  change (advanceEvents _)[4+ctaOffset arrival-4]? = _
  rw [Nat.add_sub_cancel_left]
  cases arrival <;> simp only [ctaOffset,Bool.false_eq_true,ite_false,ite_true,
    advanceEvents,List.getElem?_cons_zero,List.getElem?_cons_succ,data_prepared_generation_two,dataReuseCtaEvent]

theorem data_source_reuse_cta (a b tiles tile lane) (ht : tile < tiles) (arrival : Bool) :
    (dataCompleteCandidate a b tiles).eventAt (reuseCtaId a b tiles tile lane arrival) =
      some (dataReuseCtaEvent tile arrival) := by
  have he := data_candidate_iteration_event a b tiles tile lane ht _ _ (data_iteration_reuse_cta_at a b tiles tile lane arrival)
  simpa only [reuseCtaId,Nat.add_assoc] using he

theorem data_reuse_cta_present (a b tiles tile lane) (ht : tile < tiles) (arrival : Bool) :
    (dataCompleteCandidate a b tiles).view.Present (reuseCtaId a b tiles tile lane arrival) := by
  apply (Unified.view_present_iff _ _).mpr
  simp only [Unified.Candidate.Present,data_source_reuse_cta a b tiles tile lane ht arrival,Option.isSome_some]

theorem data_reuse_cta_tag (a b tiles tile lane) (ht : tile < tiles) (arrival : Bool) :
    (dataCompleteCandidate a b tiles).view.ctaTag arrival (reuseCtaId a b tiles tile lane arrival) = some (2,tile) := by
  rw [Hopper.Candidate.ctaTag,Unified.view_eventAt,data_source_reuse_cta a b tiles tile lane ht arrival]
  cases arrival <;> rfl

theorem data_native_wait_before_reuse_cta (a b tiles tile lane) (ht : tile < tiles) (hb : tiles ≤ 2^28) :
    Access.GenericAfter (dataCompleteCandidate a b tiles).view (dataNativeWaitId a b tiles tile lane)
      (reuseCtaId a b tiles tile lane true) := by
  apply Access.generic_program_after
  refine ⟨?_,data_reuse_cta_present a b tiles tile lane ht true,rfl,?_⟩
  · apply (Unified.view_present_iff _ _).mpr
    simp only [Unified.Candidate.Present,data_source_native_wait a b tiles tile lane ht hb,Option.isSome_some]
  · dsimp only [dataNativeWaitId,reuseCtaId,ctaOffset,ite_true]
    omega

theorem data_reuse_cta_cross_lane (a b tiles tile left right) (ht : tile < tiles) :
    Access.GenericAfter (dataCompleteCandidate a b tiles).view (reuseCtaId a b tiles tile left true)
      (reuseCtaId a b tiles tile right false) := by
  apply Access.generic_cta_after
  simp only [Hopper.CTAControl,data_reuse_cta_tag a b tiles tile left ht true,
    data_reuse_cta_tag a b tiles tile right ht false]
  exact ⟨rfl,True.intro⟩

theorem data_reuse_return_serial (a b tiles tile) (ht : tile+1 < tiles) :
    (reuseCtaId a b tiles tile 0 false).serial = 17+10*tile := by
  dsimp only [reuseCtaId]
  rw [data_tile_start_value a b tiles tile 0 (by omega)]
  have hp : needsPrefetch tile tiles (HopperStage.leader 0) := ⟨ht,rfl⟩
  rw [dataPreludeLength,ite_eq_left hp]
  simp only [show HopperStage.leader 0 = true from rfl,ite_true,ctaOffset,Bool.false_eq_true,ite_false]
  omega

theorem data_reuse_return_before_copy_a (a b tiles tile next) (hn : next < tiles) (hle : tile+2 ≤ next) (hb : tiles ≤ 2^28) :
    Access.GenericAfter (dataCompleteCandidate a b tiles).view (reuseCtaId a b tiles tile 0 false) (dataCopyAId a b tiles next).issue := by
  apply Access.generic_program_after
  refine ⟨data_reuse_cta_present a b tiles tile 0 (by omega) false,?_,rfl,?_⟩
  · simp only [Hopper.Candidate.Present,Tma.copyAt_iff.mp (data_source_copy_a a b tiles next hn hb),Option.isSome_some]
  · rw [data_reuse_return_serial a b tiles tile (by omega),data_copy_a_serial a b tiles next hn]
    simp only [copyASerial,show next ≠ 0 by omega,ite_false]
    omega

theorem data_reuse_return_before_copy_b (a b tiles tile next) (hn : next < tiles) (hle : tile+2 ≤ next) (hb : tiles ≤ 2^28) :
    Access.GenericAfter (dataCompleteCandidate a b tiles).view (reuseCtaId a b tiles tile 0 false) (dataCopyBId a b tiles next).issue := by
  apply Access.generic_program_after
  refine ⟨data_reuse_cta_present a b tiles tile 0 (by omega) false,?_,rfl,?_⟩
  · simp only [Hopper.Candidate.Present,Tma.copyAt_iff.mp (data_source_copy_b a b tiles next hn hb),Option.isSome_some]
  · rw [data_reuse_return_serial a b tiles tile (by omega),data_copy_b_serial a b tiles next hn]
    simp only [copyBSerial,show next ≠ 0 by omega,ite_false]
    omega

theorem data_native_wait_before_copy_a (a b tiles tile next lane) (hn : next < tiles) (hle : tile+2 ≤ next) (hb : tiles ≤ 2^28) :
    Access.GenericAfter (dataCompleteCandidate a b tiles).view (dataNativeWaitId a b tiles tile lane) (dataCopyAId a b tiles next).issue :=
  .trans (data_native_wait_before_reuse_cta a b tiles tile lane (by omega) hb)
    (.trans (data_reuse_cta_cross_lane a b tiles tile lane 0 (by omega))
      (data_reuse_return_before_copy_a a b tiles tile next hn hle hb))

theorem data_native_wait_before_copy_b (a b tiles tile next lane) (hn : next < tiles) (hle : tile+2 ≤ next) (hb : tiles ≤ 2^28) :
    Access.GenericAfter (dataCompleteCandidate a b tiles).view (dataNativeWaitId a b tiles tile lane) (dataCopyBId a b tiles next).issue :=
  .trans (data_native_wait_before_reuse_cta a b tiles tile lane (by omega) hb)
    (.trans (data_reuse_cta_cross_lane a b tiles tile lane 0 (by omega))
      (data_reuse_return_before_copy_b a b tiles tile next hn hle hb))

theorem data_a_native_reuse (a b tiles tile next) (hn : next < tiles) (hle : tile+2 ≤ next)
    (hs : stage next = stage tile) (hb : tiles ≤ 2^28) (p : Wgmma.ACoord) (byte : Fin 2) :
    Unified.NativeReuse Tma.localShared (dataCompleteCandidate a b tiles) (dataNativeLocation a b tiles tile (.a p byte))
      (dataNativeRead a b tiles tile (.a p byte)) (dataNativeProducer a b tiles next (.a p byte)) := by
  refine ⟨dataNativeWaitId a b tiles tile 0,data_native_completed a b tiles tile 0 (by omega) hb,
    data_native_wait_before_copy_a a b tiles tile next 0 hn hle hb,?_,
    ⟨77,4*tile+1,0⟩,dataIterationCall a b tiles tile 0,data_collective_representative a b tiles tile (by omega),rfl⟩
  rw [data_transfer_a_location a b tiles next hn hb]
  simp only [dataNativeLocation,Wgmma.operandLocation,data_call_a,a_operand_address,hs]

theorem data_b_native_reuse (a b tiles tile next) (hn : next < tiles) (hle : tile+2 ≤ next)
    (hs : stage next = stage tile) (hb : tiles ≤ 2^28) (p : Wgmma.BCoord) (byte : Fin 2) :
    Unified.NativeReuse Tma.localShared (dataCompleteCandidate a b tiles) (dataNativeLocation a b tiles tile (.b p byte))
      (dataNativeRead a b tiles tile (.b p byte)) (dataNativeProducer a b tiles next (.b p byte)) := by
  refine ⟨dataNativeWaitId a b tiles tile 0,data_native_completed a b tiles tile 0 (by omega) hb,
    data_native_wait_before_copy_b a b tiles tile next 0 hn hle hb,?_,
    ⟨77,4*tile+1,0⟩,dataIterationCall a b tiles tile 0,data_collective_representative a b tiles tile (by omega),rfl⟩
  rw [data_transfer_b_location a b tiles next hn hb]
  simp only [dataNativeLocation,Wgmma.operandLocation,data_call_b,b_operand_address,hs]

theorem data_native_reuse (a b tiles tile next) (hn : next < tiles) (hle : tile+2 ≤ next)
    (hs : stage next = stage tile) (hb : tiles ≤ 2^28) (operand : Wgmma.OperandByte) :
    Unified.NativeReuse Tma.localShared (dataCompleteCandidate a b tiles) (dataNativeLocation a b tiles tile operand)
      (dataNativeRead a b tiles tile operand) (dataNativeProducer a b tiles next operand) := by
  cases operand with
  | a p byte => exact data_a_native_reuse a b tiles tile next hn hle hs hb p byte
  | b p byte => exact data_b_native_reuse a b tiles tile next hn hle hs hb p byte

theorem data_native_reuse_byte_order (a b tiles tile next) (hn : next < tiles) (hle : tile+2 ≤ next)
    (hs : stage next = stage tile) (hb : tiles ≤ 2^28) (operand : Wgmma.OperandByte) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster (dataNativeLocation a b tiles tile operand)
      (dataNativeRead a b tiles tile operand) (dataNativeProducer a b tiles next operand) :=
  Unified.native_reuse_byte_order (data_native_reuse a b tiles tile next hn hle hs hb operand)

theorem data_cta_is_not_native_completion (a b tiles tile lane) (ht : tile < tiles) (arrival : Bool)
    (issue : Ptx.Event.EventId) :
    ¬Unified.WgmmaCompletedAt (dataCompleteCandidate a b tiles) issue (reuseCtaId a b tiles tile lane arrival) := by
  intro hc
  obtain ⟨mark,groups,keep,before,after,query,he,_⟩ := Unified.completed_has_actual_wait hc
  rw [data_source_reuse_cta a b tiles tile lane ht arrival] at he
  cases he

theorem data_mbarrier_is_not_native_completion (a b tiles tile lane) (ht : tile < tiles)
    (issue : Ptx.Event.EventId) :
    ¬Unified.WgmmaCompletedAt (dataCompleteCandidate a b tiles) issue (dataWaitId a b tiles tile lane) := by
  intro hc
  obtain ⟨mark,groups,keep,before,after,query,he,_⟩ := Unified.completed_has_actual_wait hc
  rw [show (dataCompleteCandidate a b tiles).eventAt (dataWaitId a b tiles tile lane) = _ from
    data_candidate_wait_at a b tiles tile lane ht] at he
  cases he

end
end Ptx.Kernels.HopperDoubleBuffer
