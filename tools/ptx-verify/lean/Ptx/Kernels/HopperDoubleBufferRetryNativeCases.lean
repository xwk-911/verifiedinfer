import Ptx.Kernels.HopperDoubleBufferRetryNativeSchedules
import Ptx.Kernels.HopperDoubleBufferNativeInventory

/-! Source identities of all native events with arbitrary finite retries.
Both directions retain actual event-prefix indices. Captured arithmetic values
are not constrained by native signatures; combined control remains separate. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def ReplySourceFamily.nativeId {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (tile : Nat) (lane : Wgmma.Lane) (index : Fin 4) : Ptx.Event.EventId :=
  ⟨(ctx tiles lane).id,replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+
    (family.schedules lane tile+preludeEventCount tile tiles (HopperStage.leader lane)+1+index.val)⟩
inductive RetryNativeSource {tiles candidate} (family : ReplySourceFamily tiles candidate) : Ptx.Event.EventId → Wgmma.SourceSignature → Prop
  | tile (tile : Nat) (lane : Wgmma.Lane) (index : Fin 4) (ht : tile < tiles) :
      RetryNativeSource family (family.nativeId tile lane index) (dataNativeSignature tile index)

theorem reply_compute_aligned_signature (tiles lane reply retries tile) (index : Fin 4) :
    ((computeEvents (ctx tiles lane) reply
      (preparedState (replyTileCheckpoint tiles lane reply retries tile).1 tile tiles (retries tile) (HopperStage.leader lane))
      (aDescriptor (stage tile)) (bDescriptor (stage tile)) (replyTileCheckpoint tiles lane reply retries tile).2)[index.val]?).bind dataAlignedSignature =
        some (dataNativeSignature tile index) := by
  have hm := reply_mark_value tiles lane reply retries tile
  change Wgmma.mark (ctx tiles lane) (computeFence _) = _ at hm
  fin_cases index <;> simp only [computeEvents,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.bind_some,dataAlignedSignature,Wgmma.eventSignature,Wgmma.collective,Option.map_some]
  all_goals first
    | (rw [reply_prepared_mark]; rfl)
    | (rw [reply_issued_mark,preparedState_groups,reply_checkpoint_groups]; rfl)
    | (rw [reply_committed_mark,preparedState_groups,reply_checkpoint_groups]; rfl)
    | (rw [hm]; change some (Wgmma.alignedSignature ⟨_,_,.mma (replyCall tiles lane reply retries tile).ordinal
        (replyCall tiles lane reply retries tile).group (replyCall tiles lane reply retries tile).d.names
        (replyCall tiles lane reply retries tile).a (replyCall tiles lane reply retries tile).b
        (replyCall tiles lane reply retries tile).scaleD⟩) = _
       rw [reply_call_ordinal,reply_call_group,reply_call_a,reply_call_b]; rfl)

theorem reply_iteration_signature_case (tiles lane reply retries tile) (index : Nat) (event : Wgmma.Event) (signature : Wgmma.SourceSignature)
    (he : (replyIterationEvents tiles lane reply retries tile)[index]? = some event) (hs : dataAlignedSignature event = some signature) :
    ∃ i : Fin 4, index = retries tile+preludeEventCount tile tiles (HopperStage.leader lane)+1+i.val ∧
      signature = dataNativeSignature tile i := by
  dsimp only [replyIterationEvents,iterationEvents] at he
  rw [List.append_assoc] at he
  by_cases hh : index < retries tile+1
  · rw [List.getElem?_append_left (by simpa only [List.length_append,List.length_replicate,List.length_cons,List.length_nil] using hh)] at he
    exact (signature_absent_of_empty_schedule (by
      rw [Wgmma.event_schedule_append,wait_replicate_native_schedule]
      rfl) he hs).elim
  · rw [List.getElem?_append_right (by simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil]; omega)] at he
    simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil] at he
    by_cases hp : index-(retries tile+1) < preludeEventCount tile tiles (HopperStage.leader lane)
    · rw [List.getElem?_append_left (by rwa [prelude_events_length])] at he
      exact (signature_absent_of_empty_schedule (data_prelude_schedule _ _ _ _ _ _ _ _) he hs).elim
    · rw [List.getElem?_append_right (by rw [prelude_events_length]; omega),prelude_events_length] at he
      by_cases hc : index-(retries tile+1)-preludeEventCount tile tiles (HopperStage.leader lane) < 4
      · rw [List.getElem?_append_left (by change index-(retries tile+1)-preludeEventCount tile tiles (HopperStage.leader lane) < 4; exact hc)] at he
        let i : Fin 4 := ⟨index-(retries tile+1)-preludeEventCount tile tiles (HopperStage.leader lane),hc⟩
        refine ⟨i,by dsimp [i]; omega,?_⟩
        have hm := reply_compute_aligned_signature tiles lane reply retries tile i
        change (_[index-(retries tile+1)-preludeEventCount tile tiles (HopperStage.leader lane)]?).bind dataAlignedSignature = _ at hm
        rw [he,Option.bind_some,hs] at hm
        exact Option.some.inj hm
      · rw [List.getElem?_append_right (by change 4 ≤ index-(retries tile+1)-preludeEventCount tile tiles (HopperStage.leader lane); omega)] at he
        exact (signature_absent_of_empty_schedule (by rfl) he hs).elim

theorem reply_iteration_native_signature (tiles lane reply retries tile) (index : Fin 4) :
    ((replyIterationEvents tiles lane reply retries tile)[retries tile+preludeEventCount tile tiles (HopperStage.leader lane)+1+index.val]?).bind
      dataAlignedSignature = some (dataNativeSignature tile index) := by
  dsimp only [replyIterationEvents,iterationEvents]
  rw [List.append_assoc,List.getElem?_append_right (by
    simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil]; omega)]
  simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil]
  rw [List.getElem?_append_right (by rw [prelude_events_length]; omega),prelude_events_length]
  rw [show retries tile+preludeEventCount tile tiles (HopperStage.leader lane)+1+index.val-(retries tile+1)-
    preludeEventCount tile tiles (HopperStage.leader lane) = index.val by omega]
  rw [List.getElem?_append_left (by change index.val < 4; exact index.isLt)]
  exact reply_compute_aligned_signature tiles lane reply retries tile index

theorem retry_loop_native_source {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) (n : Nat) (hn : n ≤ tiles)
    (index : Nat) (event : Wgmma.Event) (signature : Wgmma.SourceSignature)
    (he : (replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) n)[index]? = some event)
    (hs : dataAlignedSignature event = some signature) :
    RetryNativeSource family ⟨(ctx tiles lane).id,(replyInitialEvents lane (family.replies lane)).length+index⟩ signature := by
  induction n generalizing index with
  | zero => simp [replyLoopEvents,loopEvents] at he
  | succ n ih =>
    have hstep : replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) (n+1) =
        replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) n++
          replyIterationEvents tiles lane (family.replies lane) (family.schedules lane) n := by
      simp only [replyLoopEvents,loopEvents,replyIterationEvents,replyTileCheckpoint,Nat.zero_add]
    by_cases hi : index < (replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) n).length
    · rw [hstep,List.getElem?_append_left hi] at he
      exact ih (by omega) index he
    · rw [hstep,List.getElem?_append_right (by omega)] at he
      obtain ⟨i,hindex,rfl⟩ := reply_iteration_signature_case tiles lane (family.replies lane) (family.schedules lane) n _ event signature he hs
      have hserial : (replyInitialEvents lane (family.replies lane)).length+index =
          replyTileStart tiles lane (family.replies lane) (family.schedules lane) n+
            (family.schedules lane n+preludeEventCount n tiles (HopperStage.leader lane)+1+i.val) := by
        unfold replyTileStart
        omega
      rw [hserial]
      exact RetryNativeSource.tile n lane i (by omega)

theorem retry_complete_native_source {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane)
    (index : Nat) (event : Wgmma.Event) (signature : Wgmma.SourceSignature)
    (he : (replyPositiveEvents tiles lane (family.replies lane) (family.schedules lane))[index]? = some event)
    (hs : dataAlignedSignature event = some signature) : RetryNativeSource family ⟨(ctx tiles lane).id,index⟩ signature := by
  simp only [replyPositiveEvents,← List.append_assoc] at he
  change ((replyInitialEvents lane (family.replies lane)++replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) tiles)++_)[index]? = some event at he
  by_cases hi : index < replyTileStart tiles lane (family.replies lane) (family.schedules lane) tiles
  · rw [List.getElem?_append_left (by simpa only [List.length_append,replyTileStart] using hi)] at he
    by_cases hinitial : index < (replyInitialEvents lane (family.replies lane)).length
    · rw [List.getElem?_append_left hinitial] at he
      exact (signature_absent_of_empty_schedule (reply_initial_native_schedule _ _) he hs).elim
    · rw [List.getElem?_append_right (by omega)] at he
      have hc := retry_loop_native_source family lane tiles (Nat.le_refl _) _ event signature he hs
      simpa only [show (replyInitialEvents lane (family.replies lane)).length+
        (index-(replyInitialEvents lane (family.replies lane)).length) = index by omega] using hc
  · rw [List.getElem?_append_right (by simpa only [List.length_append,replyTileStart] using Nat.le_of_not_gt hi)] at he
    exact (signature_absent_of_empty_schedule (data_output_schedule _ _ _ _ _) he hs).elim

theorem retry_native_signature_shape {tiles initial candidate id signature} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (he : candidate.nativeSignatureAt id = some signature) :
    ∃ tile lane index, tile < tiles ∧ id = family.nativeId tile lane index ∧ signature = dataNativeSignature tile index := by
  obtain ⟨event,raw,hh,hs,ha⟩ := Unified.native_signature_actual he
  obtain ⟨trace,ht,hid,hget⟩ := Unified.eventAt_trace hh
  obtain ⟨lane,rfl⟩ := retry_trace_family family hw ht
  rw [family.events] at hget
  have haligned : dataAlignedSignature event = some signature := by rw [dataAlignedSignature,hs,Option.map_some,ha]
  have hc := retry_complete_native_source family lane id.serial event signature hget haligned
  have hthread : (ctx tiles lane).id = id.thread := (family.ids lane).symm.trans hid
  have hsame : (⟨(ctx tiles lane).id,id.serial⟩ : Ptx.Event.EventId) = id := by cases id; exact congrArg₂ Ptx.Event.EventId.mk hthread rfl
  rw [hsame] at hc
  cases hc with
  | tile tile actual index ht => exact ⟨tile,actual,index,ht,rfl,rfl⟩

theorem retry_actual_native_signature {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane) (index : Fin 4) :
    candidate.nativeSignatureAt (family.nativeId tile lane index) = some (dataNativeSignature tile index) := by
  obtain ⟨event,he,hs⟩ := Option.bind_eq_some_iff.mp (reply_iteration_native_signature tiles lane (family.replies lane) (family.schedules lane) tile index)
  have hc := family_event_at family hw lane _ _ (reply_complete_iteration_at tiles lane (family.replies lane) (family.schedules lane) tile _ event ht he)
  change (candidate.eventAt (family.nativeId tile lane index)).bind dataAlignedSignature = _
  rw [show candidate.eventAt (family.nativeId tile lane index) = some event from hc,Option.bind_some]
  exact hs

theorem retry_native_mma_id {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane) :
    family.nativeId tile lane 1 = family.mmaId tile lane := by
  apply congrArg₂ Ptx.Event.EventId.mk rfl
  dsimp [ReplySourceFamily.nativeId,ReplySourceFamily.mmaId,replyMmaId]
  omega

theorem retry_native_wait_id {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane) :
    family.nativeId tile lane 3 = family.nativeWaitId tile lane := by
  apply congrArg₂ Ptx.Event.EventId.mk rfl
  dsimp [ReplySourceFamily.nativeId,ReplySourceFamily.nativeWaitId,replyNativeWaitId]
  omega

theorem retry_native_mma_case {tiles initial candidate id mark call} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (he : candidate.eventAt id = some (.mma mark call)) :
    ∃ tile lane, tile < tiles ∧ id = family.nativeId tile lane 1 ∧ mark = family.marks tile lane ∧ call = family.calls tile lane := by
  have hs : candidate.nativeSignatureAt id =
      some (Wgmma.alignedSignature ⟨mark.pc,mark,.mma call.ordinal call.group call.d.names call.a call.b call.scaleD⟩) := by
    rw [Unified.Candidate.nativeSignatureAt,he]
    rfl
  obtain ⟨tile,lane,index,ht,hid,hshape⟩ := retry_native_signature_shape family hw hs
  have hk := congrArg Wgmma.SourceSignature.kind hshape
  fin_cases index <;> simp [dataNativeSignature,dataTileSchedule,Wgmma.alignedSignature] at hk
  have hmmaid := hid.trans (retry_native_mma_id family tile lane)
  have hactual := family_mma_at family hw tile ht lane
  rw [← hmmaid] at hactual
  have hh := Wgmma.Event.mma.inj (Option.some.inj (he.symm.trans hactual))
  exact ⟨tile,lane,ht,hid,hh⟩

theorem retry_native_wait_case {tiles initial candidate id mark groups keep before after query} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hb : tiles ≤ 2^28)
    (he : candidate.eventAt id = some (.wait mark groups keep before after query)) :
    ∃ tile lane, tile < tiles ∧ id = family.nativeId tile lane 3 ∧ after = tile+1 := by
  have hs : candidate.nativeSignatureAt id = some (Wgmma.alignedSignature ⟨mark.pc,mark,.wait groups keep⟩) := by
    rw [Unified.Candidate.nativeSignatureAt,he]
    rfl
  obtain ⟨tile,lane,index,ht,hid,hshape⟩ := retry_native_signature_shape family hw hs
  have hk := congrArg Wgmma.SourceSignature.kind hshape
  fin_cases index <;> simp [dataNativeSignature,dataTileSchedule,Wgmma.alignedSignature] at hk
  have hwaitid := hid.trans (retry_native_wait_id family tile lane)
  have hactual := family_native_wait_at family hw hb tile ht lane
  rw [← hwaitid] at hactual
  have hh := Wgmma.Event.wait.inj (Option.some.inj (he.symm.trans hactual))
  exact ⟨tile,lane,ht,hid,hh.2.2.2.2.1⟩

theorem retry_native_sync_identity {tiles initial candidate left right} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hs : Unified.NativeSync HopperStage.block candidate left right) :
    ∃ tile ll rl index, tile < tiles ∧ left = family.nativeId tile ll index ∧ right = family.nativeId tile rl index := by
  obtain ⟨_,signature,hl,hr⟩ := hs
  obtain ⟨lt,ll,li,hlt,rfl,hls⟩ := retry_native_signature_shape family hw hl
  obtain ⟨rt,rl,ri,hrt,rfl,hrs⟩ := retry_native_signature_shape family hw hr
  obtain ⟨rfl,rfl⟩ := data_native_signature_identity lt rt li ri (hls.symm.trans hrs)
  exact ⟨lt,ll,rl,li,hlt,rfl,rfl⟩

end
end Ptx.Kernels.HopperDoubleBuffer
