import Ptx.Kernels.HopperStageSchedules
import Ptx.Kernels.HopperStageControlData
import Ptx.Hopper.UnifiedControl

/-! Actual rich native event IDs, including fence. Resource erasure inserts
fence placeholders for ordinary events, so it cannot supply this inventory.
Only the native signature metadata is projected; payloads are not compared.
-/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def nativeId (lane : Wgmma.Lane) (index : Fin 4) : Ptx.Event.EventId :=
  ⟨(ctx lane).id,middleLength (leader lane)-1+index.val⟩
def nativeSignature (index : Fin 4) : Wgmma.SourceSignature :=
  Wgmma.alignedSignature (stageSchedule[index.val]'(by change index.val < 4; exact index.isLt))
def indexedNativeSignature (entry : Wgmma.Event × Nat) : Option (Nat × Wgmma.SourceSignature) :=
  (Wgmma.eventSignature entry.1).map (fun signature => (entry.2,Wgmma.alignedSignature signature))
theorem trace_indexed_native_signatures (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    ((trace a b lane).events.zipIdx).filterMap indexedNativeSignature =
      List.ofFn (fun index : Fin 4 => ((nativeId lane index).serial,nativeSignature index)) := by
  have hg : Ampere.linearThread (ctx lane)/128 = 0 := by rw [ctx_linear]; exact Nat.div_eq_of_lt lane.isLt
  change ((middleEvents a b lane (leader lane)++(nativeEvents a b lane (leader lane)++
    (storeResult a b lane (leader lane)).2)).zipIdx).filterMap indexedNativeSignature = _
  rw [actual_store_events]
  cases hh : leader lane <;> simp [hh,middleEvents,nativeEvents,storedEvents,indexedNativeSignature,List.zipIdx,
    Wgmma.eventSignature,Wgmma.collective,Wgmma.alignedSignature,fenceMark,hg,stageCall,Wgmma.makeCall,nativeId,middleLength,nativeSignature,stageSchedule]
  all_goals rfl
theorem actual_native_signature (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (index : Fin 4) :
    (candidate a b).nativeSignatureAt (nativeId lane index) = some (nativeSignature index) := by
  have hg : Ampere.linearThread (ctx lane)/128 = 0 := by rw [ctx_linear]; exact Nat.div_eq_of_lt lane.isLt
  change ((candidate a b).eventAt ⟨(trace a b lane).id,(nativeId lane index).serial⟩).bind _ = _
  rw [Unified.eventAt_of_member (trace_ids_unique a b) (List.mem_ofFn.mpr ⟨lane,rfl⟩)]
  change ((middleEvents a b lane (leader lane)++(nativeEvents a b lane (leader lane)++
    (storeResult a b lane (leader lane)).2))[(nativeId lane index).serial]?).bind _ = _
  rw [actual_store_events]
  fin_cases index <;> cases hh : leader lane <;> simp [hh,nativeId,middleLength,middleEvents,nativeEvents,storedEvents,
    Wgmma.eventSignature,Wgmma.collective,Wgmma.alignedSignature,fenceMark,hg,stageCall,Wgmma.makeCall,nativeSignature,stageSchedule]
  all_goals norm_num [at29,Ampere.Registers4.names,wrap]
theorem native_signature_shape {a b id signature}
    (he : (candidate a b).nativeSignatureAt id = some signature) :
    ∃ lane index, id = nativeId lane index ∧ signature = nativeSignature index := by
  obtain ⟨event,raw,hh,hs,ha⟩ := Unified.native_signature_actual he
  obtain ⟨actual,ht,hid,hget⟩ := Unified.eventAt_trace hh
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
  have hm := List.mem_filterMap.mpr ⟨(event,id.serial),List.mk_mem_zipIdx_iff_getElem?.mpr hget,
    show indexedNativeSignature (event,id.serial) = some (id.serial,signature) by simp only [indexedNativeSignature,hs,Option.map_some,ha]⟩
  rw [trace_indexed_native_signatures] at hm
  obtain ⟨index,hi⟩ := List.mem_ofFn.mp hm
  have heq := Prod.mk.inj hi
  refine ⟨lane,index,?_,heq.2.symm⟩
  rcases id with ⟨thread,serial⟩
  exact congrArg₂ Ptx.Event.EventId.mk hid.symm heq.1.symm
theorem native_signature_sequence (index : Fin 4) : (nativeSignature index).mark.sequence = index.val := by
  fin_cases index <;> rfl
theorem native_id_rank (lane : Wgmma.Lane) (index : Fin 4) : sourceControlRank (nativeId lane index) = 300+10*index.val := by
  have hb := index.isLt
  dsimp only [nativeId,sourceControlRank]
  change (if Ampere.linearThread (ctx lane) = 0 then _ else _) = _
  rw [ctx_linear]
  by_cases hl : lane.val = 0
  all_goals simp [leader,hl,middleLength]
  all_goals split_ifs <;> omega
theorem rich_native_source_rank {a b id signature}
    (he : (candidate a b).nativeSignatureAt id = some signature) :
    sourceControlRank id = 300+10*signature.mark.sequence := by
  obtain ⟨lane,index,rfl,rfl⟩ := native_signature_shape he
  rw [native_id_rank,native_signature_sequence]

end
end Ptx.Kernels.HopperStage
