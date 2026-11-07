import Ptx.Kernels.HopperStageMemoryRank
import Ptx.Hopper.InitialReadAgreement

/-! Explicit read-source values for the actual single-stage source. This file
constructs RF, rather than obtaining it from an assumed memory execution.
Causal/coherence/observer admission remains a separate obligation. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def ordinaryRead (event : Hopper.Event) (loc : Location) : Option Symbolic.Byte :=
  (match event with | .ampere (.ordinary k) => some k | _ => none).bind (fun k => k.readByte loc)
theorem trace_source_reads_absent (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (loc : Location) :
    ∀ event ∈ (trace a b lane).view.events, ordinaryRead event loc = none := by
  change ∀ event ∈ (middleEvents a b lane (leader lane)++(nativeEvents a b lane (leader lane)++
    (storeResult a b lane (leader lane)).2)).map Unified.eventView, ordinaryRead event loc = none
  rw [actual_store_events]
  cases hh : leader lane <;> simp [hh,middleEvents,nativeEvents,storedEvents,Unified.eventView,ordinaryRead,Ptx.Event.Kind.readByte]
theorem ordinary_read_none (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (event : Ptx.Event.EventId) (loc : Location) :
    Access.readByte Tma.localShared Access.globalDescriptor (candidate a b).view (.tma (.source event)) loc = none := by
  cases he : (candidate a b).view.eventAt event with
  | none => simp [Access.readByte,Access.kind,he]
  | some kind =>
    obtain ⟨actual,ht,_,hget⟩ := Hopper.eventAt_trace he
    obtain ⟨rich,hr,rfl⟩ := List.mem_map.mp ht
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp hr
    have hn := trace_source_reads_absent a b lane loc kind (List.mem_of_getElem? hget)
    simp only [Access.readByte,Access.kind,he,Option.bind_some]
    cases kind with
    | ampere event => cases event <;> exact hn
    | tmaIssue _ | proxyFenceAsyncShared _ | barrier _ | wgmma _ => exact hn

theorem actual_mma_call {a b id mark call}
    (he : (candidate a b).eventAt id = some (.mma mark call)) :
    ∃ lane, id.thread = (ctx lane).id ∧ call = calls a b lane := by
  obtain ⟨actual,ht,hid,hget⟩ := Unified.eventAt_trace he
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
  refine ⟨lane,hid.symm,?_⟩
  have hm := List.mem_of_getElem? hget
  change .mma mark call ∈ middleEvents a b lane (leader lane)++
    (nativeEvents a b lane (leader lane)++(storeResult a b lane (leader lane)).2) at hm
  rw [actual_store_events] at hm
  cases hl : leader lane <;> simp [middleEvents,nativeEvents,storedEvents,hl] at hm
  all_goals simpa only [calls,hl] using hm.2
theorem actual_representative_call {a b id mark call}
    (he : (candidate a b).representativeAt id = some (mark,call)) :
    id.thread.cta = .zero ∧ call = calls a b 0 := by
  obtain ⟨hm,hzero⟩ := Unified.representative_at he
  obtain ⟨lane,hid,rfl⟩ := actual_mma_call hm
  have hl : lane = 0 := Fin.ext (by change lane.val = 0; simpa only [call_lane] using hzero)
  subst lane
  exact ⟨congrArg ThreadId.cta hid,rfl⟩

def readWitness : Unified.ReadsFrom
  | .base _,_ => none
  | .wgmmaRead _ operand,_ => some (nativeProducer operand)
def initialProxyMemory (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame : Location → Symbolic.Byte) : Unified.ProxyMemory :=
  fun _ => representedInitial a b frame

theorem base_read_witness_value {a b frame read loc value}
    (hr : Access.readByte Tma.localShared Access.globalDescriptor (candidate a b).view read loc = some value) :
    representedInitial a b frame loc = value := by
  apply Access.initial_read_value (initial := initialProxyMemory a b frame)
    (ordinary_read_none a b) (no_nonbulk a b) (ht := ?_) (hd := ?_) hr
  · intro id op hc
    rcases all_source_copies hc with rfl | rfl
    · exact initial_descriptor_a a b frame
    · exact initial_descriptor_b a b frame
  · intro id offset loc value hl hv
    cases hc : Tma.copyAt (candidate a b).view id with
    | none => simp [Tma.readLocation,hc] at hl
    | some op =>
      have ho : offset < op.descriptor.bytes := by
        have hh := List.getElem?_eq_some_iff.mp (show op.payload[offset]? = some value by simpa [Tma.transferByte,hc] using hv)
        rcases all_source_copies hc with rfl | rfl
        · change offset < 2048; simpa only [copyA,aPayload,List.length_ofFn] using hh.1
        · change offset < 256; simpa only [copyB,bPayload,List.length_ofFn] using hh.1
      have hp := stage_payload_agreement a b frame id op hc offset ho
      have hs : Tma.sourceByte op.descriptor op.coordinates offset = some loc := by simpa [Tma.readLocation,hc] using hl
      have hb : op.payload[offset]? = some value := by simpa [Tma.transferByte,hc] using hv
      exact Option.some.inj (hb.symm.trans (by simpa [Tma.byteValue,hs,initialProxyMemory] using hp))

theorem read_witness_value (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame : Location → Symbolic.Byte)
    (read loc value) (hr : Unified.readByte Tma.localShared Access.globalDescriptor (candidate a b) read loc = some value) :
    Unified.sourceValue Tma.localShared Access.globalDescriptor (candidate a b) (initialProxyMemory a b frame) read loc (readWitness read loc) = some value := by
  cases read with
  | base node =>
    exact congrArg some (base_read_witness_value hr)
  | wgmmaRead issue operand =>
    obtain ⟨mark,call,he,hl,hv⟩ := Unified.native_read_location hr
    obtain ⟨hcta,hcall⟩ := actual_representative_call he
    subst call
    subst loc
    have hloc : Wgmma.operandLocation issue.thread.cta (calls a b 0) operand = nativeLocation a b operand := by rw [hcta]; rfl
    rw [hloc]
    change Unified.writeByte _ _ _ (nativeProducer operand) _ = some value
    rw [native_producer_write,hv]
    exact congrArg some (transfer_agreement a b 0 operand).symm

theorem read_witness_agreement (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame : Location → Symbolic.Byte) :
    Unified.ReadAgreement Tma.localShared Access.globalDescriptor (candidate a b) (initialProxyMemory a b frame)
      (Unified.Eligible Tma.localShared Access.globalDescriptor (candidate a b) histories cluster readWitness) readWitness :=
  fun read loc value _ hr => read_witness_value a b frame read loc value hr

end
end Ptx.Kernels.HopperStage
