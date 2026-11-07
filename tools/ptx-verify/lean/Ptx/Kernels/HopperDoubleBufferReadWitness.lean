import Ptx.Kernels.HopperDoubleBufferNativeEligibility
import Ptx.Hopper.InitialReadAgreement

/-! Explicit RF and value agreement for the repeated real-data source. Global
input/descriptor reads select the independently represented initial memory;
native reads select their actual round's TMA producer. No assumed memory
execution is a construction premise. Causal/coherence/observer existence
remains a separate obligation. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem data_ordinary_read_none (a b tiles) (id : Ptx.Event.EventId) (loc : Location) :
    Access.readByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles).view (.tma (.source id)) loc = none := by
  cases he : (dataCompleteCandidate a b tiles).view.eventAt id with
  | none => simp only [Access.readByte,Access.kind,he,Option.bind_none]
  | some event =>
    have hs := data_view_memory_shape he
    simp only [Access.readByte,Access.kind,he,Option.bind_some]
    cases event with
    | ampere event =>
      cases event with
      | ordinary kind =>
        cases kind with
        | read _ _ | rmw _ _ _ => cases hs
        | write _ _ | barrierArrival _ _ | barrierReturn _ _ => rfl
      | issue _ _ | commit _ | wait _ _ | mmaEntry _ | mmaReturn _ => rfl
    | tmaIssue _ | proxyFenceAsyncShared _ | barrier _ | wgmma _ => rfl

theorem data_representative_call {a b tiles id mark call}
    (he : (dataCompleteCandidate a b tiles).representativeAt id = some (mark,call)) :
    ∃ tile < tiles, id = dataMmaId a b tiles tile 0 ∧ call = dataIterationCall a b tiles tile 0 := by
  obtain ⟨hm,hzero⟩ := Unified.representative_at he
  obtain ⟨tile,lane,ht,hid,_⟩ := data_native_mma_case hm
  have hi : dataNativeId a b tiles tile lane 1 = dataMmaId a b tiles tile lane := rfl
  rw [hid,hi] at hm
  have hc := (Wgmma.Event.mma.inj (Option.some.inj (hm.symm.trans (data_candidate_mma_at a b tiles tile lane ht)))).2
  subst call
  have hl : lane = 0 := Fin.ext (by simpa only [data_call_lane,Fin.val_zero] using hzero)
  subst lane
  exact ⟨tile,ht,hid.trans hi,rfl⟩

def dataReadWitness (a : TileA) (b : TileB) (tiles : Nat) : Unified.ReadsFrom
  | .base _,_ => none
  | .wgmmaRead issue operand,_ => ((dataCompleteCandidate a b tiles).representativeAt issue).map
      (fun pair => dataNativeProducer a b tiles pair.2.ordinal operand)
def dataInitialProxyMemory (a : TileA) (b : TileB) (tiles : Nat) (frame : Location → Symbolic.Byte) : Unified.ProxyMemory :=
  fun _ => dataRepresentedInitial a b tiles frame

theorem data_read_witness_current (a b tiles tile) (ht : tile < tiles) (operand : Wgmma.OperandByte) :
    dataReadWitness a b tiles (dataNativeRead a b tiles tile operand) (dataNativeLocation a b tiles tile operand) =
      some (dataNativeProducer a b tiles tile operand) := by
  change ((dataCompleteCandidate a b tiles).representativeAt (dataMmaId a b tiles tile 0)).map _ = _
  rw [data_collective_representative a b tiles tile ht]
  simp only [Option.map_some,data_call_ordinal]

theorem data_base_read_witness_value {a b tiles frame read loc value} (hb : tiles ≤ 2^28)
    (hr : Access.readByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles).view read loc = some value) :
    dataRepresentedInitial a b tiles frame loc = value := by
  apply Access.initial_read_value (initial := dataInitialProxyMemory a b tiles frame)
    (data_ordinary_read_none a b tiles) (data_no_nonbulk a b tiles) (ht := ?_) (hd := ?_) hr
  · intro id op hc
    exact data_stored_descriptor_agreement a b tiles frame op.descriptorAddress op.descriptor
      (data_descriptor_agreement a b tiles hb id op hc)
  · intro id offset loc value hl hv
    cases hc : Tma.copyAt (dataCompleteCandidate a b tiles).view id with
    | none => simp only [Tma.readLocation,hc,Option.bind_none] at hl; cases hl
    | some op =>
      have hlen : op.payload.length = op.descriptor.bytes := by
        obtain ⟨tile,ht,hcopy⟩ := data_all_source_copies a b tiles hb id op hc
        rcases hcopy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
          simp only [dataCopyA,dataCopyB,HopperStage.a_payload_length,HopperStage.b_payload_length,
            aView,bView,Tma.Descriptor2D.bytes]
      have ho : offset < op.descriptor.bytes := by
        have hh := (List.getElem?_eq_some_iff.mp (show op.payload[offset]? = some value by
          simpa only [Tma.transferByte,hc,Option.bind_some] using hv)).1
        omega
      have hp := data_payload_agreement a b tiles frame hb id op hc offset ho
      have hs : Tma.sourceByte op.descriptor op.coordinates offset = some loc := by
        simpa only [Tma.readLocation,hc,Option.bind_some] using hl
      have hpayload : op.payload[offset]? = some value := by simpa only [Tma.transferByte,hc,Option.bind_some] using hv
      exact Option.some.inj (hpayload.symm.trans (by simpa only [Tma.byteValue,hs,dataInitialProxyMemory] using hp))

theorem data_read_witness_value (a b tiles frame) (hb : tiles ≤ 2^28) (read loc value)
    (hr : Unified.readByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) read loc = some value) :
    Unified.sourceValue Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataInitialProxyMemory a b tiles frame) read loc (dataReadWitness a b tiles read loc) = some value := by
  cases read with
  | base node => exact congrArg some (data_base_read_witness_value hb hr)
  | wgmmaRead issue operand =>
    obtain ⟨mark,call,he,hl,hv⟩ := Unified.native_read_location hr
    obtain ⟨tile,ht,rfl,rfl⟩ := data_representative_call he
    subst loc
    simp only [dataReadWitness,he,Option.map_some,data_call_ordinal,Unified.sourceValue]
    change Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataNativeProducer a b tiles tile operand) (dataNativeLocation a b tiles tile operand) = some value
    rw [data_native_producer_write a b tiles tile ht hb operand,hv]

theorem data_read_witness_agreement (a b tiles frame) (hb : tiles ≤ 2^28) :
    Unified.ReadAgreement Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataInitialProxyMemory a b tiles frame)
      (Unified.Eligible Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
        (dataHistories a b tiles) dataCluster (dataReadWitness a b tiles)) (dataReadWitness a b tiles) :=
  fun read loc value _ hr => data_read_witness_value a b tiles frame hb read loc value hr

end
end Ptx.Kernels.HopperDoubleBuffer
