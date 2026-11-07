import Ptx.Kernels.HopperDoubleBufferRetryDataTma
import Ptx.Kernels.HopperDoubleBufferReadWitness
import Ptx.Hopper.InitialReadAgreement

/-! Explicit reads-from values for independently constructed retry data.
Global input/descriptor reads use represented initial memory; native operand
reads use the actual current tile's TMA writer. No admitted memory premise is
used. Causality/coherence/atomicity/SC still require their own witnesses. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_data_transfer_a_byte (a b tiles schedules tile) (ht : tile < tiles) (hpos : 0 < tiles) (hb : tiles ≤ 2^28) (offset : Fin 2048) :
    Tma.transferByte (retryDataCandidate a b tiles schedules).view ((retryDataFamily a b tiles schedules).copyAId tile) offset.val =
      some (dataSharedTile a b tile ⟨.shared .zero,aBase (stage tile)+offset.val⟩) := by
  rw [Tma.transferByte,family_copy_a_at (retryDataFamily a b tiles schedules)
    (retry_data_source a b tiles schedules (fun _ => .bits (byte 0)) hpos hb) tile ht]
  change (replyCopyA tiles (retryDataOracle a b tiles schedules 0) (schedules 0) tile).payload[offset.val]? = _
  rw [(retry_data_copy_a_fields a b tiles schedules tile ht).2]
  have hp := HopperStage.transfer_a_payload (a tile) (b tile) offset
  simpa only [dataSharedTile,HopperStage.transferView,Wgmma.tileMemory,Nat.add_sub_cancel_left] using hp

theorem retry_data_transfer_b_byte (a b tiles schedules tile) (ht : tile < tiles) (hpos : 0 < tiles) (hb : tiles ≤ 2^28) (offset : Fin 256) :
    Tma.transferByte (retryDataCandidate a b tiles schedules).view ((retryDataFamily a b tiles schedules).copyBId tile) offset.val =
      some (dataSharedTile a b tile ⟨.shared .zero,bBase (stage tile)+offset.val⟩) := by
  rw [Tma.transferByte,family_copy_b_at (retryDataFamily a b tiles schedules)
    (retry_data_source a b tiles schedules (fun _ => .bits (byte 0)) hpos hb) tile ht]
  change (replyCopyB tiles (retryDataOracle a b tiles schedules 0) (schedules 0) tile).payload[offset.val]? = _
  rw [(retry_data_copy_b_fields a b tiles schedules tile ht).2]
  have hp := HopperStage.transfer_b_payload (a tile) (b tile) offset
  have hs : bBase (stage tile)+offset.val-aBase (stage tile) = 2048+offset.val := by dsimp [aBase,bBase]; omega
  have hs0 : 2064+offset.val-16 = 2048+offset.val := by omega
  simpa only [dataSharedTile,HopperStage.transferView,Wgmma.tileMemory,hs,hs0] using hp

theorem retry_data_producer_storage (a b tiles schedules tile) (ht : tile < tiles) (hpos : 0 < tiles) (hb : tiles ≤ 2^28) (operand : Wgmma.OperandByte) :
    Unified.writeByte Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (retryNativeProducer (retryDataFamily a b tiles schedules) tile operand) (retryNativeLocation (retryDataFamily a b tiles schedules) tile operand) =
      some (dataSharedTile a b tile (retryNativeLocation (retryDataFamily a b tiles schedules) tile operand)) := by
  have hw := retry_data_source a b tiles schedules (fun _ => .bits (byte 0)) hpos hb
  have hd := retry_data_descriptors a b tiles schedules hpos hb
  cases operand with
  | a p part =>
    rw [retry_native_a_location]
    exact Access.tensor_write (descriptor := Access.globalDescriptor) (retry_transfer_a_location (retryDataFamily a b tiles schedules) hw hd tile ht _)
      (retry_data_transfer_a_byte a b tiles schedules tile ht hpos hb (Wgmma.aOffset (p,part)))
  | b p part =>
    rw [retry_native_b_location]
    exact Access.tensor_write (descriptor := Access.globalDescriptor) (retry_transfer_b_location (retryDataFamily a b tiles schedules) hw hd tile ht _)
      (retry_data_transfer_b_byte a b tiles schedules tile ht hpos hb (Wgmma.bOffset (p,part)))

theorem retry_data_representative_call {a b tiles schedules id mark call} (hpos : 0 < tiles) (hb : tiles ≤ 2^28)
    (he : (retryDataCandidate a b tiles schedules).representativeAt id = some (mark,call)) :
    ∃ tile < tiles, id = (retryDataFamily a b tiles schedules).mmaId tile 0 ∧ call = (retryDataFamily a b tiles schedules).calls tile 0 := by
  obtain ⟨hm,hzero⟩ := Unified.representative_at he
  obtain ⟨tile,lane,ht,hid,_,hcall⟩ := retry_native_mma_case (retryDataFamily a b tiles schedules)
    (retry_data_source a b tiles schedules (fun _ => .bits (byte 0)) hpos hb) hm
  have hl : lane = 0 := by
    apply Fin.ext
    rw [hcall] at hzero
    change (replyCall tiles lane (retryDataOracle a b tiles schedules lane) (schedules lane) tile).lane.val = 0 at hzero
    simpa only [reply_call_lane,Fin.val_zero] using hzero
  subst lane
  exact ⟨tile,ht,hid.trans (retry_native_mma_id _ tile 0),hcall⟩

def retryDataReadWitness (a : TileA) (b : TileB) (tiles : Nat) (schedules : Wgmma.Lane → Nat → Nat) : Unified.ReadsFrom
  | .base _,_ => none
  | .wgmmaRead issue operand,_ => ((retryDataCandidate a b tiles schedules).representativeAt issue).map
      (fun pair => retryNativeProducer (retryDataFamily a b tiles schedules) pair.2.ordinal operand)

theorem retry_data_read_witness_current (a b tiles schedules tile) (ht : tile < tiles) (hpos : 0 < tiles) (hb : tiles ≤ 2^28) (operand : Wgmma.OperandByte) :
    retryDataReadWitness a b tiles schedules (retryNativeRead (retryDataFamily a b tiles schedules) tile operand)
      (retryNativeLocation (retryDataFamily a b tiles schedules) tile operand) = some (retryNativeProducer (retryDataFamily a b tiles schedules) tile operand) := by
  change ((retryDataCandidate a b tiles schedules).representativeAt ((retryDataFamily a b tiles schedules).mmaId tile 0)).map _ = _
  rw [Unified.collective_representative (familyCollective (retryDataFamily a b tiles schedules)
    (retry_data_source a b tiles schedules (fun _ => .bits (byte 0)) hpos hb) tile ht)]
  change some (retryNativeProducer (retryDataFamily a b tiles schedules) (replyCall tiles 0 (retryDataOracle a b tiles schedules 0) (schedules 0) tile).ordinal operand) = _
  rw [reply_call_ordinal]

theorem retry_data_base_read_value {a b tiles schedules frame read loc value} (hpos : 0 < tiles) (hb : tiles ≤ 2^28)
    (hr : Access.readByte Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules).view read loc = some value) :
    dataRepresentedInitial a b tiles frame loc = value := by
  have hw := retry_data_source a b tiles schedules (dataRepresentedInitial a b tiles frame) hpos hb
  have hc := retry_data_complete a b tiles schedules hpos hb
  apply Access.initial_read_value (initial := dataInitialProxyMemory a b tiles frame)
    (candidate_ordinary_read_none hb hw hc) (candidate_no_nonbulk hb hw hc) (ht := ?_) (hd := ?_) hr
  · intro id op he
    exact data_stored_descriptor_agreement a b tiles frame op.descriptorAddress op.descriptor
      (retry_data_descriptors a b tiles schedules hpos hb id op he)
  · intro id offset loc value hl hv
    cases he : Tma.copyAt (retryDataCandidate a b tiles schedules).view id with
    | none => simp only [Tma.readLocation,he,Option.bind_none] at hl; cases hl
    | some op =>
      have hlen := Unified.tma_copy_payload_length hw he
      have hpayload : op.payload[offset]? = some value := by simpa only [Tma.transferByte,he,Option.bind_some] using hv
      have ho : offset < op.descriptor.bytes := by have hi := (List.getElem?_eq_some_iff.mp hpayload).1; omega
      have hp := retry_data_payload_agreement a b tiles schedules frame hpos hb id op he offset ho
      have hs : Tma.sourceByte op.descriptor op.coordinates offset = some loc := by simpa only [Tma.readLocation,he,Option.bind_some] using hl
      exact Option.some.inj (hpayload.symm.trans (by simpa only [Tma.byteValue,hs,dataInitialProxyMemory] using hp))

theorem retry_data_read_witness_value (a b tiles schedules frame) (hpos : 0 < tiles) (hb : tiles ≤ 2^28) (read loc value)
    (hr : Unified.readByte Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules) read loc = some value) :
    Unified.sourceValue Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (dataInitialProxyMemory a b tiles frame) read loc (retryDataReadWitness a b tiles schedules read loc) = some value := by
  cases read with
  | base node => exact congrArg some (retry_data_base_read_value hpos hb hr)
  | wgmmaRead issue operand =>
    obtain ⟨mark,call,he,hl,hv⟩ := Unified.native_read_location hr
    obtain ⟨tile,ht,rfl,rfl⟩ := retry_data_representative_call hpos hb he
    subst loc
    change Unified.sourceValue Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (dataInitialProxyMemory a b tiles frame) (retryNativeRead (retryDataFamily a b tiles schedules) tile operand)
      (retryNativeLocation (retryDataFamily a b tiles schedules) tile operand)
      (retryDataReadWitness a b tiles schedules (retryNativeRead (retryDataFamily a b tiles schedules) tile operand)
        (retryNativeLocation (retryDataFamily a b tiles schedules) tile operand)) = _
    rw [retry_data_read_witness_current a b tiles schedules tile ht hpos hb operand]
    change Unified.writeByte Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (retryNativeProducer (retryDataFamily a b tiles schedules) tile operand) (retryNativeLocation (retryDataFamily a b tiles schedules) tile operand) = some value
    rw [retry_data_producer_storage a b tiles schedules tile ht hpos hb operand,hv]
    exact congrArg some (retry_data_call_agreement a b tiles schedules tile 0 ht operand).symm

theorem retry_data_read_witness_agreement (a b tiles schedules frame) (hpos : 0 < tiles) (hb : tiles ≤ 2^28) :
    Unified.ReadAgreement Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (dataInitialProxyMemory a b tiles frame)
      (Unified.Eligible Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
        (retryHistories (retryDataFamily a b tiles schedules)) dataCluster (retryDataReadWitness a b tiles schedules)) (retryDataReadWitness a b tiles schedules) :=
  fun read loc value _ hr => retry_data_read_witness_value a b tiles schedules frame hpos hb read loc value hr

end
end Ptx.Kernels.HopperDoubleBuffer
