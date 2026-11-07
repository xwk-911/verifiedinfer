import Ptx.Iris.ByteContentsSource
import Ptx.Kernels.HopperDoubleBufferByteContents
import Ptx.Kernels.HopperDoubleBufferByteExecution
import Ptx.Kernels.HopperDoubleBufferRetryDataExecution

/-! The real bounded positive-K Hopper data family supplies every frontier
obligation: base reads are immutable initial bytes and native reads select the
current TMA producer. No source-script existence or desired shared value is
assumed by these facts.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

def retryValueInitialState (a : TileA) (b : TileB) (tiles : Nat) (schedules : Wgmma.Lane → Nat → Nat)
    (frame : Location → Symbolic.Byte) (protocol : Ptx.Async.State) : ByteContents.State :=
  ⟨⟨protocol,fun _ => False⟩,ByteContents.initialCells (Whole.byteLocations (retryDataFamily a b tiles schedules)) (dataRepresentedInitial a b tiles frame)⟩

theorem retry_value_native_read_case {a b tiles schedules issue operand loc value}
    (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hr : ByteContents.readByte (retryDataCandidate a b tiles schedules) (.wgmmaRead issue operand) loc = some value) :
    ∃ tile < tiles, issue = (retryDataFamily a b tiles schedules).mmaId tile 0 ∧
      loc = retryNativeLocation (retryDataFamily a b tiles schedules) tile operand := by
  obtain ⟨mark,call,he,hl,_⟩ := Unified.native_read_location hr
  obtain ⟨tile,hi,hid,hcall⟩ := retry_data_representative_call ht hb he
  refine ⟨tile,hi,hid,?_⟩
  rw [hid,hcall] at hl
  exact hl

theorem retry_value_read_frontier (a b tiles schedules) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    ByteContentsHeap.ReadFrontier (byteContentsContext (retryDataFamily a b tiles schedules)) (retryDataReadWitness a b tiles schedules) := by
  let family := retryDataFamily a b tiles schedules
  have hw := retry_data_source a b tiles schedules (fun _ => .bits (byte 0)) ht hb
  have hc := retry_data_complete a b tiles schedules ht hb
  have hd := retry_data_descriptors a b tiles schedules ht hb
  have hn := candidate_no_nonbulk hb hw hc
  constructor
  · intro read loc value hr hrf writer written hwrite
    cases read with
    | base node =>
      have hi := retry_data_base_read_immutable ht hb hr writer
      change Unified.writeByte Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules) writer loc = some written at hwrite
      rw [hi] at hwrite
      cases hwrite
    | wgmmaRead issue operand =>
      obtain ⟨tile,hi,rfl,rfl⟩ := retry_value_native_read_case ht hb hr
      change retryDataReadWitness a b tiles schedules (retryNativeRead (retryDataFamily a b tiles schedules) tile operand) (retryNativeLocation (retryDataFamily a b tiles schedules) tile operand) = _ at hrf
      rw [retry_data_read_witness_current a b tiles schedules tile hi ht hb operand] at hrf
      cases hrf
  · intro read loc value hr writer hrf
    cases read with
    | base node => cases hrf
    | wgmmaRead issue operand =>
      obtain ⟨tile,hi,rfl,rfl⟩ := retry_value_native_read_case ht hb hr
      change retryDataReadWitness a b tiles schedules (retryNativeRead (retryDataFamily a b tiles schedules) tile operand) (retryNativeLocation (retryDataFamily a b tiles schedules) tile operand) = _ at hrf
      rw [retry_data_read_witness_current a b tiles schedules tile hi ht hb operand] at hrf
      have he := (Option.some.inj hrf).symm
      subst writer
      exact Unified.byte_order_control_path hn (retry_native_byte_order family ht hw hd tile hi operand)
  · intro read loc value hr writer hrf
    cases read with
    | base node => cases hrf
    | wgmmaRead issue operand =>
      obtain ⟨tile,hi,rfl,rfl⟩ := retry_value_native_read_case ht hb hr
      change retryDataReadWitness a b tiles schedules (retryNativeRead (retryDataFamily a b tiles schedules) tile operand) (retryNativeLocation (retryDataFamily a b tiles schedules) tile operand) = _ at hrf
      rw [retry_data_read_witness_current a b tiles schedules tile hi ht hb operand] at hrf
      have he := (Option.some.inj hrf).symm
      subst writer
      intro other written hwrite
      exact Or.inr (retry_byte_contents_phase family hw hc hd hb tile hi operand other written hwrite)

theorem retry_value_read_eligible (a b tiles schedules) (ht : 0 < tiles) (hb : tiles ≤ 2^28) (read loc value)
    (hr : ByteContents.readByte (retryDataCandidate a b tiles schedules) read loc = some value) :
    Unified.Eligible Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (retryHistories (retryDataFamily a b tiles schedules)) dataCluster (retryDataReadWitness a b tiles schedules) read loc := by
  have hw := retry_data_source a b tiles schedules (fun _ => .bits (byte 0)) ht hb
  have hc := retry_data_complete a b tiles schedules ht hb
  have hd := retry_data_descriptors a b tiles schedules ht hb
  cases read with
  | base node =>
    exact Unified.immutable_eligible (candidate_no_mixed_size_race hb hw hc hd) (retry_data_base_read_immutable ht hb hr)
  | wgmmaRead issue operand =>
    obtain ⟨tile,hi,rfl,rfl⟩ := retry_value_native_read_case ht hb hr
    exact retry_native_eligible (retryDataFamily a b tiles schedules) hw hc hd hb tile hi _ operand

theorem retry_value_initial_future (a b tiles schedules frame protocol) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    ByteContentsHeap.FutureReads (byteContentsContext (retryDataFamily a b tiles schedules)) (dataInitialProxyMemory a b tiles frame)
      (retryDataReadWitness a b tiles schedules) (retryValueInitialState a b tiles schedules frame protocol) := by
  have hw := retry_data_source a b tiles schedules (dataRepresentedInitial a b tiles frame) ht hb
  have hc := retry_data_complete a b tiles schedules ht hb
  have hd := retry_data_descriptors a b tiles schedules ht hb
  have hn := candidate_no_nonbulk hb hw hc
  have hbounded := Whole.byte_inventory_bounded (retryDataFamily a b tiles schedules) ht hb hw hc hd
  apply ByteContentsHeap.future_initial (by intro node h; exact h)
  intro read loc value hr hrf
  cases read with
  | base node =>
    have hu := ByteContents.actual_read_use hn hr
    have hl := hbounded _ loc .read hu
    have hg := ByteContents.initialCells_member (initial := dataRepresentedInitial a b tiles frame) hl
    have hp := retry_data_base_read_value (frame := frame) ht hb hr
    have hm := retry_data_read_witness_value a b tiles schedules frame ht hb (.base node) loc value hr
    rw [hrf,Unified.sourceValue] at hm
    change (get? (ByteContents.initialCells _ _) (ByteAuthority.key loc)).bind ByteContents.Payload.value = _
    rw [hg]
    exact congrArg some (hp.trans (Option.some.inj hm).symm)
  | wgmmaRead issue operand =>
    obtain ⟨tile,hi,rfl,rfl⟩ := retry_value_native_read_case ht hb hr
    change retryDataReadWitness a b tiles schedules (retryNativeRead (retryDataFamily a b tiles schedules) tile operand) (retryNativeLocation (retryDataFamily a b tiles schedules) tile operand) = _ at hrf
    rw [retry_data_read_witness_current a b tiles schedules tile hi ht hb operand] at hrf
    cases hrf

theorem retry_value_native_ready_needs_producer (a b tiles schedules) (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (tile : Nat) (hit : tile < tiles) (operand : Wgmma.OperandByte) (done : Cut)
    (hv : Valid HopperStage.block (retryDataCandidate a b tiles schedules) (retryHistories (retryDataFamily a b tiles schedules)) done)
    (hr : ByteAuthority.Ready HopperStage.block (retryDataCandidate a b tiles schedules) (retryHistories (retryDataFamily a b tiles schedules)) done
      (Unified.memoryControlNode (retryNativeRead (retryDataFamily a b tiles schedules) tile operand))) :
    done (Unified.memoryControlNode (retryNativeProducer (retryDataFamily a b tiles schedules) tile operand)) := by
  have hw := retry_data_source a b tiles schedules (fun _ => .bits (byte 0)) ht hb
  have hc := retry_data_complete a b tiles schedules ht hb
  have hd := retry_data_descriptors a b tiles schedules ht hb
  apply ByteContentsHeap.ready_path_before (ctx := byteContentsContext (retryDataFamily a b tiles schedules)) hv.1 hr
  apply Unified.byte_order_control_path (candidate_no_nonbulk hb hw hc)
  exact retry_native_byte_order (retryDataFamily a b tiles schedules) ht hw hd tile hit operand

end
end Ptx.Kernels.HopperDoubleBuffer
