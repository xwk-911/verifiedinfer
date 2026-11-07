import Ptx.Kernels.HopperDoubleBufferRetryArbitraryOutput
import Ptx.Tests.HopperRetryDataMemory

/-! Arbitrary-history reads and GEMM observation, with independent real inputs
and heterogeneous retries. Positive joint witnesses and bad source/observer
cases keep the universal admission implications nonvacuous and value-sensitive. -/
namespace Ptx.HopperArbitraryOutputTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev schedule := HopperRetryDataMemoryTests.schedule
abbrev frame := HopperRetryDataMemoryTests.frame
abbrev family := HopperRetryDataMemoryTests.family
abbrev candidate := HopperRetryDataMemoryTests.candidate
abbrev initial := HopperRetryDataMemoryTests.initial
abbrev rf := HopperRetryDataMemoryTests.rf
abbrev co := HopperRetryDataMemoryTests.co
abbrev observation := HopperRetryDataMemoryTests.observation
abbrev complete (a b) := retry_data_complete a b 3 schedule (by decide) (by decide)
abbrev tensors (a b) : ∀ tile, tile < 3 → ∃ memory, Wgmma.TensorConditions .zero ((family a b).calls tile) memory :=
  fun tile ht => ⟨dataSharedTile a b tile,retry_data_tensor_component a b 3 schedule tile ht⟩

theorem all_histories_current_read (a b) (histories : Location → List Tma.Entry) (reads : Unified.ReadsFrom) (order)
    (htma : Unified.TmaComponents code (completeLaunch 3 (dataRepresentedInitial a b 3 frame)) (candidate a b) Tma.localShared (dataMaps 3) histories)
    (hc : Unified.ControlAdmitted HopperStage.block (candidate a b) histories)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate a b) (initial a b) reads order histories dataCluster)
    (tile : Fin 3) (operand : Wgmma.OperandByte) :
    reads (retryNativeRead (family a b) tile operand) (retryNativeLocation (family a b) tile operand) = some (retryNativeProducer (family a b) tile operand) :=
  arbitrary_history_native_reads_from_current (family a b) (by decide) (by decide) htma (complete a b) hc hm tile tile.isLt operand

theorem all_histories_operand_bytes (a b) (histories : Location → List Tma.Entry) (reads : Unified.ReadsFrom) (order)
    (htma : Unified.TmaComponents code (completeLaunch 3 (dataRepresentedInitial a b 3 frame)) (candidate a b) Tma.localShared (dataMaps 3) histories)
    (hc : Unified.ControlAdmitted HopperStage.block (candidate a b) histories)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate a b) (initial a b) reads order histories dataCluster)
    (tile : Fin 3) (operand : Wgmma.OperandByte) :
    Unified.readByte Tma.localShared Access.globalDescriptor (candidate a b) (retryNativeRead (family a b) tile operand) (retryNativeLocation (family a b) tile operand) =
      some (dataSharedTile a b tile (retryNativeLocation (family a b) tile operand)) :=
  arbitrary_history_operand_byte (family a b) (by decide) (by decide) htma (complete a b) hc hm rfl tile tile.isLt operand

theorem all_histories_tensor_inputs (a b) (histories : Location → List Tma.Entry) (reads : Unified.ReadsFrom) (order)
    (htma : Unified.TmaComponents code (completeLaunch 3 (dataRepresentedInitial a b 3 frame)) (candidate a b) Tma.localShared (dataMaps 3) histories)
    (hc : Unified.ControlAdmitted HopperStage.block (candidate a b) histories)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate a b) (initial a b) reads order histories dataCluster) (tile : Fin 3) :
    Wgmma.InputAgreement .zero ((family a b).calls tile 0) (dataSharedTile a b tile) :=
  arbitrary_history_tensor_inputs (family a b) (by decide) (by decide) htma (complete a b) hc hm rfl tile tile.isLt

theorem all_histories_matrix_outputs (a b) (histories : Location → List Tma.Entry) (reads : Unified.ReadsFrom) (order) (obs : Unified.Observation)
    (htma : Unified.TmaComponents code (completeLaunch 3 (dataRepresentedInitial a b 3 frame)) (candidate a b) Tma.localShared (dataMaps 3) histories)
    (hc : Unified.ControlAdmitted HopperStage.block (candidate a b) histories)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate a b) (initial a b) reads order histories dataCluster)
    (ho : Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate a b) (initial a b) reads order histories dataCluster obs)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    obs.output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      .realPart .f32 (specification a b 3 (Wgmma.cCoord (lane,slot))) index.val :=
  arbitrary_history_observed_matrix_byte (family a b) (by decide) (by decide) htma (complete a b) hc hm rfl (tensors a b) ho lane slot index

theorem all_histories_frame (a b) (histories : Location → List Tma.Entry) (reads : Unified.ReadsFrom) (order) (obs : Unified.Observation)
    (htma : Unified.TmaComponents code (completeLaunch 3 (dataRepresentedInitial a b 3 frame)) (candidate a b) Tma.localShared (dataMaps 3) histories)
    (hc : Unified.ControlAdmitted HopperStage.block (candidate a b) histories)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate a b) (initial a b) reads order histories dataCluster)
    (ho : Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate a b) (initial a b) reads order histories dataCluster obs)
    (loc : Location) (hd : loc ∈ obs.domain) (hg : loc.space = .global) (hout : ¬(8192 ≤ loc.address ∧ loc.address < 10240)) :
    obs.output loc = dataRepresentedInitial a b 3 frame loc :=
  (arbitrary_history_observed_gemm (family a b) (by decide) (by decide) htma (complete a b) hc hm rfl (tensors a b) ho).2 loc hd hg hout

theorem all_histories_stale_read_rejected (a b) (histories : Location → List Tma.Entry) (reads : Unified.ReadsFrom) (order)
    (htma : Unified.TmaComponents code (completeLaunch 3 (dataRepresentedInitial a b 3 frame)) (candidate a b) Tma.localShared (dataMaps 3) histories)
    (hc : Unified.ControlAdmitted HopperStage.block (candidate a b) histories)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate a b) (initial a b) reads order histories dataCluster)
    (operand : Wgmma.OperandByte) :
    reads (retryNativeRead (family a b) 2 operand) (retryNativeLocation (family a b) 2 operand) ≠ some (retryNativeProducer (family a b) 0 operand) :=
  publication_native_stale_source_rejected (family a b) (arbitrary_native_publication_facts (family a b) (by decide) htma hc)
    htma.source (complete a b) htma.descriptors (by decide) hm 2 0 (by decide) (by decide) (by decide) operand

theorem all_histories_future_read_rejected (a b) (histories : Location → List Tma.Entry) (reads : Unified.ReadsFrom) (order)
    (htma : Unified.TmaComponents code (completeLaunch 3 (dataRepresentedInitial a b 3 frame)) (candidate a b) Tma.localShared (dataMaps 3) histories)
    (hc : Unified.ControlAdmitted HopperStage.block (candidate a b) histories)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate a b) (initial a b) reads order histories dataCluster)
    (operand : Wgmma.OperandByte) :
    reads (retryNativeRead (family a b) 0 operand) (retryNativeLocation (family a b) 0 operand) ≠ some (retryNativeProducer (family a b) 2 operand) :=
  publication_native_future_source_rejected (family a b) (arbitrary_native_publication_facts (family a b) (by decide) htma hc)
    htma.source (complete a b) htma.descriptors (by decide) hm 0 2 (by decide) (by decide) (by decide) operand

theorem all_histories_initial_source_rejected (a b) (histories : Location → List Tma.Entry) (reads : Unified.ReadsFrom) (order)
    (htma : Unified.TmaComponents code (completeLaunch 3 (dataRepresentedInitial a b 3 frame)) (candidate a b) Tma.localShared (dataMaps 3) histories)
    (hc : Unified.ControlAdmitted HopperStage.block (candidate a b) histories)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate a b) (initial a b) reads order histories dataCluster)
    (tile : Fin 3) (operand : Wgmma.OperandByte) :
    reads (retryNativeRead (family a b) tile operand) (retryNativeLocation (family a b) tile operand) ≠ none := by
  rw [all_histories_current_read a b histories reads order htma hc hm tile operand]
  simp

theorem all_histories_initial_co_rejected (a b) (histories : Location → List Tma.Entry) (reads : Unified.ReadsFrom)
    (htma : Unified.TmaComponents code (completeLaunch 3 (dataRepresentedInitial a b 3 frame)) (candidate a b) Tma.localShared (dataMaps 3) histories)
    (hc : Unified.ControlAdmitted HopperStage.block (candidate a b) histories) (operand : Wgmma.OperandByte) :
    ¬Unified.Coherent Tma.localShared Access.globalDescriptor (candidate a b) histories dataCluster reads
      (Unified.InitialCo Tma.localShared Access.globalDescriptor (candidate a b)) :=
  publication_repeated_initial_co_rejected (family a b) (arbitrary_native_publication_facts (family a b) (by decide) htma hc)
    htma.source htma.descriptors (by decide) 0 2 (by decide) (by decide) (by decide) reads operand

theorem positive_observed_matrix (a b) (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    (observation a b).output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      .realPart .f32 (specification a b 3 (Wgmma.cCoord (lane,slot))) index.val := by
  obtain ⟨htma,hc,hm,_,ho⟩ := HopperRetryDataMemoryTests.positive_joint_components a b
  exact all_histories_matrix_outputs a b _ _ _ _ htma hc hm ho lane slot index

theorem positive_nonzero_result (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    (observation (fun _ _ => 1) (fun _ _ => 2)).output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      .realPart .f32 96 index.val := by
  rw [positive_observed_matrix]
  norm_num [specification]

theorem positive_adjacent_frame (a b) :
    (observation a b).output ⟨.global,8191⟩ = .bits (byte 17) ∧ (observation a b).output ⟨.global,10240⟩ = .bits (byte 17) := by
  obtain ⟨htma,hc,hm,_,ho⟩ := HopperRetryDataMemoryTests.positive_joint_components a b
  constructor
  · exact all_histories_frame a b _ _ _ _ htma hc hm ho ⟨.global,8191⟩
      (by change (⟨.global,8191⟩ : Location) ∈ dataOutputDomain; decide) rfl (by decide)
  · exact all_histories_frame a b _ _ _ _ htma hc hm ho ⟨.global,10240⟩
      (by change (⟨.global,10240⟩ : Location) ∈ dataOutputDomain; decide) rfl (by decide)

theorem positive_constructed_interface_reuse (a b) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    rf a b (retryNativeRead (family a b) tile operand) (retryNativeLocation (family a b) tile operand) =
      some (retryNativeProducer (family a b) tile operand) := by
  obtain ⟨htma,_,hm,_⟩ := HopperRetryDataMemoryTests.positive_joint_components a b
  have hpub := constructed_native_publication_facts (family a b) (by decide) htma.source htma.descriptors
  exact publication_native_reads_from_current (family a b) hpub htma.source (complete a b) htma.descriptors (by decide) hm tile tile.isLt operand

theorem wrong_operand_byte_rejected (a b) (histories : Location → List Tma.Entry) (reads : Unified.ReadsFrom) (order)
    (htma : Unified.TmaComponents code (completeLaunch 3 (dataRepresentedInitial a b 3 frame)) (candidate a b) Tma.localShared (dataMaps 3) histories)
    (hc : Unified.ControlAdmitted HopperStage.block (candidate a b) histories) (tile : Fin 3) (operand : Wgmma.OperandByte) (value : Symbolic.Byte)
    (hr : Unified.readByte Tma.localShared Access.globalDescriptor (candidate a b) (retryNativeRead (family a b) tile operand) (retryNativeLocation (family a b) tile operand) = some value)
    (hne : value ≠ dataSharedTile a b tile (retryNativeLocation (family a b) tile operand)) :
    ¬Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate a b) (initial a b) reads order histories dataCluster := by
  intro hm
  have hv := all_histories_operand_bytes a b histories reads order htma hc hm tile operand
  exact hne (Option.some.inj (hr.symm.trans hv))

def wrongObservation (a : TileA) (b : TileB) : Unified.Observation :=
  {observation a b with output := fun loc => if loc = (⟨.global,8192⟩ : Location) then .realPart .f32 0 0 else (observation a b).output loc}

theorem wrong_output_observer_rejected (histories : Location → List Tma.Entry) (reads : Unified.ReadsFrom) (order)
    (htma : Unified.TmaComponents code (completeLaunch 3 (dataRepresentedInitial (fun _ _ => 1) (fun _ _ => 2) 3 frame))
      (candidate (fun _ _ => 1) (fun _ _ => 2)) Tma.localShared (dataMaps 3) histories)
    (hc : Unified.ControlAdmitted HopperStage.block (candidate (fun _ _ => 1) (fun _ _ => 2)) histories)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate (fun _ _ => 1) (fun _ _ => 2))
      (initial (fun _ _ => 1) (fun _ _ => 2)) reads order histories dataCluster) :
    ¬Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate (fun _ _ => 1) (fun _ _ => 2))
      (initial (fun _ _ => 1) (fun _ _ => 2)) reads order histories dataCluster (wrongObservation (fun _ _ => 1) (fun _ _ => 2)) := by
  intro ho
  have hv := all_histories_matrix_outputs (fun _ _ => 1) (fun _ _ => 2) histories reads order _ htma hc hm ho 0 0 0
  change Symbolic.Byte.realPart .f32 0 0 = .realPart .f32 (specification (fun _ _ => 1) (fun _ _ => 2) 3 (Wgmma.cCoord (0,0))) 0 at hv
  norm_num [specification,Symbolic.Byte.realPart.injEq] at hv

end
end Ptx.HopperArbitraryOutputTests
