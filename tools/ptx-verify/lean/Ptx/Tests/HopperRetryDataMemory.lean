import Ptx.Kernels.HopperDoubleBufferRetryDataExecution
import Ptx.Tests.HopperRetryData

/-! Joint positive memory/execution components on real data with nonzero
heterogeneous retries, plus actual reuse-coherence/communication and observer
counterexamples. These are model-relative checks, not GPU execution results. -/
namespace Ptx.HopperRetryDataMemoryTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev schedule := HopperRetryDataTests.schedule
abbrev frame := HopperRetryDataTests.frame
abbrev family := HopperRetryDataTests.family
abbrev candidate := HopperRetryDataTests.candidate
abbrev rf (a b) := retryDataReadWitness a b 3 schedule
abbrev co (a b) := retryDataCoherenceWitness a b 3 schedule
abbrev initial (a b) := dataInitialProxyMemory a b 3 frame
abbrev observation (a b) := retryDataObservation a b 3 schedule frame
abbrev source (a b) := retry_data_source a b 3 schedule (dataRepresentedInitial a b 3 frame) (by decide) (by decide)

theorem positive_memory_witness (a b) :
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate a b) (initial a b) (rf a b) (co a b) (retryHistories (family a b)) dataCluster :=
  retry_data_memory_witness a b 3 schedule frame (by decide) (by decide)

theorem positive_joint_components (a b) :
    Unified.TmaComponents code (completeLaunch 3 (dataRepresentedInitial a b 3 frame)) (candidate a b) Tma.localShared (dataMaps 3) (retryHistories (family a b)) ∧
    Unified.ControlAdmitted HopperStage.block (candidate a b) (retryHistories (family a b)) ∧
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate a b) (initial a b) (rf a b) (co a b) (retryHistories (family a b)) dataCluster ∧
    (∀ tile < 3, Wgmma.TensorConditions .zero ((family a b).calls tile) (dataSharedTile a b tile)) ∧
    Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate a b) (initial a b) (rf a b) (co a b) (retryHistories (family a b)) dataCluster (observation a b) :=
  retry_data_complete_components a b 3 schedule frame (by decide) (by decide)

theorem actual_same_slot_coherence (a b) (operand : Wgmma.OperandByte) :
    co a b (retryNativeLocation (family a b) 0 operand) (some (retryNativeProducer (family a b) 0 operand)) (some (retryNativeProducer (family a b) 2 operand)) := by
  have hp0 := retry_data_producer_storage a b 3 schedule 0 (by decide) (by decide) (by decide) operand
  have hp2 := retry_data_producer_storage a b 3 schedule 2 (by decide) (by decide) (by decide) operand
  have hs := retry_native_location_same_stage (family a b) 0 2 (by decide) operand
  rw [← hs] at hp2
  refine ⟨?_,?_,?_⟩
  · change (Unified.writeByte Tma.localShared Access.globalDescriptor (candidate a b) (retryNativeProducer (family a b) 0 operand) (retryNativeLocation (family a b) 0 operand)).isSome = true
    rw [hp0]; rfl
  · change (Unified.writeByte Tma.localShared Access.globalDescriptor (candidate a b) (retryNativeProducer (family a b) 2 operand) (retryNativeLocation (family a b) 0 operand)).isSome = true
    rw [hp2]; rfl
  · apply Nat.add_lt_add_right _ 1
    exact retry_data_memory_byte_order_rank (by decide) (by decide)
      (retry_native_writes_order (family a b) (source a b) (retry_data_descriptors a b 3 schedule (by decide) (by decide))
        (by decide) 0 2 (by decide) (by decide) (by decide) operand)

theorem reversed_reuse_coherence_rejected (a b) (operand : Wgmma.OperandByte) :
    ¬co a b (retryNativeLocation (family a b) 0 operand) (some (retryNativeProducer (family a b) 2 operand)) (some (retryNativeProducer (family a b) 0 operand)) := by
  intro hr
  have hc := retry_data_coherent_witness a b 3 schedule (by decide) (by decide)
  exact hc.irrefl _ _ (hc.transitive _ _ _ _ (actual_same_slot_coherence a b operand) hr)

theorem actual_initialization_before_writer (a b) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    co a b (retryNativeLocation (family a b) tile operand) none (some (retryNativeProducer (family a b) tile operand)) :=
  (retry_data_coherent_witness a b 3 schedule (by decide) (by decide)).initialization _ _ _
    (retry_data_producer_storage a b 3 schedule tile tile.isLt (by decide) (by decide) operand)

theorem actual_from_read_rank (a b) (operand : Wgmma.OperandByte) :
    retryDataMemoryRank a b 3 schedule (retryNativeRead (family a b) 0 operand) <
      retryDataMemoryRank a b 3 schedule (retryNativeProducer (family a b) 2 operand) := by
  have hr := (HopperRetryDataTests.actual_native_read_values a b (0 : Fin 3) operand).1
  have hc := actual_same_slot_coherence a b operand
  rw [← retry_data_read_witness_current a b 3 schedule 0 (by decide) (by decide) (by decide) operand] at hc
  exact retry_data_memory_from_read_rank (by decide) (by decide) hr hc

theorem communication_cycles_rejected (a b) (node : Unified.Node) :
    ¬Ptx.Event.Path (fun left right => Unified.ProgramOrder (candidate a b) left right ∨
      Unified.Communication Tma.localShared Access.globalDescriptor (candidate a b) (rf a b) (co a b) left right) node node := by
  intro hp
  have hh := hp.rank_lt (retryDataMemoryRank a b 3 schedule) (fun _ _ he =>
    he.elim (retry_data_memory_program_order_rank (by decide) (by decide)) (retry_data_memory_communication_rank (by decide) (by decide)))
  omega

theorem observed_all_matrix_bytes (a b) (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    (observation a b).output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      .realPart .f32 (specification a b 3 (Wgmma.cCoord (lane,slot))) index.val :=
  retry_data_observed_matrix_byte a b 3 schedule frame (by decide) (by decide) lane slot index

theorem observed_nonzero_result (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    (observation (fun _ _ => 1) (fun _ _ => 2)).output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      .realPart .f32 96 index.val := by
  rw [observed_all_matrix_bytes]
  norm_num [specification]

theorem adjacent_frame_preserved (a b) :
    (observation a b).output ⟨.global,8191⟩ = .bits (byte 17) ∧ (observation a b).output ⟨.global,10240⟩ = .bits (byte 17) := by
  constructor
  · exact retry_data_observed_frame a b 3 schedule frame (by decide) (by decide) _
      (mem_data_output_domain.mpr ⟨rfl,by decide,by decide⟩) rfl (by decide)
  · exact retry_data_observed_frame a b 3 schedule frame (by decide) (by decide) _
      (mem_data_output_domain.mpr ⟨rfl,by decide,by decide⟩) rfl (by decide)

theorem initial_only_coherence_rejected (a b) (operand : Wgmma.OperandByte) :
    ¬Unified.Coherent Tma.localShared Access.globalDescriptor (candidate a b) (retryHistories (family a b)) dataCluster (rf a b)
      (Unified.InitialCo Tma.localShared Access.globalDescriptor (candidate a b)) :=
  retry_repeated_initial_co_rejected (family a b) (source a b) (retry_data_descriptors a b 3 schedule (by decide) (by decide))
    (by decide) 0 2 (by decide) (by decide) (by decide) (rf a b) operand

def omitted (a : TileA) (b : TileB) : Unified.Observation := {observation a b with domain := []}
def stale (a : TileA) (b : TileB) : Unified.Observation := {observation a b with source := fun _ => none,output := (initial a b) .generic}
def wrong : Unified.Observation := {observation (fun _ _ => 1) (fun _ _ => 2) with output := fun _ => .realPart .f32 0 0}

theorem omitted_output_rejected (a b) :
    ¬Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate a b) (initial a b) (rf a b) (co a b) (retryHistories (family a b)) dataCluster (omitted a b) := by
  intro ho
  have hp := ho.coverage _ _ _ rfl (retry_actual_output_byte (family a b) (source a b) 0 0 0)
  cases hp

theorem stale_output_rejected (a b) :
    ¬Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate a b) (initial a b) (rf a b) (co a b) (retryHistories (family a b)) dataCluster (stale a b) := by
  intro ho
  have hw := retry_actual_output_byte (family a b) (source a b) 0 0 0
  have hd := ho.coverage _ _ _ rfl hw
  have hh := ho.noStale _ hd (candidate_no_mixed_size_race (by decide) (source a b)
    (retry_data_complete a b 3 schedule (by decide) (by decide)) (retry_data_descriptors a b 3 schedule (by decide) (by decide))) _ _ hw
  exact hh ((retry_data_coherent_witness a b 3 schedule (by decide) (by decide)).initialization _ _ _ hw)

theorem fabricated_output_rejected :
    ¬Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate (fun _ _ => 1) (fun _ _ => 2))
      (initial (fun _ _ => 1) (fun _ _ => 2)) (rf (fun _ _ => 1) (fun _ _ => 2)) (co (fun _ _ => 1) (fun _ _ => 2))
      (retryHistories (family (fun _ _ => 1) (fun _ _ => 2))) dataCluster wrong := by
  intro ho
  have hv := retry_observed_matrix_byte (family (fun _ _ => 1) (fun _ _ => 2)) (source (fun _ _ => 1) (fun _ _ => 2))
    (retry_data_complete _ _ 3 schedule (by decide) (by decide)) (retry_data_descriptors _ _ 3 schedule (by decide) (by decide))
    (by decide) (positive_memory_witness (fun _ _ => 1) (fun _ _ => 2)) rfl
    (fun tile hi => ⟨_,retry_data_tensor_component _ _ 3 schedule tile hi⟩) ho 0 0 0
  change Symbolic.Byte.realPart .f32 0 0 = .realPart .f32 (specification (fun _ _ => 1) (fun _ _ => 2) 3 _) 0 at hv
  norm_num [specification] at hv

end
end Ptx.HopperRetryDataMemoryTests
