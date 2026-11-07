import Ptx.Kernels.HopperDoubleBufferObservedOutput
import Ptx.Tests.HopperDoubleBufferData

/-! Actual source-indexed global stores, compatible completed observation,
matrix/frame bytes and malformed observer rejection. Closed decidable checks
only inspect locations, source IDs and domain metadata, never real equality. -/
namespace Ptx.HopperDoubleBufferObservedOutputTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev a := HopperDoubleBufferDataTests.a
abbrev b := HopperDoubleBufferDataTests.b
def selection (loc : Location) : Option Unified.Node := dataOutputSelect a b 3 loc

theorem output_domain_size : dataOutputDomain.length = 2056 := by decide
theorem domain_boundary : (⟨.global,8188⟩ : Location) ∈ dataOutputDomain ∧
    (⟨.global,10243⟩ : Location) ∈ dataOutputDomain ∧
    (⟨.global,8187⟩ : Location) ∉ dataOutputDomain ∧ (⟨.global,10244⟩ : Location) ∉ dataOutputDomain := by decide
theorem domain_shared_excluded : (⟨.shared .zero,8192⟩ : Location) ∉ dataOutputDomain := by decide
theorem first_word_owner : dataOutputOwner 8192 = (0,0) ∧ dataOutputOwner 8195 = (0,0) := by decide
theorem last_byte_owner : dataOutputOwner 10239 = (127,3) := by decide
theorem first_store_selected : selection ⟨.global,8192⟩ = some (.base (.tma (.source (dataStoreId a b 3 0 0)))) := by decide
theorem last_store_selected : selection ⟨.global,10239⟩ = some (.base (.tma (.source (dataStoreId a b 3 127 3)))) := by decide
theorem adjacent_frame_unselected : selection ⟨.global,8191⟩ = none ∧ selection ⟨.global,10240⟩ = none := by decide
theorem input_descriptor_shared_unselected : selection ⟨.global,65536⟩ = none ∧ selection ⟨.global,4096⟩ = none ∧
    selection ⟨.shared .zero,8192⟩ = none := by decide
theorem actual_store_serials_distinct (x : TileA) (y : TileB) (tiles : Nat) (lane : Wgmma.Lane) :
    dataStoreId x y tiles lane 0 ≠ dataStoreId x y tiles lane 3 := by
  intro he
  have hh := congrArg Ptx.Event.EventId.serial he
  change (dataPreOutputEvents x y tiles lane).length+0 = (dataPreOutputEvents x y tiles lane).length+3 at hh
  omega

theorem arbitrary_global_writer_unique (x : TileA) (y : TileB) (tiles : Nat) (hb : tiles ≤ 2^28)
    (loc : Location) (hg : loc.space = .global) (left right : Unified.Node) (lv rv : Symbolic.Byte)
    (hl : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate x y tiles) left loc = some lv)
    (hr : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate x y tiles) right loc = some rv) : left = right :=
  data_global_unique_writers hb hg hl hr

theorem arbitrary_compatible_observer (x : TileA) (y : TileB) (tiles : Nat) (hb : tiles ≤ 2^28) (frame : Location → Symbolic.Byte) :
    Unified.ObserverConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate x y tiles)
      (dataInitialProxyMemory x y tiles frame) (dataReadWitness x y tiles) (dataCoherenceWitness x y tiles)
      (dataHistories x y tiles) dataCluster (dataObservation x y tiles frame) := data_observer_witness x y tiles frame hb

theorem repeated_output_byte (frame : Location → Symbolic.Byte) :
    (dataObservation a b 5 frame).output ((⟨.global,outputWordAddress (127,3)⟩ : Location).add 3) =
      .realPart .f32 (specification a b 5 (Wgmma.cCoord (127,3))) 3 :=
  data_independent_observed_matrix a b 5 frame (by decide) 127 3 3
theorem zero_round_output (frame : Location → Symbolic.Byte) :
    (dataObservation a b 0 frame).output ((⟨.global,outputWordAddress (0,0)⟩ : Location).add 0) = .realPart .f32 0 0 := by
  simpa only [specification,Finset.range_zero,Finset.sum_empty,Fin.val_zero] using
    data_independent_observed_matrix a b 0 frame (by decide) 0 0 0
theorem left_frame_preserved (frame : Location → Symbolic.Byte) :
    (dataObservation a b 3 frame).output ⟨.global,8191⟩ = frame ⟨.global,8191⟩ :=
  data_independent_observed_frame a b 3 frame (by decide) _ (by decide) (by decide)
theorem right_frame_preserved (frame : Location → Symbolic.Byte) :
    (dataObservation a b 3 frame).output ⟨.global,10240⟩ = frame ⟨.global,10240⟩ :=
  data_independent_observed_frame a b 3 frame (by decide) _ (by decide) (by decide)

theorem ordinary_matmul_contract (x : Fin 64 × Nat → ℝ) (y : Nat × Fin 8 → ℝ) (tiles : Nat) (hb : tiles ≤ 2^28)
    (frame : Location → Symbolic.Byte) (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    (dataObservation (tileA x) (tileB y) tiles frame).output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      .realPart .f32 (matmul x y tiles (Wgmma.cCoord (lane,slot))) index.val :=
  data_independent_observed_matmul x y tiles frame hb lane slot index

theorem arbitrary_compatible_matrix_byte (x : TileA) (y : TileB) (tiles : Nat) (hb : tiles ≤ 2^28)
    (initial : Unified.ProxyMemory) (rf : Unified.ReadsFrom) (co : Location → Option Unified.Node → Option Unified.Node → Prop)
    (obs : Unified.Observation)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate x y tiles)
      initial rf co (dataHistories x y tiles) dataCluster)
    (ho : Unified.ObserverConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate x y tiles)
      initial rf co (dataHistories x y tiles) dataCluster obs)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    obs.output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      .realPart .f32 (specification x y tiles (Wgmma.cCoord (lane,slot))) index.val :=
  data_observed_matrix_byte hb hm.toCausalConstraints ho lane slot index

theorem all_components_compatible (x : TileA) (y : TileB) (tiles : Nat) (hb : tiles ≤ 2^28) (frame : Location → Symbolic.Byte) :
    Unified.TmaComponents code (completeLaunch tiles (dataRepresentedInitial x y tiles frame))
        (dataCompleteCandidate x y tiles) Tma.localShared (dataMaps tiles) (dataHistories x y tiles) ∧
    Unified.ControlAdmitted HopperStage.block (dataCompleteCandidate x y tiles) (dataHistories x y tiles) ∧
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate x y tiles)
      (dataInitialProxyMemory x y tiles frame) (dataReadWitness x y tiles) (dataCoherenceWitness x y tiles) (dataHistories x y tiles) dataCluster ∧
    Unified.ObserverConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate x y tiles)
      (dataInitialProxyMemory x y tiles frame) (dataReadWitness x y tiles) (dataCoherenceWitness x y tiles)
      (dataHistories x y tiles) dataCluster (dataObservation x y tiles frame) := data_independent_observed_components x y tiles frame hb

theorem omitted_observer_rejected (frame : Location → Symbolic.Byte) :
    ¬Unified.ObserverConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 3)
      (dataInitialProxyMemory a b 3 frame) (dataReadWitness a b 3) (dataCoherenceWitness a b 3)
      (dataHistories a b 3) dataCluster (dataOmittedObservation a b 3 frame) := data_omitted_output_rejected a b 3 frame
theorem stale_observer_rejected (frame : Location → Symbolic.Byte) :
    ¬Unified.ObserverConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 3)
      (dataInitialProxyMemory a b 3 frame) (dataReadWitness a b 3) (dataCoherenceWitness a b 3)
      (dataHistories a b 3) dataCluster (dataStaleObservation a b 3 frame) := data_stale_output_rejected a b 3 frame (by decide)

end
end Ptx.HopperDoubleBufferObservedOutputTests
