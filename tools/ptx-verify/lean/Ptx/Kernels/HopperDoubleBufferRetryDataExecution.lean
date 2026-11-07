import Ptx.Kernels.HopperDoubleBufferRetryDataMemory
import Ptx.Kernels.HopperDoubleBufferRetryObservedOutput

/-! Joint checked source/TMA/control/memory/tensor/observer witnesses and
observed GEMM bytes for every finite heterogeneous retry schedule, positive K
and independent real inputs. These are existing model components, not a claim
of physical ISA/runtime, allocation/lifetime or IEEE correspondence. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def retryDataObservation (a : TileA) (b : TileB) (tiles : Nat) (schedules : Wgmma.Lane → Nat → Nat) (frame : Location → Symbolic.Byte) : Unified.Observation :=
  retryObservation (retryDataFamily a b tiles schedules) (dataInitialProxyMemory a b tiles frame)

theorem retry_data_observer_witness (a b tiles schedules frame) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Unified.ObserverConditions Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (dataInitialProxyMemory a b tiles frame) (retryDataReadWitness a b tiles schedules) (retryDataCoherenceWitness a b tiles schedules)
      (retryHistories (retryDataFamily a b tiles schedules)) dataCluster (retryDataObservation a b tiles schedules frame) :=
  retry_observer_from_memory (retryDataFamily a b tiles schedules) hb
    (retry_data_source a b tiles schedules (dataRepresentedInitial a b tiles frame) ht hb) (retry_data_complete a b tiles schedules ht hb)
    (retry_data_descriptors a b tiles schedules ht hb) (retry_data_memory_witness a b tiles schedules frame ht hb)

theorem retry_data_observed_matrix_byte (a b tiles schedules frame) (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    (retryDataObservation a b tiles schedules frame).output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      .realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val :=
  retry_observed_matrix_byte (retryDataFamily a b tiles schedules)
    (retry_data_source a b tiles schedules (dataRepresentedInitial a b tiles frame) ht hb) (retry_data_complete a b tiles schedules ht hb)
    (retry_data_descriptors a b tiles schedules ht hb) hb (retry_data_memory_witness a b tiles schedules frame ht hb) rfl
    (fun tile hi => ⟨dataSharedTile a b tile,retry_data_tensor_component a b tiles schedules tile hi⟩)
    (retry_data_observer_witness a b tiles schedules frame ht hb) lane slot index

theorem retry_data_observed_frame (a b tiles schedules frame) (ht : 0 < tiles) (hb : tiles ≤ 2^28) (loc : Location)
    (hd : loc ∈ (retryDataObservation a b tiles schedules frame).domain) (hg : loc.space = .global)
    (hout : ¬(8192 ≤ loc.address ∧ loc.address < 10240)) :
    (retryDataObservation a b tiles schedules frame).output loc = dataRepresentedInitial a b tiles frame loc :=
  retry_observed_frame (retryDataFamily a b tiles schedules) hb
    (retry_data_source a b tiles schedules (dataRepresentedInitial a b tiles frame) ht hb) (retry_data_complete a b tiles schedules ht hb)
    (retry_data_descriptors a b tiles schedules ht hb) (retry_data_observer_witness a b tiles schedules frame ht hb) hd hg hout

theorem retry_data_complete_components (a b tiles schedules frame) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Unified.TmaComponents code (completeLaunch tiles (dataRepresentedInitial a b tiles frame))
      (retryDataCandidate a b tiles schedules) Tma.localShared (dataMaps tiles) (retryHistories (retryDataFamily a b tiles schedules)) ∧
    Unified.ControlAdmitted HopperStage.block (retryDataCandidate a b tiles schedules) (retryHistories (retryDataFamily a b tiles schedules)) ∧
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (dataInitialProxyMemory a b tiles frame) (retryDataReadWitness a b tiles schedules) (retryDataCoherenceWitness a b tiles schedules)
      (retryHistories (retryDataFamily a b tiles schedules)) dataCluster ∧
    (∀ tile < tiles, Wgmma.TensorConditions .zero ((retryDataFamily a b tiles schedules).calls tile) (dataSharedTile a b tile)) ∧
    Unified.ObserverConditions Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (dataInitialProxyMemory a b tiles frame) (retryDataReadWitness a b tiles schedules) (retryDataCoherenceWitness a b tiles schedules)
      (retryHistories (retryDataFamily a b tiles schedules)) dataCluster (retryDataObservation a b tiles schedules frame) := by
  obtain ⟨htma,hcontrol,htensor⟩ := retry_data_tma_control_tensor_components a b tiles schedules frame ht hb
  exact ⟨htma,hcontrol,retry_data_memory_witness a b tiles schedules frame ht hb,htensor,retry_data_observer_witness a b tiles schedules frame ht hb⟩

theorem retry_data_execution_exists (a b tiles schedules frame) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    ∃ (candidate : Unified.Candidate) (family : ReplySourceFamily tiles candidate)
      (rf : Unified.ReadsFrom) (co : Location → Option Unified.Node → Option Unified.Node → Prop) (obs : Unified.Observation),
      family.schedules = schedules ∧
      Unified.TmaComponents code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate Tma.localShared (dataMaps tiles) (retryHistories family) ∧
      Unified.ControlAdmitted HopperStage.block candidate (retryHistories family) ∧
      Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate (dataInitialProxyMemory a b tiles frame) rf co (retryHistories family) dataCluster ∧
      (∀ tile < tiles, Wgmma.TensorConditions .zero (family.calls tile) (dataSharedTile a b tile)) ∧
      Unified.ObserverConditions Tma.localShared Access.globalDescriptor candidate (dataInitialProxyMemory a b tiles frame) rf co (retryHistories family) dataCluster obs ∧
      ∀ lane slot (index : Fin 4), obs.output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
        .realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val := by
  obtain ⟨htma,hcontrol,hmemory,htensor,hobserver⟩ := retry_data_complete_components a b tiles schedules frame ht hb
  exact ⟨retryDataCandidate a b tiles schedules,retryDataFamily a b tiles schedules,retryDataReadWitness a b tiles schedules,
    retryDataCoherenceWitness a b tiles schedules,retryDataObservation a b tiles schedules frame,rfl,
    htma,hcontrol,hmemory,htensor,hobserver,fun lane slot index => retry_data_observed_matrix_byte a b tiles schedules frame ht hb lane slot index⟩

end
end Ptx.Kernels.HopperDoubleBuffer
