import Ptx.Kernels.HopperDoubleBufferTensorAdmission
import Ptx.Kernels.HopperDoubleBufferRetryDataExecution
import Ptx.Kernels.HopperDoubleBufferZeroExecution

/-! One source-independent model-relative correctness and nonvacuity entry for
zero and positive bounded K. Existing instruction, memory and observer components
are packaged explicitly. Allocation/ownership, compiler/runtime and physical GPU
correspondence are not asserted by this execution record. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def ObservedGemm (a : TileA) (b : TileB) (tiles : Nat) (frame : Location → Symbolic.Byte) (observation : Unified.Observation) : Prop :=
  (∀ lane slot (index : Fin 4), observation.output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
    .realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val) ∧
  (∀ loc ∈ observation.domain, loc.space = .global → ¬(8192 ≤ loc.address ∧ loc.address < 10240) →
    observation.output loc = dataRepresentedInitial a b tiles frame loc)

def MatchesRetrySchedule (tiles : Nat) (candidate : Unified.Candidate) (schedules : Wgmma.Lane → Nat → Nat) : Prop :=
  0 < tiles → ∃ family : ReplySourceFamily tiles candidate, family.schedules = schedules

theorem completed_zero_tensor_components {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    Unified.TensorComponents candidate := by
  apply Unified.tensor_components_of_no_mma
  intro event mark call he
  have hn := completed_zero_native_signature_none hw hc event
  simp [Unified.Candidate.nativeSignatureAt,he,Wgmma.eventSignature,Wgmma.collective] at hn

theorem completed_zero_execution_components {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    Unified.ExecutionComponents code (completeLaunch 0 initial) candidate Tma.localShared Access.globalDescriptor (dataMaps 0)
      (fun _ => initial) zeroRf (zeroCo candidate) zeroHistories dataCluster (zeroObservation candidate initial) := by
  obtain ⟨htma,hcontrol,hmemory,_,hobserver⟩ := completed_zero_components hw hc
  exact ⟨htma,hcontrol,hmemory,completed_zero_tensor_components hw hc,hobserver⟩

theorem retry_data_execution_components (a b tiles schedules frame) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Unified.ExecutionComponents code (completeLaunch tiles (dataRepresentedInitial a b tiles frame))
      (retryDataCandidate a b tiles schedules) Tma.localShared Access.globalDescriptor (dataMaps tiles)
      (dataInitialProxyMemory a b tiles frame) (retryDataReadWitness a b tiles schedules) (retryDataCoherenceWitness a b tiles schedules)
      (retryHistories (retryDataFamily a b tiles schedules)) dataCluster (retryDataObservation a b tiles schedules frame) := by
  obtain ⟨htma,hcontrol,hmemory,htensor,hobserver⟩ := retry_data_complete_components a b tiles schedules frame ht hb
  refine ⟨htma,hcontrol,hmemory,?_,hobserver⟩
  exact (family_tensor_components_iff (retryDataFamily a b tiles schedules) htma.source).2 (fun tile htile => ⟨_,htensor tile htile⟩)

theorem execution_refines_gemm {a b tiles frame candidate initial rf co histories observation} (hb : tiles ≤ 2^28)
    (he : Unified.ExecutionComponents code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate
      Tma.localShared Access.globalDescriptor (dataMaps tiles) initial rf co histories dataCluster observation)
    (hi : initial = fun _ => dataRepresentedInitial a b tiles frame) : ObservedGemm a b tiles frame observation := by
  by_cases hz : tiles = 0
  · subst tiles
    constructor
    · intro lane slot index
      have hv := completed_zero_observed_output_of_admission he.tma.source he.tma.complete he.memory.toCausalConstraints he.observer lane slot index
      simpa only [specification,Finset.range_zero,Finset.sum_empty] using hv
    · intro loc hdom hg hout
      have hv := completed_zero_observed_frame_of_admission he.tma.source he.tma.complete he.observer hdom hg hout
      simpa only [hi] using hv
  · have ht : 0 < tiles := by omega
    obtain ⟨family⟩ := completed_candidate_reply_family ht hb he.tma.source he.tma.complete
    have htensor := (family_tensor_components_iff family he.tma.source).1 he.tensor
    exact arbitrary_history_observed_gemm family ht hb he.tma he.tma.complete he.control he.memory hi htensor he.observer

theorem gemm_execution_exists (a : TileA) (b : TileB) (tiles : Nat) (schedules : Wgmma.Lane → Nat → Nat)
    (frame : Location → Symbolic.Byte) (hb : tiles ≤ 2^28) :
    ∃ candidate initial rf co histories observation,
      MatchesRetrySchedule tiles candidate schedules ∧
      Unified.ExecutionComponents code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate
        Tma.localShared Access.globalDescriptor (dataMaps tiles) initial rf co histories dataCluster observation ∧
      initial = (fun _ => dataRepresentedInitial a b tiles frame) ∧ ObservedGemm a b tiles frame observation := by
  by_cases hz : tiles = 0
  · subst tiles
    have hw : Unified.WellFormed code (completeLaunch 0 (dataRepresentedInitial a b 0 frame)) zeroCandidate :=
      data_source_well_formed _ _ 0 _ (by decide)
    have hc : Unified.Complete zeroCandidate := data_candidate_local _ _ 0 (by decide)
    have he := completed_zero_execution_components hw hc
    refine ⟨zeroCandidate,_,zeroRf,zeroCo zeroCandidate,zeroHistories,_,?_,he,rfl,?_⟩
    · intro ht
      omega
    · exact execution_refines_gemm (by decide) he rfl
  · have ht : 0 < tiles := by omega
    have he := retry_data_execution_components a b tiles schedules frame ht hb
    refine ⟨retryDataCandidate a b tiles schedules,_,retryDataReadWitness a b tiles schedules,retryDataCoherenceWitness a b tiles schedules,
      retryHistories (retryDataFamily a b tiles schedules),_,?_,he,rfl,execution_refines_gemm hb he rfl⟩
    intro _
    exact ⟨retryDataFamily a b tiles schedules,rfl⟩

theorem execution_matrix_deterministic {a b tiles frame left right leftInitial rightInitial leftRf rightRf leftCo rightCo leftHistories rightHistories leftObservation rightObservation}
    (hb : tiles ≤ 2^28)
    (hl : Unified.ExecutionComponents code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) left
      Tma.localShared Access.globalDescriptor (dataMaps tiles) leftInitial leftRf leftCo leftHistories dataCluster leftObservation)
    (hr : Unified.ExecutionComponents code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) right
      Tma.localShared Access.globalDescriptor (dataMaps tiles) rightInitial rightRf rightCo rightHistories dataCluster rightObservation)
    (hil : leftInitial = fun _ => dataRepresentedInitial a b tiles frame)
    (hir : rightInitial = fun _ => dataRepresentedInitial a b tiles frame)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    leftObservation.output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      rightObservation.output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) :=
  ((execution_refines_gemm hb hl hil).1 lane slot index).trans ((execution_refines_gemm hb hr hir).1 lane slot index).symm

end
end Ptx.Kernels.HopperDoubleBuffer
