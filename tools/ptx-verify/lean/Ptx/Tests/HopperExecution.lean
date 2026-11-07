import Ptx.Kernels.HopperDoubleBufferExecution
import Ptx.Tests.HopperArbitraryOutput
import Ptx.Tests.WgmmaProtocol
import Ptx.Tests.WgmmaTensor

/-! Unified correctness/nonvacuity, distinct retry executions and component
counterexamples. The orphan and bad-collective fixtures test tensor admission
alone; they are not claimed to be fully source/control-admitted PTX executions. -/
namespace Ptx.HopperExecutionTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev schedule := HopperArbitraryOutputTests.schedule
abbrev frame := HopperArbitraryOutputTests.frame
abbrev family := HopperArbitraryOutputTests.family
abbrev candidate := HopperArbitraryOutputTests.candidate
abbrev observation := HopperArbitraryOutputTests.observation
def noRetries : Wgmma.Lane → Nat → Nat := fun _ _ => 0

theorem positive_gemm_refinement (a b) : ObservedGemm a b 3 frame (observation a b) :=
  execution_refines_gemm (by decide) (retry_data_execution_components a b 3 schedule frame (by decide) (by decide)) rfl

theorem zero_gemm_has_full_execution (a b) (initialFrame : Location → Symbolic.Byte) :
    ∃ c initial rf co histories obs,
      Unified.ExecutionComponents code (completeLaunch 0 (dataRepresentedInitial a b 0 initialFrame)) c Tma.localShared Access.globalDescriptor
        (dataMaps 0) initial rf co histories dataCluster obs ∧
      initial = (fun _ => dataRepresentedInitial a b 0 initialFrame) ∧
      ∀ lane slot (index : Fin 4), obs.output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = .realPart .f32 0 index.val := by
  obtain ⟨c,initial,rf,co,histories,obs,_,he,hi,hpost⟩ := gemm_execution_exists a b 0 schedule initialFrame (by decide)
  refine ⟨c,initial,rf,co,histories,obs,he,hi,?_⟩
  simpa only [specification,Finset.range_zero,Finset.sum_empty] using hpost.1

theorem positive_execution_keeps_schedule (a b) :
    ∃ c initial rf co histories obs, (∃ family : ReplySourceFamily 3 c, family.schedules = schedule) ∧
      Unified.ExecutionComponents code (completeLaunch 3 (dataRepresentedInitial a b 3 frame)) c Tma.localShared Access.globalDescriptor
        (dataMaps 3) initial rf co histories dataCluster obs ∧ ObservedGemm a b 3 frame obs := by
  obtain ⟨c,initial,rf,co,histories,obs,hs,he,_,hpost⟩ := gemm_execution_exists a b 3 schedule frame (by decide)
  exact ⟨c,initial,rf,co,histories,obs,hs (by decide),he,hpost⟩

theorem schedules_are_distinct : schedule 0 0 = 1 ∧ noRetries 0 0 = 0 := by decide

theorem different_retry_schedules_same_matrix (a b) (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    (retryDataObservation a b 3 schedule frame).output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      (retryDataObservation a b 3 noRetries frame).output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) :=
  execution_matrix_deterministic (by decide)
    (retry_data_execution_components a b 3 schedule frame (by decide) (by decide))
    (retry_data_execution_components a b 3 noRetries frame (by decide) (by decide)) rfl rfl lane slot index

theorem positive_nonzero_result (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    (observation (fun _ _ => 1) (fun _ _ => 2)).output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = .realPart .f32 96 index.val := by
  rw [(positive_gemm_refinement (fun _ _ => 1) (fun _ _ => 2)).1 lane slot index]
  norm_num [specification]

theorem positive_adjacent_frame (a b) :
    (observation a b).output ⟨.global,8191⟩ = .bits (byte 17) ∧ (observation a b).output ⟨.global,10240⟩ = .bits (byte 17) := by
  have hp := (positive_gemm_refinement a b).2
  constructor
  · exact hp ⟨.global,8191⟩ (by change (⟨.global,8191⟩ : Location) ∈ dataOutputDomain; decide) rfl (by decide)
  · exact hp ⟨.global,10240⟩ (by change (⟨.global,10240⟩ : Location) ∈ dataOutputDomain; decide) rfl (by decide)

theorem every_actual_mma_covered (a b) (tile : Fin 3) (lane : Wgmma.Lane) :
    ∃ issue, ∃ collective : Unified.Collective (candidate a b) issue, ∃ member,
      collective.sources member = (family a b).mmaId tile lane := by
  have he := retry_data_execution_components a b 3 schedule frame (by decide) (by decide)
  exact he.tensor.covered _ _ _ (family_mma_at (family a b) he.tma.source tile tile.isLt lane)

theorem mixed_tiles_cannot_form_collective (a b) {issue} (collective : Unified.Collective (candidate a b) issue)
    (hfirst : collective.calls 0 = (family a b).calls 0 0)
    (hlater : collective.calls 1 = (family a b).calls 2 1) : False := by
  have hg := collective.cohort.group 1
  rw [hfirst,hlater] at hg
  change (replyCall 3 1 _ _ 2).group = (replyCall 3 0 _ _ 0).group at hg
  rw [reply_call_group,reply_call_group] at hg
  cases hg

def orphanTrace : Unified.ThreadTrace := {
  id := ⟨.zero,.zero⟩,oracle := WgmmaProtocolTests.oracle,count := 0,final := {},
  events := [.mma ⟨0,0,0⟩ (WgmmaTensorTests.good 0)]
}
def orphanCandidate : Unified.Candidate := ⟨[orphanTrace]⟩

theorem orphan_mma_present : orphanCandidate.eventAt ⟨orphanTrace.id,0⟩ = some (.mma ⟨0,0,0⟩ (WgmmaTensorTests.good 0)) := by rfl

theorem orphan_all_calls_lane_zero {event mark call} (he : orphanCandidate.eventAt event = some (.mma mark call)) : call.lane = 0 := by
  obtain ⟨trace,ht,_,hevent⟩ := Unified.eventAt_trace he
  have htrace : trace = orphanTrace := by simpa only [orphanCandidate,List.mem_singleton] using ht
  subst trace
  have hm := List.mem_of_getElem? hevent
  change Wgmma.Event.mma mark call ∈ [.mma ⟨0,0,0⟩ (WgmmaTensorTests.good 0)] at hm
  simp only [List.mem_singleton] at hm
  rw [(Wgmma.Event.mma.inj hm).2]
  rfl

theorem orphan_tensor_components_rejected : ¬Unified.TensorComponents orphanCandidate := by
  intro htensor
  obtain ⟨issue,collective,_,_⟩ := htensor.covered _ _ _ orphan_mma_present
  have hzero := orphan_all_calls_lane_zero (collective.matched 1)
  have hone := collective.cohort.lane 1
  rw [hzero] at hone
  cases hone

theorem bad_tensor_any_memory (memory : Location → Symbolic.Byte) : ¬Wgmma.TensorConditions .zero WgmmaTensorTests.bad memory := by
  intro htensor
  obtain ⟨a,b,hvalues,hmath⟩ := htensor.tensor
  have hones : Wgmma.InputValues (WgmmaTensorTests.bad 0) WgmmaTensorTests.onesA WgmmaTensorTests.onesB :=
    ⟨Wgmma.payload_a _ _,Wgmma.payload_b _ _⟩
  obtain ⟨ha,hb⟩ := Wgmma.input_values_unique (hvalues 0) hones
  subst a
  subst b
  have hm := hmath (0,0)
  norm_num [WgmmaTensorTests.bad,WgmmaTensorTests.good,Wgmma.tensorCalls,Wgmma.results,Wgmma.gatherC,
    Wgmma.matrixStep,Wgmma.scatterC,WgmmaTensorTests.onesA,WgmmaTensorTests.onesB,WgmmaTensorTests.zeroC] at hm

theorem bad_collective_rejected {c issue} (collective : Unified.Collective c issue)
    (hcta : issue.thread.cta = .zero) (hcalls : collective.calls = WgmmaTensorTests.bad) : ¬Unified.TensorComponents c := by
  intro htensor
  obtain ⟨memory,ht⟩ := htensor.tensor issue collective
  rw [hcta,hcalls] at ht
  exact bad_tensor_any_memory memory ht

theorem corrupted_observer_rejected :
    ¬Unified.ExecutionComponents code (completeLaunch 3 (dataRepresentedInitial (fun _ _ => 1) (fun _ _ => 2) 3 frame))
      (candidate (fun _ _ => 1) (fun _ _ => 2)) Tma.localShared Access.globalDescriptor (dataMaps 3)
      (HopperArbitraryOutputTests.initial (fun _ _ => 1) (fun _ _ => 2))
      (HopperArbitraryOutputTests.rf (fun _ _ => 1) (fun _ _ => 2)) (HopperArbitraryOutputTests.co (fun _ _ => 1) (fun _ _ => 2))
      (retryHistories (family (fun _ _ => 1) (fun _ _ => 2))) dataCluster (HopperArbitraryOutputTests.wrongObservation (fun _ _ => 1) (fun _ _ => 2)) := by
  intro he
  have hv := (execution_refines_gemm (by decide) he rfl).1 0 0 0
  change Symbolic.Byte.realPart .f32 0 0 = .realPart .f32 (specification (fun _ _ => 1) (fun _ _ => 2) 3 (Wgmma.cCoord (0,0))) 0 at hv
  norm_num [specification,Symbolic.Byte.realPart.injEq] at hv

def missingObservation (a : TileA) (b : TileB) : Unified.Observation := {observation a b with domain := []}

theorem missing_output_domain_rejected (a b) :
    ¬Unified.ExecutionComponents code (completeLaunch 3 (dataRepresentedInitial a b 3 frame)) (candidate a b)
      Tma.localShared Access.globalDescriptor (dataMaps 3) (HopperArbitraryOutputTests.initial a b)
      (HopperArbitraryOutputTests.rf a b) (HopperArbitraryOutputTests.co a b) (retryHistories (family a b)) dataCluster (missingObservation a b) := by
  intro he
  have hw := retry_actual_output_byte (family a b) he.tma.source 0 0 0
  have hc := he.observer.coverage _ _ _ rfl hw
  change _ ∈ ([] : List Location) at hc
  exact List.not_mem_nil hc

end
end Ptx.HopperExecutionTests
