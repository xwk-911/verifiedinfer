import Ptx.Kernels.HopperDoubleBufferZeroExecution

/-! Universal zero-K checks instantiated with arbitrary oracles and reversed
trace order. Duplicate traces preserve lookup but invalidate inventory counts;
resource exhaustiveness is not inferred from lookup equality alone. -/
namespace Ptx.HopperZeroExecutionTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def trace (replies : Wgmma.Lane → Wgmma.Oracle) (lane : Wgmma.Lane) : Unified.ThreadTrace :=
  {completeTrace 0 lane with oracle := replies lane}
def reversed (replies : Wgmma.Lane → Wgmma.Oracle) : Unified.Candidate := ⟨(List.ofFn (trace replies)).reverse⟩

theorem source (replies : Wgmma.Lane → Wgmma.Oracle) (initial : Location → Symbolic.Byte) :
    Unified.WellFormed code (completeLaunch 0 initial) (reversed replies) := by
  refine ⟨(complete_source_well_formed 0 initial (by decide)).1,?_,?_,?_⟩
  · have hn : (List.ofFn (fun lane : Wgmma.Lane => (HopperStage.ctx lane).id)).Nodup := by decide
    have hr : (List.ofFn (fun lane : Wgmma.Lane => (HopperStage.ctx lane).id)).reverse.Nodup := by simpa only [List.nodup_reverse] using hn
    simpa only [reversed,List.map_reverse,List.map_ofFn,Function.comp_def,trace,completeTrace,ctx] using hr
  · intro actual ht
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp ht)
    exact ⟨HopperStage.ctx_valid lane,zero_complete_any_reply lane (replies lane)⟩
  · intro id hi
    obtain ⟨lane,hid⟩ := HopperStage.ctx_covered hi
    exact ⟨trace replies lane,List.mem_reverse.mpr (List.mem_ofFn.mpr ⟨lane,rfl⟩),hid⟩

theorem complete (replies : Wgmma.Lane → Wgmma.Oracle) : Unified.Complete (reversed replies) := by
  intro actual ht
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp ht)
  exact complete_source_status 0 lane (by decide)

theorem reversed_first_lane (replies : Wgmma.Lane → Wgmma.Oracle) :
    ((reversed replies).traces.head?).map Unified.ThreadTrace.id = some (ctx 0 127).id := rfl

theorem actual_lookup_correspondence (replies : Wgmma.Lane → Wgmma.Oracle) :
    (reversed replies).eventAt = zeroCandidate.eventAt :=
  completed_zero_event_lookup (source replies (fun _ => .bits (byte 17))) (complete replies)

theorem actual_event_id_permutation (replies : Wgmma.Lane → Wgmma.Oracle) :
    (reversed replies).view.eventIds.Perm zeroCandidate.view.eventIds :=
  completed_zero_event_ids_perm (source replies (fun _ => .bits (byte 17))) (complete replies)

theorem positive_joint_components (replies : Wgmma.Lane → Wgmma.Oracle) (initial : Location → Symbolic.Byte) :
    Unified.TmaComponents code (completeLaunch 0 initial) (reversed replies) Tma.localShared (dataMaps 0) zeroHistories ∧
    Unified.ControlAdmitted HopperStage.block (reversed replies) zeroHistories ∧
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (reversed replies) (fun _ => initial) zeroRf (zeroCo (reversed replies)) zeroHistories dataCluster ∧
    (∀ id, (reversed replies).representativeAt id = none) ∧
    Unified.ObserverConditions Tma.localShared Access.globalDescriptor (reversed replies) (fun _ => initial) zeroRf (zeroCo (reversed replies)) zeroHistories dataCluster (zeroObservation (reversed replies) initial) :=
  completed_zero_components (source replies initial) (complete replies)

theorem observed_zero_matrix (replies : Wgmma.Lane → Wgmma.Oracle) (initial : Location → Symbolic.Byte)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    (zeroObservation (reversed replies) initial).output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = .realPart .f32 0 index.val :=
  completed_zero_observed_output (source replies initial) (complete replies)
    (completed_zero_observer_witness (source replies initial) (complete replies)) lane slot index

theorem arbitrary_admitted_history_output (replies : Wgmma.Lane → Wgmma.Oracle) (initial : Location → Symbolic.Byte)
    (proxyInitial : Unified.ProxyMemory) (rf : Unified.ReadsFrom) (co : Location → Option Unified.Node → Option Unified.Node → Prop)
    (histories : Location → List Tma.Entry) (cluster : Unified.ClusterScope) (obs : Unified.Observation)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (reversed replies) proxyInitial rf co histories cluster)
    (ho : Unified.ObserverConditions Tma.localShared Access.globalDescriptor (reversed replies) proxyInitial rf co histories cluster obs)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    obs.output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = .realPart .f32 0 index.val :=
  completed_zero_observed_output_of_admission (source replies initial) (complete replies) hm.toCausalConstraints ho lane slot index

theorem adjacent_frame_preserved (replies : Wgmma.Lane → Wgmma.Oracle) (initial : Location → Symbolic.Byte) :
    (zeroObservation (reversed replies) initial).output ⟨.global,8191⟩ = initial ⟨.global,8191⟩ ∧
    (zeroObservation (reversed replies) initial).output ⟨.global,10240⟩ = initial ⟨.global,10240⟩ := by
  have ho := completed_zero_observer_witness (source replies initial) (complete replies)
  constructor
  · exact completed_zero_observed_frame (source replies initial) (complete replies) ho
      (mem_data_output_domain.mpr ⟨rfl,by decide,by decide⟩) rfl (by decide)
  · exact completed_zero_observed_frame (source replies initial) (complete replies) ho
      (mem_data_output_domain.mpr ⟨rfl,by decide,by decide⟩) rfl (by decide)

def duplicate : Unified.Candidate := ⟨dataCompleteTrace (fun _ _ => 0) (fun _ _ => 0) 0 0 :: zeroCandidate.traces⟩

theorem duplicate_lookup_same : duplicate.eventAt = zeroCandidate.eventAt := by
  let first := dataCompleteTrace (fun _ _ => 0) (fun _ _ => 0) 0 0
  have hn : (zeroCandidate.traces.map Unified.ThreadTrace.id).Nodup :=
    (data_source_well_formed (fun _ _ => 0) (fun _ _ => 0) 0 (fun _ => .bits (byte 0)) (by decide)).2.1
  have hm : first ∈ zeroCandidate.traces := List.mem_ofFn.mpr ⟨0,rfl⟩
  funext id
  change (((first::zeroCandidate.traces).find? (fun t => t.id == id.thread)).bind (fun t => t.events[id.serial]?)) = _
  rw [List.find?_cons]
  split
  · rename_i he
    have hid : first.id = id.thread := by simpa only [beq_iff_eq] using he
    have ht : zeroCandidate.traceAt id.thread = some first := by rw [← hid]; exact Unified.traceAt_of_member hn hm
    change first.events[id.serial]? = (zeroCandidate.traceAt id.thread).bind _
    rw [ht]
    rfl
  · rfl

theorem duplicate_inventory_counts :
    (Tma.inventory Tma.localShared duplicate.view ⟨.shared .zero,0⟩).length = 4 ∧ (zeroHistories ⟨.shared .zero,0⟩).length = 2 := by decide

theorem duplicate_history_rejected : ¬Tma.HistoryValid Tma.localShared duplicate.view ⟨.shared .zero,0⟩ (zeroHistories ⟨.shared .zero,0⟩) := by
  intro hh
  have he := hh.exhaustive.length_eq
  rw [duplicate_inventory_counts.1,duplicate_inventory_counts.2] at he
  omega

theorem duplicate_source_rejected : ¬Unified.WellFormed code (completeLaunch 0 (fun _ => .bits (byte 0))) duplicate := by
  intro hw
  have hn := hw.2.1
  change ((_::zeroCandidate.traces).map Unified.ThreadTrace.id).Nodup at hn
  simp only [List.map_cons,List.nodup_cons] at hn
  exact hn.1 (List.mem_map.mpr ⟨_,List.mem_ofFn.mpr ⟨0,rfl⟩,rfl⟩)

theorem invented_notification_rejected (replies : Wgmma.Lane → Wgmma.Oracle) (loc : Location) (id : Tma.CopyId) (op : BarrierOp) :
    Tma.Entry.mk (.notification id) op ∉ zeroHistories loc :=
  Tma.no_ghost_notification (completed_zero_history_valid (source replies (fun _ => .bits (byte 0))) (complete replies) loc)
    (completed_zero_no_tma (source replies (fun _ => .bits (byte 0))) (complete replies) id) op

def omitted (replies : Wgmma.Lane → Wgmma.Oracle) (initial : Location → Symbolic.Byte) : Unified.Observation :=
  {zeroObservation (reversed replies) initial with domain := []}
def stale (replies : Wgmma.Lane → Wgmma.Oracle) (initial : Location → Symbolic.Byte) : Unified.Observation :=
  {zeroObservation (reversed replies) initial with source := fun _ => none,output := initial}

theorem omitted_output_rejected (replies : Wgmma.Lane → Wgmma.Oracle) (initial : Location → Symbolic.Byte) :
    ¬Unified.ObserverConditions Tma.localShared Access.globalDescriptor (reversed replies) (fun _ => initial) zeroRf (zeroCo (reversed replies)) zeroHistories dataCluster (omitted replies initial) := by
  intro ho
  have hh := ho.coverage _ _ _ rfl (completed_zero_output_byte (source replies initial) (complete replies) 0 0 0)
  cases hh

theorem stale_output_rejected (replies : Wgmma.Lane → Wgmma.Oracle) (initial : Location → Symbolic.Byte) :
    ¬Unified.ObserverConditions Tma.localShared Access.globalDescriptor (reversed replies) (fun _ => initial) zeroRf (zeroCo (reversed replies)) zeroHistories dataCluster (stale replies initial) := by
  intro ho
  have hw := source replies initial
  have hc := complete replies
  have hwrite := completed_zero_output_byte hw hc 0 0 0
  have hh := ho.noStale _ (ho.coverage _ _ _ rfl hwrite) (candidate_no_mixed_size_race (by decide) hw hc (completed_zero_descriptors hw hc)) _ _ hwrite
  exact hh ((completed_zero_coherent hw hc).initialization _ _ _ hwrite)

end
end Ptx.HopperZeroExecutionTests
