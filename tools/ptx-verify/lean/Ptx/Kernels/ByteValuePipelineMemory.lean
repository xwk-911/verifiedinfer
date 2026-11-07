import Ptx.Kernels.ByteValuePipelineMemoryOrder

/-! A full existing-model memory witness for the generated source. Coherence,
causal freshness/future, both atomicity fields and SC-per-location are proved;
no memory condition is replaced by an assumed rank or desired load result.
-/
namespace Ptx.Kernels.ByteValuePipeline
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

def proxyInitial : Unified.ProxyMemory := fun _ => initial
def cluster : Unified.ClusterScope := fun _ _ => False
def coherence (value reply : Nat) := Unified.InitialCo Tma.localShared Access.globalDescriptor (candidate value reply)

theorem witness_read_agreement (value : Nat) (initialProxy : Unified.ProxyMemory) (scope : Unified.ClusterScope) :
    Unified.ReadAgreement Tma.localShared Access.globalDescriptor (candidate value value) initialProxy
      (Unified.Eligible Tma.localShared Access.globalDescriptor (candidate value value) (fun _ => []) scope readWitness) readWitness := by
  intro read loc byteValue _ hr
  have he := reader_only hr
  subst read
  change ByteContents.writeByte (candidate value value) writerMemory loc = some byteValue
  exact (written_and_read_payloads_match value loc).symm.trans hr

theorem witness_causal_conditions (value : Nat) (initialProxy : Unified.ProxyMemory) (scope : Unified.ClusterScope) :
    Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate value value) initialProxy readWitness (coherence value value) (fun _ => []) scope := by
  refine ⟨witness_read_agreement value initialProxy scope,?_,?_,?_⟩
  · intro _ writer loc byteValue hw
    exact ⟨rfl,writer,rfl,by rw [Unified.WritesAt,hw]; rfl⟩
  · intro _ writer read loc vw vr hw hr hc hco
    have he : (some writerMemory : Option Unified.Node) = none := hco.1
    cases he
  · intro _ read writer loc vr vw hr hw hc
    have he := writer_only hw
    subst writer
    exact (no_causality_to_writer hc).elim

theorem witness_coherent (value : Nat) (scope : Unified.ClusterScope) :
    Unified.Coherent Tma.localShared Access.globalDescriptor (candidate value value) (fun _ => []) scope readWitness (coherence value value) := by
  apply Unified.unique_initial_coherent
  · intro loc a b va vb ha hb
    exact (writer_only ha).trans (writer_only hb).symm
  · intro loc writer byteValue hw hc
    have he := writer_only hw
    subst writer
    exact no_causality_to_writer hc

theorem witness_single_copy_atomicity (value : Nat) :
    Unified.SingleCopyAtomicity Tma.localShared Access.globalDescriptor (candidate value value) readWitness (coherence value value) := by
  intro read writer hs loc vr vw hr hw hf other vr' vw' hr' hw' hco
  have he : (some writerMemory : Option Unified.Node) = none := hco.1
  cases he

theorem witness_rmw_atomicity (value : Nat) :
    Unified.RMWAtomicity Tma.localShared Access.globalDescriptor (candidate value value) readWitness (coherence value value) := by
  intro atomic writer hm hs loc vr vw hr hw hco
  have he : (some writerMemory : Option Unified.Node) = none := hco.1
  cases he

theorem program_order_rank {value reply left right}
    (hp : Unified.ProgramOrder (candidate value reply) left right) : memoryRank left < memoryRank right := by
  have he : Unified.ControlEdge .one (candidate value reply) (fun _ => []) (Unified.memoryControlNode left) (Unified.memoryControlNode right) :=
    Unified.program_order_control_edge hp
  exact control_edge_rank he

theorem communication_shape {value reply left right}
    (hc : Unified.Communication Tma.localShared Access.globalDescriptor (candidate value reply) readWitness (coherence value reply) left right) :
    left = writerMemory ∧ right = readerMemory := by
  rcases hc with ⟨loc,byteValue,hr,hf,_⟩ | ⟨loc,hco⟩ | ⟨_,loc,byteValue,hr,hco⟩
  · exact ⟨(Option.some.inj hf).symm,reader_only hr⟩
  · have he : (some left : Option Unified.Node) = none := hco.1
    cases he
  · have he : (some writerMemory : Option Unified.Node) = none := hco.1
    cases he

theorem communication_rank {value reply left right}
    (hc : Unified.Communication Tma.localShared Access.globalDescriptor (candidate value reply) readWitness (coherence value reply) left right) :
    memoryRank left < memoryRank right := by
  obtain ⟨rfl,rfl⟩ := communication_shape hc
  decide

theorem witness_sc_per_location (value : Nat) :
    Unified.SCPerLocation Tma.localShared Access.globalDescriptor (candidate value value) readWitness (coherence value value) := by
  intro members hPresent hStrong node hn hp
  have hr := hp.rank_lt memoryRank (fun left right h => h.2.2.elim program_order_rank communication_rank)
  exact Nat.lt_irrefl _ hr

theorem full_memory_witness (value : Nat) (initialProxy : Unified.ProxyMemory) (scope : Unified.ClusterScope) :
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate value value) initialProxy readWitness (coherence value value) (fun _ => []) scope := {
  toCausalConstraints := witness_causal_conditions value initialProxy scope
  baseAcyclic := fun _ _ hp => Nat.lt_irrefl _ (byte_order_rank hp)
  coherence := fun _ => witness_coherent value scope
  atomicity := fun _ => witness_single_copy_atomicity value
  rmwAtomicity := fun _ => witness_rmw_atomicity value
  scPerLocation := fun _ => witness_sc_per_location value
}

theorem ordinary_tma_components (value reply : Nat) :
    Unified.TmaComponents program (launch value) (candidate value reply) Tma.localShared (fun _ => none) (fun _ => []) := by
  refine ⟨source_well_formed value reply,source_complete value reply,?_,?_,empty_histories_valid value reply,?_⟩
  · intro id op hc
    rw [no_tma_copy] at hc
    cases hc
  · intro id op hc
    rw [no_tma_copy] at hc
    cases hc
  · intro node hp
    exact (control_admitted value reply).2 (.base node) (Unified.base_control_path hp)

theorem actual_joint_components (value : Nat) :
    Unified.TmaComponents program (launch value) (candidate value value) Tma.localShared (fun _ => none) (fun _ => []) ∧
    Unified.ControlAdmitted .one (candidate value value) (fun _ => []) ∧
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate value value) proxyInitial readWitness (coherence value value) (fun _ => []) cluster :=
  ⟨ordinary_tma_components value value,control_admitted value value,full_memory_witness value proxyInitial cluster⟩

end
end Ptx.Kernels.ByteValuePipeline
