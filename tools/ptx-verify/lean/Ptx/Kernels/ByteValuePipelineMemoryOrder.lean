import Ptx.Kernels.ByteValuePipelineCorrect

/-! Source-derived control/byte ranks and race eligibility for the real
ordinary store/load source. The rank is a proof device, not an execution-order
assumption added to PTX admission. Arbitrary load replies are retained here.
-/
namespace Ptx.Kernels.ByteValuePipeline
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

def controlRank (node : Unified.ControlNode) : Nat := if node = readerControl then 1 else 0
def memoryRank (node : Unified.Node) : Nat := controlRank (Unified.memoryControlNode node)

theorem empty_histories_valid (value reply : Nat) (loc : Location) :
    Tma.HistoryValid Tma.localShared (candidate value reply).view loc [] := by
  refine ⟨by simp,?_,?_,?_⟩
  · change List.Perm [] []
    exact List.Perm.refl _
  · intro a ha
    cases ha
  · exact ⟨none,rfl⟩

theorem no_native_signature (value reply : Nat) (id : Ptx.Event.EventId) : (candidate value reply).nativeSignatureAt id = none := by
  unfold Unified.Candidate.nativeSignatureAt
  cases he : (candidate value reply).eventAt id with
  | none => rfl
  | some event =>
    rcases source_event_shape he with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> rfl

theorem present_control_shape {value reply node} (hp : Present (candidate value reply) node) : node = writerControl ∨ node = readerControl := by
  cases node with
  | base node =>
    cases node with
    | source id =>
      change ((candidate value reply).view.eventAt id).isSome = true at hp
      rw [Unified.view_eventAt,Option.isSome_map] at hp
      obtain ⟨event,he⟩ := Option.isSome_iff_exists.mp hp
      rcases source_event_shape he with ⟨rfl,_⟩ | ⟨rfl,_⟩
      · exact .inl rfl
      · exact .inr rfl
    | descriptor id | notify id => simp [Present,Tma.Present,no_tma_copy] at hp
    | read id offset => simp [Present,Tma.Present,Tma.readLocation,no_tma_copy] at hp
    | write id offset => simp [Present,Tma.Present,Tma.WritePresent,no_tma_copy] at hp
  | arrival id => simp [Present,no_native_signature] at hp
  | operand issue operand => simp [Present,no_native_representative] at hp

theorem control_edge_shape {value reply left right}
    (he : Unified.ControlEdge .one (candidate value reply) (fun _ => []) left right) : left = writerControl ∧ right = readerControl := by
  have hp := (control_edge_present (empty_histories_valid value reply) he).2
  rcases present_control_shape hp with rfl | rfl
  · exact ((writer_ready value reply).2.2 left he).elim
  · exact ⟨reader_predecessor he,rfl⟩

theorem control_edge_rank {value reply left right}
    (he : Unified.ControlEdge .one (candidate value reply) (fun _ => []) left right) : controlRank left < controlRank right := by
  obtain ⟨rfl,rfl⟩ := control_edge_shape he
  decide

theorem control_admitted (value reply : Nat) : Unified.ControlAdmitted .one (candidate value reply) (fun _ => []) :=
  ⟨by rfl,Unified.control_acyclic_of_rank controlRank (fun _ _ => control_edge_rank)⟩

theorem byte_order_rank {value reply cluster loc left right}
    (hp : Unified.ByteOrder Tma.localShared Access.globalDescriptor (candidate value reply) (fun _ => []) cluster loc left right) :
    memoryRank left < memoryRank right :=
  (Unified.byte_order_control_path (no_nonbulk_copy value reply) hp).rank_lt controlRank (fun _ _ => control_edge_rank)

theorem no_byte_order_to_writer {value reply cluster loc before} :
    ¬Unified.ByteOrder Tma.localShared Access.globalDescriptor (candidate value reply) (fun _ => []) cluster loc before writerMemory := by
  intro hp
  have h := byte_order_rank hp
  have hz : memoryRank writerMemory = 0 := by decide
  omega

theorem no_causality_to_writer {value reply cluster rf loc before} :
    ¬Unified.CausalityAt Tma.localShared Access.globalDescriptor (candidate value reply) (fun _ => []) cluster rf loc before writerMemory := by
  rintro (⟨_,_,hp⟩ | ⟨middle,_,_,_,hp⟩) <;> exact no_byte_order_to_writer hp

theorem actual_access_shape {value reply node loc}
    (ha : Unified.Accesses Tma.localShared Access.globalDescriptor (candidate value reply) node loc) : node = writerMemory ∨ node = readerMemory := by
  rcases ha with hr | hw
  · obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp hr
    exact .inr (reader_only hv)
  · obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp hw
    exact .inl (writer_only hv)

theorem actual_accesses_are_strong {value reply left right loc}
    (hl : Unified.Accesses Tma.localShared Access.globalDescriptor (candidate value reply) left loc)
    (hr : Unified.Accesses Tma.localShared Access.globalDescriptor (candidate value reply) right loc) :
    Unified.MorallyStrong Tma.localShared Access.globalDescriptor (candidate value reply) left right := by
  rcases actual_access_shape hl with rfl | rfl <;> rcases actual_access_shape hr with rfl | rfl
  all_goals exact ⟨rfl,Or.inl rfl,(base,4),rfl,rfl⟩

theorem no_data_race {value reply cluster rf loc left right} :
    ¬Unified.DataRaceAt Tma.localShared Access.globalDescriptor (candidate value reply) (fun _ => []) cluster rf loc left right :=
  fun hr => hr.notStrong (actual_accesses_are_strong hr.left hr.right)

theorem every_read_is_eligible (value reply : Nat) (cluster : Unified.ClusterScope) (rf : Unified.ReadsFrom) (node : Unified.Node) (loc : Location) :
    Unified.Eligible Tma.localShared Access.globalDescriptor (candidate value reply) (fun _ => []) cluster rf node loc := by
  constructor
  · rintro ⟨_,_,_,hr,_⟩
    exact no_data_race hr
  · rintro (⟨_,_,hr⟩ | ⟨_,_,_,_,hr⟩) <;> exact no_data_race hr

end
end Ptx.Kernels.ByteValuePipeline
