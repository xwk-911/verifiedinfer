import Ptx.Kernels.HopperStageNativeEligibility
import Ptx.Kernels.HopperStageNativeRankData

/-! Independent rank for the actual unified byte order. A rank proves an
individual witness acyclic; it is never added to allowed-execution premises.
Control order is used only to bound already justified memory edges. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def memoryRank : Unified.Node → Nat
  | .base (.tma node) => controlRank node
  | .base (.copyRead _) | .base (.copyWrite _) => 0
  | .wgmmaRead _ _ => 315
theorem actual_control_edge_rank {a b left right}
    (he : Tma.ControlEdge (candidate a b).view histories left right) : controlRank left < controlRank right := by
  have hm := (Tma.ResourceErasure.control_edge_preserved (candidate a b).view histories left right).mpr he
  rw [candidate_resource_erasure] at hm
  rcases hm with hp | hc | hi | hr
  · exact control_program_order hp
  · exact control_cta_order hc
  · exact control_internal_order hi
  · exact control_resource_order hr
theorem actual_control_path_rank {a b left right}
    (he : Ptx.Event.Path (Tma.ControlEdge (candidate a b).view histories) left right) : controlRank left < controlRank right :=
  he.rank_lt controlRank (fun _ _ => actual_control_edge_rank)
theorem generic_after_rank {a b left right} (he : Access.GenericAfter (candidate a b).view left right) :
    sourceControlRank left < sourceControlRank right := actual_control_path_rank (Access.generic_after_control he)
theorem actual_mma_source_rank {a b id mark call} (he : (candidate a b).eventAt id = some (.mma mark call)) : sourceControlRank id = 310 := by
  have hv : resourceCandidate.eventAt id = some (.wgmma .mma) := by
    rw [← candidate_resource_erasure a b,Tma.ResourceErasure.eventAt_preserved,Unified.view_eventAt,he]
    rfl
  exact native_source_tag_ranks id (Hopper.present_mem_eventIds (by simp only [Hopper.Candidate.Present,hv,Option.isSome_some]))
    310 (by simp only [hv,Option.bind_some,nativeRankTag,Option.toList_some,List.mem_singleton])
theorem actual_wait_source_rank {a b id mark groups keep before after query}
    (he : (candidate a b).eventAt id = some (.wait mark groups keep before after query)) : sourceControlRank id = 330 := by
  have hv : resourceCandidate.eventAt id = some (.wgmma .wait) := by
    rw [← candidate_resource_erasure a b,Tma.ResourceErasure.eventAt_preserved,Unified.view_eventAt,he]
    rfl
  exact native_source_tag_ranks id (Hopper.present_mem_eventIds (by simp only [Hopper.Candidate.Present,hv,Option.isSome_some]))
    330 (by simp only [hv,Option.bind_some,nativeRankTag,Option.toList_some,List.mem_singleton])
theorem write_location_present {a b id offset loc}
    (hl : Tma.writeLocation Tma.localShared (candidate a b).view id offset = some loc) : Tma.WritePresent (candidate a b).view id offset := by
  cases hc : Tma.copyAt (candidate a b).view id with
  | none => simp [Tma.writeLocation,hc] at hl
  | some op =>
    simp only [Tma.writeLocation,hc,Option.bind_some] at hl
    unfold Tma.WritePresent
    rw [hc]
    split at hl
    · assumption
    · cases hl
theorem protected_control_path {a b event id offset loc}
    (h : Access.Protected Tma.localShared (candidate a b).view (.tma (.source event)) (.tma (.write id offset)) loc) :
    Ptx.Event.Path (Tma.ControlEdge (candidate a b).view histories) (.source event) (.write id offset) := by
  obtain ⟨fence,_,hp,hq,hl,_⟩ := h
  have hw := write_location_present hl
  obtain ⟨op,hc,_⟩ := Tma.write_has_copy hw
  exact .trans (.single (.inl (show Tma.ProgramOrder _ (.source event) (.source fence) from hp))) (.trans (.single (.inl (show Tma.ProgramOrder _ (.source fence) (.source id.issue) from hq)))
    (.trans (.single (.inr (.inr (.inl (.issue (by rw [hc]; rfl)))))) (.single (.inr (.inr (.inl (.descriptorWrite hw)))))))
theorem base_byte_edge_rank {a b loc left right}
    (h : Access.ByteEdge Tma.localShared Access.globalDescriptor (candidate a b).view histories cluster loc left right) :
    memoryRank (.base left) < memoryRank (.base right) := by
  rcases h with hg | hi | hc | ht | hp | hf
  · cases left with
    | tma left =>
      cases left <;> cases right <;> try exact False.elim hg
      rename_i left right
      cases right <;> try exact False.elim hg
      exact actual_control_edge_rank (left := .source _) (right := .source _)
        (hg.elim (fun h => .inl h) (fun h => .inr (.inl h)))
    | copyRead _ | copyWrite _ => exact False.elim hg
  · cases left <;> cases right <;> simp [Access.NonbulkInternal,no_nonbulk] at hi
  · cases left <;> cases right <;> simp only [Access.NonbulkCompleted] at hc
    rename_i issue node
    cases node <;> simp_all [no_nonbulk]
  · cases left <;> cases right <;> simp only [Access.TensorInternal] at ht
    rename_i left right
    cases left <;> cases right <;> simp only [Access.TensorInternal] at ht
    rcases ht with ⟨rfl,rfl,hr⟩
    exact actual_control_edge_rank (.inr (.inr (.inl (.data hr))))
  · cases left <;> cases right <;> simp only [Access.Published] at hp
    rename_i left right
    cases left <;> cases right <;> simp only [Access.Published] at hp
    exact actual_control_path_rank (Access.published_control_path hp)
  · cases left <;> cases right <;> simp only [Access.Protected] at hf
    rename_i left right
    cases left <;> cases right <;> simp only [Access.Protected] at hf
    exact actual_control_path_rank (protected_control_path hf)
theorem native_publication_rank {a b loc left right}
    (h : Unified.NativePublished Tma.localShared (candidate a b) histories cluster loc left right) : memoryRank left < memoryRank right := by
  cases left <;> cases right <;> simp only [Unified.NativePublished] at h
  rename_i left issue operand
  cases left <;> try exact False.elim h
  rename_i node
  cases node <;> try exact False.elim h
  · obtain ⟨collective,_,_,all⟩ := h
    obtain ⟨fence,_,_,ha,hb⟩ := all 0
    have hr := (generic_after_rank ha).trans (generic_after_rank hb)
    rw [actual_mma_source_rank (collective.matched 0)] at hr
    change sourceControlRank _ < 315
    omega
  · obtain ⟨collective,hl,_,all⟩ := h
    obtain ⟨wait,ho,ha⟩ := all 0
    have hw := write_location_present hl
    have path : Ptx.Event.Path (Tma.ControlEdge (candidate a b).view histories) (.write _ _) (.source (collective.sources 0)) :=
      .trans (.single (.inr (.inr (.inl (.complete hw)))))
        (.trans (.single (.inr (.inr (.inr (Access.observed_resource_edge ho))))) (Access.generic_after_control ha))
    have hr := actual_control_path_rank path
    change controlRank _ < sourceControlRank (collective.sources 0) at hr
    rw [actual_mma_source_rank (collective.matched 0)] at hr
    exact hr.trans (by change 310 < 315; decide)
theorem native_completion_rank {a b loc left right}
    (h : Unified.NativeCompleted (candidate a b) loc left right) : memoryRank left < memoryRank right := by
  cases left <;> cases right <;> try exact False.elim h
  rename_i issue operand right
  cases right <;> try exact False.elim h
  rename_i node
  cases node <;> try exact False.elim h
  obtain ⟨mark,groups,keep,before,after,query,he,_⟩ := Unified.completed_has_actual_wait h.1
  change 315 < sourceControlRank _
  rw [actual_wait_source_rank he]
  decide
theorem native_reuse_impossible {a b loc left right}
    (h : Unified.NativeReuse Tma.localShared (candidate a b) loc left right) : False := by
  cases left <;> cases right <;> try exact False.elim h
  rename_i issue operand right
  cases right <;> try exact False.elim h
  rename_i node
  cases node <;> try exact False.elim h
  obtain ⟨wait,hc,ha,hl,_⟩ := h
  obtain ⟨mark,groups,keep,before,after,query,he,_⟩ := Unified.completed_has_actual_wait hc
  have hr := generic_after_rank ha
  rw [actual_wait_source_rank he] at hr
  rcases tensor_write_id_cases hl with rfl | rfl <;> norm_num [sourceControlRank,copyId,ctx,tid,block,Dim3.linear] at hr
theorem memory_byte_edge_rank {a b loc left right}
    (h : Unified.ByteEdge Tma.localShared Access.globalDescriptor (candidate a b) histories cluster loc left right) : memoryRank left < memoryRank right := by
  rcases h with hb | hp | hc | hr
  · cases left <;> cases right <;> try exact False.elim hb
    exact base_byte_edge_rank hb
  · exact native_publication_rank hp
  · exact native_completion_rank hc
  · exact (native_reuse_impossible hr).elim
theorem memory_byte_order_rank {a b loc left right}
    (h : Unified.ByteOrder Tma.localShared Access.globalDescriptor (candidate a b) histories cluster loc left right) : memoryRank left < memoryRank right :=
  h.rank_lt memoryRank (fun _ _ => memory_byte_edge_rank)
theorem memory_base_acyclic (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    ∀ loc node, ¬Unified.ByteOrder Tma.localShared Access.globalDescriptor (candidate a b) histories cluster loc node node := by
  intro loc node h
  have hh := memory_byte_order_rank h
  omega

end
end Ptx.Kernels.HopperStage
