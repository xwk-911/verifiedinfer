import Ptx.Kernels.HopperStageNativeInventory
import Ptx.Kernels.HopperStageMemoryRank

/-! Independent acyclicity for the source/CTA/TMA/resource/native control
graph. Native arrivals and source returns are separate. This admits no new
byte-level visibility and does not close allocation or arbitrary-source proofs.
-/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def nativeControlRank : Unified.ControlNode → Nat
  | .base node => 2*controlRank node
  | .arrival id => 2*sourceControlRank id-1
  | .operand _ _ => 630
theorem native_sync_equal_ranks {a b left right} (hs : Unified.NativeSync block (candidate a b) left right) :
    sourceControlRank left = sourceControlRank right := by
  obtain ⟨_,signature,hl,hr⟩ := hs
  rw [rich_native_source_rank hl,rich_native_source_rank hr]
theorem native_arrival_rank {a b left right}
    (he : Unified.NativeArrival (candidate a b) left right) : nativeControlRank left < nativeControlRank right := by
  cases left with
  | base node =>
    cases node <;> cases right <;> try exact False.elim he
    rename_i before event
    have hr := actual_control_edge_rank (left := .source before) (right := .source event) (.inl he.1)
    change 2*sourceControlRank before < 2*sourceControlRank event-1
    change sourceControlRank before < sourceControlRank event at hr
    omega
  | arrival _ | operand _ _ => exact False.elim he
theorem native_rendezvous_rank {a b left right}
    (he : Unified.NativeRendezvous block (candidate a b) left right) : nativeControlRank left < nativeControlRank right := by
  cases left <;> cases right <;> try exact False.elim he
  rename_i event node
  cases node <;> try exact False.elim he
  have heq := native_sync_equal_ranks he
  obtain ⟨_,signature,hl,_⟩ := he
  have hr := rich_native_source_rank hl
  change 2*sourceControlRank _-1 < 2*sourceControlRank _
  omega
theorem native_issue_rank {a b left right}
    (he : Unified.NativeIssue (candidate a b) left right) : nativeControlRank left < nativeControlRank right := by
  cases left with
  | base node =>
    cases node <;> cases right <;> try exact False.elim he
    rename_i event issue operand
    obtain ⟨rfl,hp⟩ := he
    obtain ⟨pair,hpair⟩ := Option.isSome_iff_exists.mp hp
    have hevent := (Unified.representative_at hpair).1
    have hr := actual_mma_source_rank hevent
    change 2*sourceControlRank event < 630
    rw [hr]
    decide
  | arrival _ | operand _ _ => exact False.elim he
theorem native_finish_rank {a b left right}
    (he : Unified.NativeFinish (candidate a b) left right) : nativeControlRank left < nativeControlRank right := by
  cases left <;> cases right <;> try exact False.elim he
  rename_i issue operand node
  cases node <;> try exact False.elim he
  obtain ⟨mark,groups,keep,before,after,query,hw,_⟩ := Unified.completed_has_actual_wait he
  change 630 < 2*sourceControlRank _
  rw [actual_wait_source_rank hw]
  decide
theorem native_control_edge_rank {a b left right}
    (he : Unified.ControlEdge block (candidate a b) histories left right) : nativeControlRank left < nativeControlRank right := by
  rcases he with hb | ha | hr | hi | hf
  · cases left <;> cases right <;> try exact False.elim hb
    have hh := actual_control_edge_rank hb
    change 2*controlRank _ < 2*controlRank _
    omega
  · exact native_arrival_rank ha
  · exact native_rendezvous_rank hr
  · exact native_issue_rank hi
  · exact native_finish_rank hf
theorem stage_native_control_acyclic (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    Unified.ControlAcyclic block (candidate a b) histories :=
  Unified.control_acyclic_of_rank nativeControlRank (fun _ _ => native_control_edge_rank)
theorem stage_native_control_admitted (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    Unified.ControlAdmitted block (candidate a b) histories :=
  ⟨stage_schedules_admitted a b,stage_native_control_acyclic a b⟩

end
end Ptx.Kernels.HopperStage
