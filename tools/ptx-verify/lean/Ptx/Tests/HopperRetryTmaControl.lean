import Ptx.Kernels.HopperDoubleBufferRetryResourceControl
import Ptx.Tests.HopperRetryAdmission

/-! Actual implicit TMA and resource control components with heterogeneous
retries. The combined subgraph test explicitly omits CTA/native edges. The
fixture's positive source/resource components remain separate from its known
negative full-memory status and fully admitted execution existence. -/
namespace Ptx.HopperRetryTmaControlTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev family := HopperRetryAdmissionTests.family
abbrev candidate := HopperRetryAdmissionTests.candidate
abbrev source := HopperRetryAdmissionTests.source_well_formed
abbrev descriptors := HopperRetryAdmissionTests.actual_descriptor_admission

theorem actual_resource_source_ranks (value : ℝ) (tile : Fin 3) :
    retrySourceRank (family value) ((family value).expectId tile) = retryUnit (family value)*(1024*expectSerial tile) ∧
    retrySourceRank (family value) ((family value).copyAId tile).issue = retryUnit (family value)*(1024*copyASerial tile) ∧
    retrySourceRank (family value) ((family value).copyBId tile).issue = retryUnit (family value)*(1024*copyBSerial tile) :=
  ⟨retry_expect_source_rank (family value) tile tile.isLt,retry_copy_a_source_rank (family value) tile tile.isLt,
    retry_copy_b_source_rank (family value) tile tile.isLt⟩

theorem actual_endpoint_ranks (value : ℝ) (slot : Stage) :
    retrySourceRank (family value) ((family value).initId slot) = retryUnit (family value)*(1024*slot.val) ∧
    retrySourceRank (family value) ((family value).invalId slot) = retryUnit (family value)*(1024*(44+slot.val)) :=
  ⟨retry_init_source_rank (family value) slot,retry_inval_source_rank (family value) slot⟩

theorem actual_notification_roles (value : ℝ) (tile : Fin 3) :
    retryTmaRank (family value) (.notify ((family value).copyAId tile)) = retryNoticeClock (family value) tile false ∧
    retryTmaRank (family value) (.notify ((family value).copyBId tile)) = retryNoticeClock (family value) tile true :=
  ⟨retry_notification_a_rank (family value) tile tile.isLt,retry_notification_b_rank (family value) tile tile.isLt⟩

theorem actual_completion_component (value : ℝ) (tile : Fin 3) (offset : Fin 2048) :
    Tma.InternalEdge (candidate value).view (.write ((family value).copyAId tile) offset.val) (.notify ((family value).copyAId tile)) ∧
    retryTmaRank (family value) (.write ((family value).copyAId tile) offset.val) < retryTmaRank (family value) (.notify ((family value).copyAId tile)) := by
  have hp : Tma.WritePresent (candidate value).view ((family value).copyAId tile) offset.val := by
    rw [Tma.WritePresent,family_copy_a_at (family value) (source value (fun _ => .bits (byte 0))) tile tile.isLt]
    change offset.val < (replyCopyA 3 ((family value).replies 0) ((family value).schedules 0) tile).descriptor.bytes
    rw [family_copy_a_descriptor (family value) (source value (fun _ => .bits (byte 0))) (descriptors value) tile tile.isLt]
    exact offset.isLt
  have he := Tma.InternalEdge.complete hp
  exact ⟨he,retry_tma_internal_order (family value) (by decide) (source value (fun _ => .bits (byte 0))) he⟩

theorem actual_failed_notice_success_order (value : ℝ) (tile : Fin 3) (lane : Wgmma.Lane) (attempt : Fin ((family value).schedules lane tile)) :
    retryTmaRank (family value) (.source ((family value).failedWaitId tile lane attempt)) < retryTmaRank (family value) (.notify ((family value).copyAId tile)) ∧
    retryTmaRank (family value) (.notify ((family value).copyAId tile)) < retryTmaRank (family value) (.notify ((family value).copyBId tile)) ∧
    retryTmaRank (family value) (.notify ((family value).copyBId tile)) < retryTmaRank (family value) (.source ((family value).waitId tile lane)) := by
  simp only [retryTmaRank,retry_notification_a_rank (family value) tile tile.isLt,retry_notification_b_rank (family value) tile tile.isLt,
    retry_failed_wait_source_rank (family value) tile tile.isLt lane attempt attempt.isLt,retry_successful_wait_source_rank (family value) tile tile.isLt lane]
  exact ⟨retry_failed_before_notice (family value) tile tile.isLt lane attempt attempt.isLt,
    retry_notice_a_before_b (family value) tile,retry_notice_before_success (family value) tile lane⟩

theorem old_immediate_notice_clock_fails (value : ℝ) :
    ¬retrySourceRank (family value) ((family value).failedWaitId 0 0 0) <
      retrySourceRank (family value) ((family value).copyAId 0).issue+retryUnit (family value)*512 := by
  rw [retry_failed_wait_source_rank (family value) 0 (by decide) 0 0 (by change 0 < 1; decide),
    retry_copy_a_source_rank (family value) 0 (by decide)]
  have aux (unit : Nat) : ¬unit*(1024*7+128) < unit*(1024*6)+unit*512 := by omega
  simpa only [retryFailedClock,copyASerial,ite_true,Fin.val_zero,Nat.mul_zero,Nat.add_zero] using aux (retryUnit (family value))

theorem admitted_sorted_resource_component (value : ℝ) (loc : Location) :
    Tma.HistoryValid Tma.localShared (candidate value).view loc (retryHistories (family value) loc) ∧
    ((retryHistories (family value) loc).map Tma.Entry.origin).Pairwise
      (fun left right => retryTmaRank (family value) left.node < retryTmaRank (family value) right.node) :=
  ⟨HopperRetryAdmissionTests.all_resource_histories_admitted value loc,retry_histories_control_sorted (family value) loc⟩

theorem actual_history_lengths (value : ℝ) :
    (retryResourceHistory (family value) 0).length = 1030 ∧ (retryResourceHistory (family value) 1).length = 516 := ⟨rfl,rfl⟩

theorem reverse_completion_rejected (value : ℝ) (tile : Fin 3) (offset : Fin 2048) :
    ¬Tma.InternalEdge (candidate value).view (.notify ((family value).copyAId tile)) (.write ((family value).copyAId tile) offset.val) := by
  intro he
  have hh := retry_tma_internal_order (family value) (by decide) (source value (fun _ => .bits (byte 0))) he
  have ha := (actual_completion_component value tile offset).2
  omega

theorem source_tma_resource_cycles_rejected (value : ℝ) (node : Tma.Node) :
    ¬Ptx.Event.Path (fun left right => Tma.ProgramOrder (candidate value).view left right ∨
      Tma.InternalEdge (candidate value).view left right ∨ Tma.ResourceEdge (retryHistories (family value)) left right) node node := by
  intro hcycle
  have hh := hcycle.rank_lt (retryTmaRank (family value)) (fun _ _ he =>
    he.elim (retry_tma_program_order (family value) (source value (fun _ => .bits (byte 0))))
      (fun h => h.elim (retry_tma_internal_order (family value) (by decide) (source value (fun _ => .bits (byte 0))))
        (retry_control_resource_order (family value))))
  omega

end
end Ptx.HopperRetryTmaControlTests
