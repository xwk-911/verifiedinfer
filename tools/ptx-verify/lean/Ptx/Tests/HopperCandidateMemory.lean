import Ptx.Kernels.HopperDoubleBufferCandidateMemory
import Ptx.Kernels.HopperDoubleBufferReplyCandidate

/-! A complete source candidate with heterogeneous lane retries and arbitrary
captured arithmetic values. It deliberately has no tensor/memory admission:
source structure alone must not assume a correct matrix result. -/
namespace Ptx.HopperCandidateMemoryTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def schedule (lane : Wgmma.Lane) (_tile : Nat) : Nat := lane.val%3
def firstQuery (lane : Wgmma.Lane) : Nat := if HopperStage.leader lane then 4 else 0
def replies (value : ℝ) (lane : Wgmma.Lane) : Wgmma.Oracle := {oracle 1 with
  base := {(oracle 1).base with wait := fun q => decide (firstQuery lane+schedule lane 0 ≤ q)}
  matrix := fun _ _ => value}
def candidate (value : ℝ) : Unified.Candidate := replyCandidate 1 (replies value) schedule

theorem heterogeneous_source_well_formed (value : ℝ) (initial : Location → Symbolic.Byte) :
    Unified.WellFormed code (completeLaunch 1 initial) (candidate value) := by
  apply reply_candidate_well_formed 1 (replies value) schedule initial (by decide) (by decide)
  · intro lane _
    exact ⟨oracle_payload_shape 1 0,oracle_payload_shape 1 2⟩
  · intro lane i hi
    have he : i = 0 := by omega
    subst i
    refine ⟨?_,?_,?_⟩
    · intro j hj
      change decide (firstQuery lane+schedule lane 0 ≤ firstQuery lane+j) = false
      simp only [decide_eq_false_iff_not]
      omega
    · change decide (firstQuery lane+schedule lane 0 ≤ firstQuery lane+schedule lane 0) = true
      simp only [decide_eq_true_eq]
      exact Nat.le_refl _
    · intro hn
      have hh := hn.1
      omega

theorem heterogeneous_source_complete (value : ℝ) : Unified.Complete (candidate value) :=
  reply_candidate_complete 1 (replies value) schedule (by decide) (by decide)
theorem heterogeneous_retries : schedule 0 0 = 0 ∧ schedule 1 0 = 1 ∧ schedule 2 0 = 2 := by decide

theorem arbitrary_captured_values_preserved (value : ℝ) (lane : Wgmma.Lane) :
    (replyTrace 1 (replies value) schedule lane).events.filterMap globalWrite =
      List.ofFn (fun slot : Wgmma.Slot => (outputWordAddress (lane,slot),Symbolic.encode .f32 value)) := by
  change (replyPositiveEvents 1 lane (replies value lane) (schedule lane)).filterMap globalWrite = _
  rw [reply_positive_write_inventory]
  congr 1

theorem exactly_four_output_words (value : ℝ) (lane : Wgmma.Lane) :
    ((replyTrace 1 (replies value) schedule lane).events.filterMap globalWrite).length = 4 := by
  rw [arbitrary_captured_values_preserved,List.length_ofFn]

theorem no_nonbulk_for_heterogeneous_candidate (value : ℝ) (id : Ptx.Event.EventId) :
    Access.copyAt (candidate value).view id = none :=
  candidate_no_nonbulk (by decide) (heterogeneous_source_well_formed value (fun _ => .bits (byte 0))) (heterogeneous_source_complete value) id

theorem no_hidden_ordinary_reads (value : ℝ) (id : Ptx.Event.EventId) (loc : Location) :
    Access.readByte Tma.localShared Access.globalDescriptor (candidate value).view (.tma (.source id)) loc = none :=
  candidate_ordinary_read_none (by decide) (heterogeneous_source_well_formed value (fun _ => .bits (byte 0))) (heterogeneous_source_complete value) id loc

theorem no_hidden_ordinary_shared_writes (value : ℝ) (id : Ptx.Event.EventId) (cta : Dim3) (address : Nat) :
    Access.writeByte Tma.localShared Access.globalDescriptor (candidate value).view (.tma (.source id)) ⟨.shared cta,address⟩ = none :=
  candidate_ordinary_shared_write_none (by decide) (heterogeneous_source_well_formed value (fun _ => .bits (byte 0)))
    (heterogeneous_source_complete value) id _ cta rfl

theorem input_and_descriptor_immutable (value : ℝ) (writer : Unified.Node) :
    Unified.writeByte Tma.localShared Access.globalDescriptor (candidate value) writer ⟨.global,65536⟩ = none ∧
    Unified.writeByte Tma.localShared Access.globalDescriptor (candidate value) writer ⟨.global,4096⟩ = none := by
  constructor
  · exact candidate_global_outside_output_immutable (by decide)
      (heterogeneous_source_well_formed value (fun _ => .bits (byte 0))) (heterogeneous_source_complete value) rfl (by decide) writer
  · exact candidate_global_outside_output_immutable (by decide)
      (heterogeneous_source_well_formed value (fun _ => .bits (byte 0))) (heterogeneous_source_complete value) rfl (by decide) writer

theorem output_guard_bytes_immutable (value : ℝ) (writer : Unified.Node) :
    Unified.writeByte Tma.localShared Access.globalDescriptor (candidate value) writer ⟨.global,8191⟩ = none ∧
    Unified.writeByte Tma.localShared Access.globalDescriptor (candidate value) writer ⟨.global,10240⟩ = none := by
  constructor
  · exact candidate_global_outside_output_immutable (by decide)
      (heterogeneous_source_well_formed value (fun _ => .bits (byte 0))) (heterogeneous_source_complete value) rfl (by decide) writer
  · exact candidate_global_outside_output_immutable (by decide)
      (heterogeneous_source_well_formed value (fun _ => .bits (byte 0))) (heterogeneous_source_complete value) rfl (by decide) writer

theorem actual_shared_writer_has_tma_origin (value : ℝ) {writer loc payload cta} (hl : loc.space = .shared cta)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (candidate value) writer loc = some payload) :
    ∃ id offset, writer = .base (.tma (.write id offset)) ∧ Tma.writeLocation Tma.localShared (candidate value).view id offset = some loc :=
  candidate_shared_writer_is_tensor (by decide) (heterogeneous_source_well_formed value (fun _ => .bits (byte 0)))
    (heterogeneous_source_complete value) hl hw

theorem source_footprints_have_actual_output_owner (value : ℝ) {id base size}
    (hf : (Access.kind Tma.localShared Access.globalDescriptor (candidate value).view (.tma (.source id))).bind
      Ptx.Event.Kind.footprint = some (base,size)) :
    ∃ lane slot, id.thread = (ctx 1 lane).id ∧ base = ⟨.global,outputWordAddress (lane,slot)⟩ ∧ size = 4 :=
  candidate_source_footprint_owner (by decide) (heterogeneous_source_well_formed value (fun _ => .bits (byte 0)))
    (heterogeneous_source_complete value) hf

theorem fake_ordinary_read_rejected (value : ℝ) (id : Ptx.Event.EventId) (loc : Location) (payload : Symbolic.Byte) :
    Access.readByte Tma.localShared Access.globalDescriptor (candidate value).view (.tma (.source id)) loc ≠ some payload := by
  rw [no_hidden_ordinary_reads]
  intro h; cases h

theorem input_write_claim_rejected (value : ℝ) (writer : Unified.Node) (payload : Symbolic.Byte) :
    Unified.writeByte Tma.localShared Access.globalDescriptor (candidate value) writer ⟨.global,65536⟩ ≠ some payload := by
  rw [(input_and_descriptor_immutable value writer).1]
  intro h; cases h

end
end Ptx.HopperCandidateMemoryTests
