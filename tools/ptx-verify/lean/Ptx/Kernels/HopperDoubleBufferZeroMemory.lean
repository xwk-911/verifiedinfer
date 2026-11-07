import Ptx.Kernels.HopperDoubleBufferZeroControl
import Ptx.Kernels.HopperDoubleBufferObservedOutput
import Ptx.Kernels.HopperDoubleBufferCandidateAdmission
import Ptx.Hopper.UnifiedMemoryControl

/-! Full memory admission for every actual completed zero-K candidate and
arbitrary initial bytes. Actual reads are absent; actual output writers remain
present, unique and ordered. This does not erase output/observer obligations. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def zeroRf : Unified.ReadsFrom := fun _ _ => none
def zeroCo (candidate : Unified.Candidate) := Unified.InitialCo Tma.localShared Access.globalDescriptor candidate
def zeroMemoryRank (node : Unified.Node) : Nat := dataNativeControlRank 0 (Unified.memoryControlNode node)

theorem completed_zero_no_reads {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    (node : Unified.Node) (loc : Location) : Unified.readByte Tma.localShared Access.globalDescriptor candidate node loc = none := by
  cases node with
  | wgmmaRead issue operand => simp only [Unified.readByte,Unified.kind,completed_zero_representative_none hw hc,Option.map_none,Option.bind_none]
  | base node =>
    cases node with
    | copyRead _ | copyWrite _ => simp [Unified.readByte,Unified.kind,Access.kind,candidate_no_nonbulk (by decide) hw hc]
    | tma node =>
      cases node with
      | source id => exact candidate_ordinary_read_none (by decide) hw hc id loc
      | descriptor _ | read _ _ | write _ _ | notify _ =>
        simp only [Unified.readByte,Unified.kind,Access.kind,Tma.readLocation,Tma.writeLocation,Tma.transferByte,
          completed_zero_no_tma hw hc,Option.map_none,Option.bind_none] <;> rfl

theorem completed_zero_byte_order_rank {initial candidate loc left right}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    (he : Unified.ByteOrder Tma.localShared Access.globalDescriptor candidate zeroHistories dataCluster loc left right) :
    zeroMemoryRank left < zeroMemoryRank right := by
  have hp := Unified.byte_order_control_path (block := HopperStage.block) (candidate_no_nonbulk (by decide) hw hc) he
  exact hp.rank_lt (dataNativeControlRank 0) (fun _ _ => completed_zero_control_rank hw hc)

theorem completed_zero_no_observation_order {initial candidate rf left right}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    ¬Unified.ObservationOrder Tma.localShared Access.globalDescriptor candidate rf left right := by
  intro he
  induction he with
  | direct h =>
    obtain ⟨_,loc,value,hr,_⟩ := h
    rw [completed_zero_no_reads hw hc] at hr
    cases hr
  | viaRMW _ _ _ ih _ => exact ih

theorem completed_zero_causality_rank {initial candidate rf loc left right}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    (he : Unified.CausalityAt Tma.localShared Access.globalDescriptor candidate zeroHistories dataCluster rf loc left right) :
    zeroMemoryRank left < zeroMemoryRank right := by
  rcases he with ⟨_,_,hp⟩ | ⟨middle,ho,_⟩
  · exact completed_zero_byte_order_rank hw hc hp
  · exact (completed_zero_no_observation_order hw hc ho).elim

theorem completed_zero_global_writers_unique {initial candidate loc left right lv rv}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) (hg : loc.space = .global)
    (hl : Unified.writeByte Tma.localShared Access.globalDescriptor candidate left loc = some lv)
    (hr : Unified.writeByte Tma.localShared Access.globalDescriptor candidate right loc = some rv) : left = right := by
  rw [Unified.write_byte_lookup_eq (completed_zero_event_lookup hw hc)] at hl hr
  exact data_global_unique_writers (a := fun _ _ => 0) (b := fun _ _ => 0) (tiles := 0) (by decide) hg hl hr

theorem completed_zero_writers_unique {initial candidate loc left right lv rv}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    (hl : Unified.writeByte Tma.localShared Access.globalDescriptor candidate left loc = some lv)
    (hr : Unified.writeByte Tma.localShared Access.globalDescriptor candidate right loc = some rv) : left = right := by
  obtain ⟨base,size,hf,hs | hg⟩ := candidate_write_footprint_regions (by decide) hw hc hl
  all_goals have hb := Unified.access_footprint_bounds (.inr (by rw [hl]; rfl)) hf
  · obtain ⟨id,offset,_,hloc⟩ := candidate_shared_writer_is_tensor (by decide) hw hc (hb.1.symm.trans hs.1) hl
    simp only [Tma.writeLocation,completed_zero_no_tma hw hc,Option.bind_none] at hloc
    cases hloc
  · exact completed_zero_global_writers_unique hw hc (hb.1.symm.trans hg.1) hl hr

theorem completed_zero_coherent {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    Unified.Coherent Tma.localShared Access.globalDescriptor candidate zeroHistories dataCluster zeroRf (zeroCo candidate) := by
  apply Unified.unique_initial_coherent
  · intro loc left right lv rv hl hr
    exact completed_zero_writers_unique hw hc hl hr
  · intro loc writer value hwrite hself
    exact Nat.lt_irrefl _ (completed_zero_causality_rank hw hc hself)

theorem completed_zero_no_communication {initial candidate left right}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    ¬Unified.Communication Tma.localShared Access.globalDescriptor candidate zeroRf (zeroCo candidate) left right := by
  rintro (⟨loc,value,hr,_⟩ | ⟨loc,hco⟩ | ⟨_,loc,value,hr,_⟩)
  · rw [completed_zero_no_reads hw hc] at hr; cases hr
  · cases hco.1
  · rw [completed_zero_no_reads hw hc] at hr; cases hr

theorem completed_zero_sc_per_location {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    Unified.SCPerLocation Tma.localShared Access.globalDescriptor candidate zeroRf (zeroCo candidate) := by
  intro members _ _ node _ hp
  have hh := hp.rank_lt zeroMemoryRank (fun left right he => he.2.2.elim
    (fun h => completed_zero_control_rank hw hc (Unified.program_order_control_edge (histories := zeroHistories) h))
    (fun h => (completed_zero_no_communication hw hc h).elim))
  omega

theorem completed_zero_memory_witness {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate (fun _ => initial) zeroRf (zeroCo candidate) zeroHistories dataCluster := by
  refine ⟨⟨?_,?_,?_,?_⟩,?_,fun _ => completed_zero_coherent hw hc,?_,?_,fun _ => completed_zero_sc_per_location hw hc⟩
  · intro read loc value _ hr
    rw [completed_zero_no_reads hw hc] at hr; cases hr
  · intro _ writer loc value hwrite
    exact ⟨rfl,writer,rfl,by rw [Unified.WritesAt,hwrite]; rfl⟩
  · intro _ writer read loc vw vr hwrite hr
    rw [completed_zero_no_reads hw hc] at hr; cases hr
  · intro _ read writer loc vr vw hr
    rw [completed_zero_no_reads hw hc] at hr; cases hr
  · intro loc node hp
    exact Nat.lt_irrefl _ (completed_zero_byte_order_rank hw hc hp)
  · intro _ read writer _ loc vr vw hr
    rw [completed_zero_no_reads hw hc] at hr; cases hr
  · intro _ atomic writer _ _ loc vr vw hr
    rw [completed_zero_no_reads hw hc] at hr; cases hr

end
end Ptx.Kernels.HopperDoubleBuffer
