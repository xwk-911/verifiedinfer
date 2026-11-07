import Ptx.Kernels.HopperDoubleBufferNativeRanks

/-! Combined TMA/resource/CTA/native control acyclicity for the repeated
source witness. Native arrivals precede all matching warp returns; lane
offsets in source/resource ranks are retained. Control admission does not
establish byte-memory eligibility, RF/co, observers or runtime correspondence. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def dataNativeControlRank (tiles : Nat) : Unified.ControlNode → Nat
  | .base node => 2*controlRank tiles node
  | .arrival id => 2*(1024*nativeTick tiles id)-1
  | .operand issue _ => 2*(1024*nativeTick tiles issue+128)

theorem data_native_arrival_rank {a b tiles left right}
    (he : Unified.NativeArrival (dataCompleteCandidate a b tiles) left right) :
    dataNativeControlRank tiles left < dataNativeControlRank tiles right := by
  cases left with
  | base node =>
    cases node <;> cases right <;> try exact False.elim he
    rename_i before event
    obtain ⟨signature,hs⟩ := Option.isSome_iff_exists.mp he.2
    obtain ⟨tile,lane,index,ht,hid,_⟩ := data_native_signature_shape hs
    have hb : resourceLane before.thread < 128 := by
      rw [he.1.2.2.1,hid]
      change resourceLane (ctx tiles lane).id < 128
      rw [resource_lane_value]
      exact lane.isLt
    have hm : nativeTick tiles before < nativeTick tiles event := by
      have hmono := source_tick_strict tiles (resourceLane before.thread) he.1.2.2.2
      simpa only [nativeTick,← he.1.2.2.1] using hmono
    change 2*(1024*nativeTick tiles before+resourceLane before.thread) < 2*(1024*nativeTick tiles event)-1
    omega
  | arrival _ | operand _ _ => exact False.elim he

theorem data_native_rendezvous_rank {a b tiles left right}
    (he : Unified.NativeRendezvous HopperStage.block (dataCompleteCandidate a b tiles) left right) :
    dataNativeControlRank tiles left < dataNativeControlRank tiles right := by
  cases left <;> cases right <;> try exact False.elim he
  rename_i event node
  cases node <;> try exact False.elim he
  have heq := data_native_sync_equal_ticks he
  obtain ⟨_,signature,hl,_⟩ := he
  have hp := data_native_tick_positive hl
  change 2*(1024*nativeTick tiles _)-1 < 2*(1024*nativeTick tiles _+_)
  omega

theorem data_native_issue_rank {a b tiles left right}
    (he : Unified.NativeIssue (dataCompleteCandidate a b tiles) left right) :
    dataNativeControlRank tiles left < dataNativeControlRank tiles right := by
  cases left with
  | base node =>
    cases node <;> cases right <;> try exact False.elim he
    rename_i event issue operand
    obtain ⟨rfl,hp⟩ := he
    obtain ⟨pair,hpair⟩ := Option.isSome_iff_exists.mp hp
    obtain ⟨tile,lane,ht,hid,_⟩ := data_native_mma_case (Unified.representative_at hpair).1
    have hb : resourceLane event.thread < 128 := by
      rw [hid]
      change resourceLane (ctx tiles lane).id < 128
      rw [resource_lane_value]
      exact lane.isLt
    change 2*(1024*nativeTick tiles event+resourceLane event.thread) < 2*(1024*nativeTick tiles event+128)
    omega
  | arrival _ | operand _ _ => exact False.elim he

theorem data_native_finish_rank {a b tiles left right} (hb : tiles ≤ 2^28)
    (he : Unified.NativeFinish (dataCompleteCandidate a b tiles) left right) :
    dataNativeControlRank tiles left < dataNativeControlRank tiles right := by
  cases left <;> cases right <;> try exact False.elim he
  rename_i issue operand node
  cases node <;> try exact False.elim he
  rename_i wait
  obtain ⟨collective,lane,mark,groups,keep,before,after,query,hw,_,_,_,_,hg,_⟩ := he
  have hi : (dataCompleteCandidate a b tiles).eventAt issue = some (.mma (collective.marks 0) (collective.calls 0)) := by
    simpa only [collective.representative] using collective.matched 0
  obtain ⟨it,il,hit,hissue,hgroup⟩ := data_native_mma_case hi
  obtain ⟨wt,wl,hwt,hwait,hafter⟩ := data_native_wait_case hb hw
  have hle : it ≤ wt := by
    rw [collective.cohort.group lane,hgroup,hafter] at hg
    omega
  change 2*(1024*nativeTick tiles issue+128) < 2*sourceControlRank tiles wait
  rw [hissue,hwait,data_native_id_tick a b tiles it il hit 1,data_native_id_control_rank a b tiles wt wl hwt 3]
  have hl := wl.isLt
  omega

theorem data_tma_control_edge_rank {a b tiles left right}
    (he : Tma.ControlEdge (dataCompleteCandidate a b tiles).view (dataHistories a b tiles) left right) :
    controlRank tiles left < controlRank tiles right := by
  rcases he with hp | hc | hi | hr
  · exact control_program_order a b tiles hp
  · exact control_cta_order a b tiles hc
  · exact control_internal_order a b tiles hi
  · exact control_resource_order a b tiles hr

theorem data_native_control_edge_rank {a b tiles left right} (hb : tiles ≤ 2^28)
    (he : Unified.ControlEdge HopperStage.block (dataCompleteCandidate a b tiles) (dataHistories a b tiles) left right) :
    dataNativeControlRank tiles left < dataNativeControlRank tiles right := by
  rcases he with hbase | ha | hr | hi | hf
  · cases left <;> cases right <;> try exact False.elim hbase
    have hh := data_tma_control_edge_rank hbase
    change 2*controlRank tiles _ < 2*controlRank tiles _
    omega
  · exact data_native_arrival_rank ha
  · exact data_native_rendezvous_rank hr
  · exact data_native_issue_rank hi
  · exact data_native_finish_rank hb hf

theorem data_native_control_acyclic (a b tiles) (hb : tiles ≤ 2^28) :
    Unified.ControlAcyclic HopperStage.block (dataCompleteCandidate a b tiles) (dataHistories a b tiles) :=
  Unified.control_acyclic_of_rank (dataNativeControlRank tiles) (fun _ _ => data_native_control_edge_rank hb)

theorem data_native_control_admitted (a b tiles) (hb : tiles ≤ 2^28) :
    Unified.ControlAdmitted HopperStage.block (dataCompleteCandidate a b tiles) (dataHistories a b tiles) :=
  ⟨data_native_schedules_admitted a b tiles,data_native_control_acyclic a b tiles hb⟩

end
end Ptx.Kernels.HopperDoubleBuffer
