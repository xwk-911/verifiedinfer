import Ptx.Hopper.UnifiedCollective
import Ptx.Tests.WgmmaProtocol

/-! Source/view unit tests. The small one-thread fixtures deliberately do not
meet warpgroup participation; a source witness is not full ISA admission.
Pending-ledger completion and missing-lane collective rejection are separate.
-/
namespace Ptx.UnifiedTests
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def ctx : Scalar.Context := {id := ⟨.zero,.zero⟩,params := [],block := .one}
def oracle : Wgmma.Oracle := WgmmaProtocolTests.oracle
def setup : List Hopper.Instr := [
  .ampere (.scalar (.integer (.mov 64 "%a" (.imm Wgmma.packedA)))),
  .ampere (.scalar (.integer (.mov 64 "%b" (.imm Wgmma.packedB)))),
  .ampere (.scalar (.integer (.mov 64 "%out" (.imm 8192))))]
def issue : List Hopper.Instr := setup++[.wgmma .fence,.wgmma (.mma WgmmaProtocolTests.d "%a" "%b" (.imm 0))]
def goodCode : List Hopper.Instr := issue++[.wgmma .commit,.wgmma (.wait 0),
  .ampere (.scalar (.store .f32 .global ⟨.reg "%out",0⟩ (.reg "%d0"))),.ampere (.scalar (.integer .ret))]
def badCode : List Hopper.Instr := issue++[.ampere (.scalar (.integer .ret))]
def goodResult : Wgmma.State × List Wgmma.Event := (Wgmma.run ctx oracle goodCode 9 {}).toOption.getD ({},[])
def badResult : Wgmma.State × List Wgmma.Event := (Wgmma.run ctx oracle badCode 6 {}).toOption.getD ({},[])
def trace (result : Wgmma.State × List Wgmma.Event) (count : Nat) : Unified.ThreadTrace := ⟨ctx.id,oracle,count,result.1,result.2⟩
def good : Unified.Candidate := ⟨[trace goodResult 9]⟩
def bad : Unified.Candidate := ⟨[trace badResult 6]⟩
def launch : Scalar.Launch := ⟨⟨.one,.one⟩,[],fun _ => .bits (byte 0)⟩
def eid (serial : Nat) : Ptx.Event.EventId := ⟨ctx.id,serial⟩

theorem good_produced : Unified.Produced goodCode [] .one (trace goodResult 9) := by rfl
theorem bad_produced : Unified.Produced badCode [] .one (trace badResult 6) := by rfl
theorem good_complete : Unified.Complete good := by
  intro actual ht
  simp only [good,List.mem_singleton] at ht
  subst actual
  apply Wgmma.complete_of_metadata
  decide
theorem bad_base_status_done : Hopper.Complete bad.view := by
  intro actual ht
  simp only [bad,Unified.Candidate.view,List.map_cons,List.map_nil,List.mem_singleton] at ht
  subst actual
  rfl
theorem bad_pending_not_complete : ¬Unified.Complete bad := by
  intro h
  have hp := (h (trace badResult 6) (by simp [bad])).2
  have hn := congrArg List.length hp
  have hlen : (Wgmma.pending (trace badResult 6).final.ledger).length = 1 := by decide
  rw [hlen] at hn
  cases hn
theorem view_keeps_all_slots : good.view.traces[0]?.map (fun trace => trace.events.length) = some 5 := by decide
theorem source_tags_are_not_memory :
    (Unified.kind Tma.localShared Access.globalDescriptor good (.base (.tma (.source (eid 1))))).isSome = false := by decide
theorem actual_store_serial :
    (good.view.eventAt (eid 4)).map (fun event => match event with | .ampere (.ordinary (.write _ _)) => true | _ => false) = some true := by decide
theorem actual_representative : (good.representativeAt (eid 1)).isSome = true := by decide
theorem no_representative_from_fence : (good.representativeAt (eid 0)).isSome = false := by decide
theorem legacy_entry_rejects_unified_source : (Hopper.run ctx oracle.base goodCode 9 {}).toOption.isSome = false := by decide

def fake : Unified.Candidate := ⟨[{trace goodResult 9 with events := [.base (.wgmma .mma)]}]⟩
theorem projected_tag_cannot_create_reader : (fake.representativeAt (eid 0)).isSome = false := by decide
theorem projected_tag_has_no_wgmma_read :
    (Unified.kind Tma.localShared Access.globalDescriptor fake (.wgmmaRead (eid 0) (.a (0,0) 0))).isSome = false := by decide
theorem all_actual_calls_lane_zero {id mark call} (he : good.eventAt id = some (.mma mark call)) : call.lane = 0 := by
  obtain ⟨actual,ht,_,hx⟩ := Unified.eventAt_trace he
  simp only [good,List.mem_singleton] at ht
  subst actual
  have hm := List.mem_of_getElem? hx
  change Wgmma.Event.mma mark call ∈ [_,_,_,_,_] at hm
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hm
  rcases hm with hm | hm | hm | hm | hm
  · cases hm
  · cases hm; rfl
  · cases hm
  · cases hm
  · cases hm
theorem incomplete_warpgroup_rejected (id : Ptx.Event.EventId) : IsEmpty (Unified.Collective good id) :=
  Unified.collective_missing_lane_rejected (1 : Wgmma.Lane) (fun _ _ _ he h => by
    have hz := all_actual_calls_lane_zero he
    rw [hz] at h
    cases h)

end
end Ptx.UnifiedTests
