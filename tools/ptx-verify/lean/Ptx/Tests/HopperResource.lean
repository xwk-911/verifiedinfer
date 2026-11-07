import Ptx.Hopper.ResourceControl
import Ptx.Generated.HopperMbarrierPeers
import Ptx.Tests.HopperMbarrier
import Mathlib.Tactic.IntervalCases

/-! Four actual threads in two CTAs share two independent mbarrier resources
at offset zero. This checks source/resource/control witnesses, not a complete
Hopper memory/proxy/TMA/WGMMA execution or a GEMM correctness contract. -/
namespace Ptx.HopperResourceTests
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def id (cta lane : Nat) : ThreadId := ⟨⟨cta,0,0⟩,⟨lane,0,0⟩⟩
def loc (cta : Nat) : Location := ⟨.shared ⟨cta,0,0⟩,0⟩
def eid (cta lane serial : Nat) : Ptx.Event.EventId := ⟨id cta lane,serial⟩
def oracle : Oracle := {ampere := {scalar := fun _ => .integer 0,bytes := fun _ => []},wait := fun _ => true}
def geometry : Geometry := ⟨⟨2,1,1⟩,⟨2,1,1⟩⟩
def launch : Scalar.Launch := ⟨geometry,[],fun _ => .bits (byte 165)⟩
def barrier (cta : Nat) (op : BarrierOp) : Hopper.Event := .barrier ⟨loc cta,op⟩
def arrival (generation : Nat) : Hopper.Event := .ampere (.ordinary (.barrierArrival 0 generation))
def returned (generation : Nat) : Hopper.Event := .ampere (.ordinary (.barrierReturn 0 generation))
def leaderEvents (cta : Nat) : List Hopper.Event :=
  [barrier cta (.init 1),arrival 0,returned 0,barrier cta (.arriveExpectTx 16),barrier cta (.completeTx 16),
    barrier cta (.tryWaitParity 0 true),arrival 1,returned 1,barrier cta .inval]
def peerEvents (cta : Nat) : List Hopper.Event :=
  [arrival 0,returned 0,barrier cta (.tryWaitParity 0 true),arrival 1,returned 1]
def done (lane : Nat) : State := {
  scalar := {
    core := {
      thread := {pc := 14,regs := [("%ready",1),("%leader",if lane = 0 then 1 else 0),("%lane",lane),("%bar",0)],status := .done}
      queries := 1
      generations := [(0,2)]
    }
  }
}
def leader (cta : Nat) : ThreadTrace := ⟨id cta 0,oracle,15,done 0,leaderEvents cta⟩
def peer (cta : Nat) : ThreadTrace := ⟨id cta 1,oracle,11,done 1,peerEvents cta⟩
def candidate : Candidate := ⟨[leader 0,peer 0,leader 1,peer 1]⟩

theorem leader_source (cta : Nat) : Produced Generated.hopper_mbarrier_peers.program [] ⟨2,1,1⟩ (leader cta) := by rfl
theorem peer_source (cta : Nat) : Produced Generated.hopper_mbarrier_peers.program [] ⟨2,1,1⟩ (peer cta) := by rfl

theorem formed : WellFormed Generated.hopper_mbarrier_peers.program launch candidate := by
  refine ⟨by norm_num [launch,geometry,Geometry.Valid,Dim3.Positive],by decide,?_,?_⟩
  · intro t ht
    simp only [candidate,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact ⟨by norm_num [leader,id,launch,geometry,ThreadId.Valid,Dim3.Within],leader_source 0⟩
    · exact ⟨by norm_num [peer,id,launch,geometry,ThreadId.Valid,Dim3.Within],peer_source 0⟩
    · exact ⟨by norm_num [leader,id,launch,geometry,ThreadId.Valid,Dim3.Within],leader_source 1⟩
    · exact ⟨by norm_num [peer,id,launch,geometry,ThreadId.Valid,Dim3.Within],peer_source 1⟩
  · intro who hv
    rcases who with ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩
    change (cx < 2 ∧ cy < 1 ∧ cz < 1) ∧ (tx < 2 ∧ ty < 1 ∧ tz < 1) at hv
    rcases hv with ⟨⟨hcx,hcy,hcz⟩,⟨htx,hty,htz⟩⟩
    obtain ⟨rfl,rfl,rfl,rfl⟩ : cy = 0 ∧ cz = 0 ∧ ty = 0 ∧ tz = 0 := by omega
    interval_cases cx <;> interval_cases tx <;>
      first | exact ⟨leader 0,by simp [candidate],rfl⟩ | exact ⟨peer 0,by simp [candidate],rfl⟩ |
        exact ⟨leader 1,by simp [candidate],rfl⟩ | exact ⟨peer 1,by simp [candidate],rfl⟩

theorem complete : Complete candidate := by
  intro t ht
  simp only [candidate,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> rfl

def history (cta : Nat) : List ResourceEntry :=
  [⟨eid cta 0 0,.init 1⟩,⟨eid cta 0 3,.arriveExpectTx 16⟩,⟨eid cta 0 4,.completeTx 16⟩,
    ⟨eid cta 0 5,.tryWaitParity 0 true⟩,⟨eid cta 1 2,.tryWaitParity 0 true⟩,⟨eid cta 0 8,.inval⟩]
def histories (location : Location) : List ResourceEntry :=
  if location = loc 0 then history 0 else if location = loc 1 then history 1 else []

theorem actual_resources : candidate.resourceLocations = [loc 0,loc 1] := by rfl

theorem history_zero : HistoryValid candidate (loc 0) (history 0) :=
  ⟨by decide,by decide,by decide,⟨none,by decide⟩⟩
theorem history_one : HistoryValid candidate (loc 1) (history 1) :=
  ⟨by decide,by decide,by decide,⟨none,by decide⟩⟩

theorem all_histories : ∀ location, HistoryValid candidate location (histories location) := by
  intro location
  by_cases h0 : location = loc 0
  · subst location
    exact history_zero
  · by_cases h1 : location = loc 1
    · subst location
      exact history_one
    · have hn : location ∉ candidate.resourceLocations := by rw [actual_resources]; simp [h0,h1]
      simpa [histories,h0,h1] using empty_history (barrier_inventory_empty hn)

def schedule (cta : Nat) : List Ptx.Event.EventId :=
  [eid cta 0 0,eid cta 0 1,eid cta 1 0,eid cta 0 2,eid cta 1 1,eid cta 0 3,eid cta 0 4,
   eid cta 0 5,eid cta 1 2,eid cta 0 6,eid cta 1 3,eid cta 0 7,eid cta 1 4,eid cta 0 8]
def rank (event : Ptx.Event.EventId) : Nat := (schedule 0++schedule 1).idxOf event

theorem finite_control_rank : ∀ a ∈ candidate.eventIds, ∀ b ∈ candidate.eventIds,
    ResourceControlEdge candidate histories a b → rank a < rank b := by decide

theorem control_acyclic : ResourceControlAcyclic candidate histories :=
  resource_control_acyclic_of_rank all_histories rank finite_control_rank

theorem source_resources_control : ResourceConditions Generated.hopper_mbarrier_peers.program launch candidate histories :=
  ⟨formed,complete,all_histories,control_acyclic⟩

theorem peer_wait_actual_phase : ∃ state, candidate.barrierAt (eid 0 1 2) = some ⟨loc 0,.tryWaitParity 0 true⟩ ∧
    Mbarrier.WellFormed state ∧ Mbarrier.run none (((history 0).map ResourceEntry.operation).take 4) = some (some state) ∧
    0 < state.phase ∧ 0%2 ≠ state.phase%2 :=
  successful_wait_has_actual_phase history_zero (by rfl)

theorem peer_wait_source_pc : sourcePC candidate Generated.hopper_mbarrier_peers.program [] ⟨2,1,1⟩ (eid 0 1 2) = some 9 := by rfl
theorem leader_wait_source_pc : sourcePC candidate Generated.hopper_mbarrier_peers.program [] ⟨2,1,1⟩ (eid 1 0 5) = some 9 := by rfl
theorem initial_cta_barrier_pc : sourcePC candidate Generated.hopper_mbarrier_peers.program [] ⟨2,1,1⟩ (eid 0 1 1) = some 5 := by rfl
theorem final_cta_barrier_pc : sourcePC candidate Generated.hopper_mbarrier_peers.program [] ⟨2,1,1⟩ (eid 1 0 7) = some 11 := by rfl

theorem peer_before_invalidation : ResourceEdge candidate histories (eid 0 1 2) (eid 0 0 8) := by decide
theorem other_cta_not_same_resource : ¬ ResourceEdge candidate histories (eid 0 0 4) (eid 1 1 2) := by decide

def droppedPeer := (history 0).eraseIdx 4
theorem dropped_peer_breaks_coverage : ¬ droppedPeer.Perm (candidate.barrierInventory (loc 0)) := by decide

def duplicateEntry : List ResourceEntry := ⟨eid 0 0 0,.init 1⟩ :: history 0
theorem duplicate_identity_rejected : ¬ (duplicateEntry.map ResourceEntry.id).Nodup := by decide

def reversedLeader := (history 0).reverse
theorem reversed_thread_order_rejected : ¬ ThreadOrder reversedLeader := by decide

def badCandidate : Candidate := ⟨[⟨⟨.zero,.zero⟩,HopperMbarrierTests.oracle (fun _ => true),4,
  HopperMbarrierTests.badDone,HopperMbarrierTests.badEvents⟩]⟩
def ghostComplete : List ResourceEntry :=
  [⟨⟨⟨.zero,.zero⟩,0⟩,.init 1⟩,⟨⟨⟨.zero,.zero⟩,1⟩,.arriveExpectTx 16⟩,
   ⟨⟨⟨.zero,.zero⟩,99⟩,.completeTx 16⟩,⟨⟨⟨.zero,.zero⟩,2⟩,.tryWaitParity 0 true⟩]

theorem ghost_not_a_source_event : badCandidate.barrierAt ⟨⟨.zero,.zero⟩,99⟩ = none := by rfl
theorem ghost_protocol_alone_passes : Mbarrier.Admitted (ghostComplete.map ResourceEntry.operation) := ⟨some ⟨1,1,1,0,true⟩,by decide⟩
theorem ghost_breaks_coverage : ¬ ghostComplete.Perm (badCandidate.barrierInventory HopperMbarrierTests.loc) := by decide

end
end Ptx.HopperResourceTests
