import Ptx.Tests.HopperResource
import Ptx.Generated.HopperMbarrierCycle
import Mathlib.Data.List.Permutation

/-! Actual circular waiting source: every individual resource history can pass,
but no source-matching family can have acyclic source/resource control. This is
not a GPU deadlock/termination theorem and the fixture is never GPU-launched. -/
namespace Ptx.HopperResourceCycleTests
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

abbrev id := HopperResourceTests.id 0
abbrev eid (lane serial : Nat) := HopperResourceTests.eid 0 lane serial
def a : Location := ⟨.shared .zero,0⟩
def b : Location := ⟨.shared .zero,8⟩
def geometry : Geometry := ⟨.one,⟨2,1,1⟩⟩
def launch : Scalar.Launch := ⟨geometry,[],fun _ => .bits (byte 165)⟩
def ev (loc : Location) (op : BarrierOp) : Hopper.Event := .barrier ⟨loc,op⟩
def done (lane pc : Nat) : State := {
  scalar := {
    core := {
      thread := {pc := pc,regs := [("%ready",1),("%leader",if lane = 0 then 1 else 0),("%lane",lane),("%b",8),("%a",0)],status := .done}
      queries := 1
      generations := [(0,1)]
    }
  }
}
def leaderEvents : List Hopper.Event :=
  [ev a (.init 1),HopperResourceTests.arrival 0,HopperResourceTests.returned 0,ev b (.tryWaitParity 0 true),ev a (.arriveExpectTx 0)]
def peerEvents : List Hopper.Event :=
  [ev b (.init 1),HopperResourceTests.arrival 0,HopperResourceTests.returned 0,ev a (.tryWaitParity 0 true),ev b (.arriveExpectTx 0)]
def leader : ThreadTrace := ⟨id 0,HopperResourceTests.oracle,13,done 0 13,leaderEvents⟩
def peer : ThreadTrace := ⟨id 1,HopperResourceTests.oracle,12,done 1 17,peerEvents⟩
def candidate : Candidate := ⟨[leader,peer]⟩

theorem leader_source : Produced Generated.hopper_mbarrier_cycle.program [] ⟨2,1,1⟩ leader := by rfl
theorem peer_source : Produced Generated.hopper_mbarrier_cycle.program [] ⟨2,1,1⟩ peer := by rfl
theorem formed : WellFormed Generated.hopper_mbarrier_cycle.program launch candidate := by
  refine ⟨by norm_num [launch,geometry,Geometry.Valid,Dim3.Positive,Dim3.one],by decide,?_,?_⟩
  · intro t ht
    simp only [candidate,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨by norm_num [leader,HopperResourceTests.id,launch,geometry,ThreadId.Valid,Dim3.Within,Dim3.one],leader_source⟩
    · exact ⟨by norm_num [peer,HopperResourceTests.id,launch,geometry,ThreadId.Valid,Dim3.Within,Dim3.one],peer_source⟩
  · intro who hv
    rcases who with ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩
    change (cx < 1 ∧ cy < 1 ∧ cz < 1) ∧ (tx < 2 ∧ ty < 1 ∧ tz < 1) at hv
    rcases hv with ⟨⟨hcx,hcy,hcz⟩,⟨htx,hty,htz⟩⟩
    obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ : cx = 0 ∧ cy = 0 ∧ cz = 0 ∧ ty = 0 ∧ tz = 0 := by omega
    interval_cases tx
    · exact ⟨leader,by simp [candidate],rfl⟩
    · exact ⟨peer,by simp [candidate],rfl⟩

theorem complete : Complete candidate := by
  intro t ht
  simp only [candidate,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl <;> rfl

def historyA : List ResourceEntry := [⟨eid 0 0,.init 1⟩,⟨eid 0 4,.arriveExpectTx 0⟩,⟨eid 1 3,.tryWaitParity 0 true⟩]
def historyB : List ResourceEntry := [⟨eid 1 0,.init 1⟩,⟨eid 1 4,.arriveExpectTx 0⟩,⟨eid 0 3,.tryWaitParity 0 true⟩]
def histories (loc : Location) := if loc = a then historyA else if loc = b then historyB else []

theorem actual_resources : candidate.resourceLocations = [a,b] := by rfl
theorem history_a_valid : HistoryValid candidate a historyA := ⟨by decide,by decide,by decide,⟨some ⟨1,1,1,0,true⟩,by decide⟩⟩
theorem history_b_valid : HistoryValid candidate b historyB := ⟨by decide,by decide,by decide,⟨some ⟨1,1,1,0,true⟩,by decide⟩⟩
theorem all_histories_valid : ∀ loc, HistoryValid candidate loc (histories loc) := by
  intro loc
  by_cases ha : loc = a
  · subst loc
    exact history_a_valid
  · by_cases hb : loc = b
    · subst loc
      exact history_b_valid
    · have hn : loc ∉ candidate.resourceLocations := by rw [actual_resources]; simp [ha,hb]
      simpa [histories,ha,hb] using empty_history (barrier_inventory_empty hn)

theorem only_protocol_order_a : ∀ entries ∈ (candidate.barrierInventory a).permutations',
    (Mbarrier.run none (entries.map ResourceEntry.operation)).isSome = true → entries = historyA := by decide
theorem only_protocol_order_b : ∀ entries ∈ (candidate.barrierInventory b).permutations',
    (Mbarrier.run none (entries.map ResourceEntry.operation)).isSome = true → entries = historyB := by decide

theorem matching_order_a {entries} (h : HistoryValid candidate a entries) : entries = historyA := by
  obtain ⟨last,hr⟩ := h.protocol
  exact only_protocol_order_a entries (List.mem_permutations'.mpr h.exhaustive) (by rw [hr]; rfl)
theorem matching_order_b {entries} (h : HistoryValid candidate b entries) : entries = historyB := by
  obtain ⟨last,hr⟩ := h.protocol
  exact only_protocol_order_b entries (List.mem_permutations'.mpr h.exhaustive) (by rw [hr]; rfl)

theorem every_matching_family_has_cycle (family : Location → List ResourceEntry)
    (h : ∀ loc, HistoryValid candidate loc (family loc)) : ¬ ResourceControlAcyclic candidate family := by
  have ha := matching_order_a (h a)
  have hb := matching_order_b (h b)
  have ab : ResourceControlEdge candidate family (eid 0 3) (eid 0 4) := .inl (by decide)
  have bc : ResourceControlEdge candidate family (eid 0 4) (eid 1 3) :=
    .inr (.inr ⟨a,by decide,by rw [ha]; decide⟩)
  have cd : ResourceControlEdge candidate family (eid 1 3) (eid 1 4) := .inl (by decide)
  have da : ResourceControlEdge candidate family (eid 1 4) (eid 0 3) :=
    .inr (.inr ⟨b,by decide,by rw [hb]; decide⟩)
  intro hc
  exact hc (eid 0 3) (.trans (.single ab) (.trans (.single bc) (.trans (.single cd) (.single da))))

theorem no_resource_conditions (family : Location → List ResourceEntry) :
    ¬ ResourceConditions Generated.hopper_mbarrier_cycle.program launch candidate family := by
  intro h
  exact every_matching_family_has_cycle family h.histories_valid h.control

theorem wrong_local_order_rejected : Mbarrier.run none [.init 1,.tryWaitParity 0 true,.arriveExpectTx 0] = none := by decide

theorem actual_wait_before_own_signal : ProgramOrder candidate (eid 0 3) (eid 0 4) ∧
    ProgramOrder candidate (eid 1 3) (eid 1 4) := by decide

end
end Ptx.HopperResourceCycleTests
