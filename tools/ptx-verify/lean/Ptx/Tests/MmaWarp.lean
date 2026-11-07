import Ptx.Tests.MmaLocal
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-! A complete 32-lane source-produced smoke witness for warp matching and
arithmetic. Memory rf/co/observer admission is a separate obligation. -/
namespace Ptx.MmaWarpTests
open Ptx.ISA Ptx.Ampere
noncomputable section

def id (lane : Mma.Lane) : ThreadId := ⟨.zero,⟨lane.val,0,0⟩⟩
def block : Dim3 := ⟨32,1,1⟩
def oracle : Oracle := {
  scalar := fun _ => .integer 0
  bytes := fun _ => []
  word32 := fun _ => .packed ⟨1,1⟩
  matrix := fun _ _ => 16
}
def trace (lane : Mma.Lane) : ThreadTrace :=
  let result := ((Ampere.run {id := id lane,params := MmaLocalTests.params,block := block}
    oracle Generated.mma_probe.program 25 {}).toOption).getD ({},[])
  ⟨id lane,oracle,25,result.1,result.2⟩
def candidate : Candidate := ⟨List.ofFn trace⟩
def launch : Scalar.Launch := ⟨⟨.one,block⟩,MmaLocalTests.params,fun _ => .bits (byte 165)⟩
def rawCall (lane : Mma.Lane) : MmaCall :=
  match ((trace lane).events[7]? : Option Ampere.Event) with
  | some (.mmaReturn mc) => mc
  | _ => MmaLocalTests.fallback

def call (lane : Mma.Lane) : MmaCall := ⟨19,0,0,lane,(rawCall lane).inputs,fun _ => 16⟩

def participant (lane : Mma.Lane) : MmaParticipant := ⟨⟨id lane,6⟩,⟨id lane,7⟩,call lane⟩

theorem produced (lane : Mma.Lane) : Ampere.Produced Generated.mma_probe.program launch.params block (trace lane) := by
  fin_cases lane <;> rfl

theorem done (lane : Mma.Lane) : (trace lane).final.scalar.core.thread.status = .done := by
  fin_cases lane <;> rfl

theorem trace_at (lane : Mma.Lane) : candidate.traceAt (id lane) = some (trace lane) := by
  fin_cases lane <;> rfl

theorem entry (lane : Mma.Lane) : candidate.eventAt ⟨id lane,6⟩ = some (.mmaEntry (call lane)) := by
  fin_cases lane <;> rfl

theorem leave (lane : Mma.Lane) : candidate.eventAt ⟨id lane,7⟩ = some (.mmaReturn (call lane)) := by
  fin_cases lane <;> rfl

theorem call_lane (lane : Mma.Lane) : (call lane).lane = lane := by
  fin_cases lane <;> rfl

theorem call_keys (lane : Mma.Lane) : (call lane).pc = 19 ∧ (call lane).ordinal = 0 ∧ (call lane).warp = 0 := by
  fin_cases lane <;> exact ⟨rfl,rfl,rfl⟩

theorem input_a (lane : Mma.Lane) (slot : Fin 4) : (call lane).inputs.a slot = ⟨1,1⟩ := by
  fin_cases lane <;> fin_cases slot <;> rfl

theorem input_b (lane : Mma.Lane) (slot : Fin 2) : (call lane).inputs.b slot = ⟨1,1⟩ := by
  fin_cases lane <;> fin_cases slot <;> rfl

theorem input_c (lane : Mma.Lane) (slot : Fin 4) : (call lane).inputs.c slot = 0 := by
  fin_cases lane <;> fin_cases slot <;> exact Scalar.F32Literal.zero_value

theorem output (lane : Mma.Lane) (slot : Fin 4) : (call lane).output slot = 16 := by
  fin_cases lane <;> rfl

set_option maxHeartbeats 2000000 in
theorem participant_valid (lane : Mma.Lane) : (participant lane).Valid Generated.mma_probe.program launch candidate := by
  refine ⟨rfl,by change 6 < 7; decide,entry lane,leave lane,?_,?_,?_⟩
  · fin_cases lane <;> rfl
  · fin_cases lane <;> rfl
  · change 0 = lane.val/32 ∧ lane.val = lane.val%32
    exact ⟨(Nat.div_eq_of_lt lane.isLt).symm,(Nat.mod_eq_of_lt lane.isLt).symm⟩

set_option maxHeartbeats 2000000 in
theorem wellFormed : WellFormed Generated.mma_probe.program launch candidate := by
  refine ⟨by norm_num [launch,block,Geometry.Valid,Dim3.Positive,Dim3.one],by decide +kernel,?_,?_⟩
  · intro t ht
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
    refine ⟨?_,produced lane⟩
    change (id lane).Valid launch.geometry
    simp only [id,launch,ThreadId.Valid,Dim3.Within,block,Dim3.one,Dim3.zero]
    have := lane.isLt
    omega
  · intro thread hv
    rcases thread with ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩
    simp only [launch,ThreadId.Valid,Dim3.Within,block,Dim3.one] at hv
    have hz : cx = 0 ∧ cy = 0 ∧ cz = 0 ∧ ty = 0 ∧ tz = 0 := by omega
    rcases hz with ⟨rfl,rfl,rfl,rfl,rfl⟩
    exact ⟨trace ⟨tx,by omega⟩,List.mem_ofFn.mpr ⟨⟨tx,by omega⟩,rfl⟩,rfl⟩

theorem complete : Complete candidate := by
  intro t ht
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
  exact done lane

set_option maxHeartbeats 2000000 in
theorem return_origin {event mc} (he : candidate.eventAt event = some (.mmaReturn mc)) :
    ∃ lane, event = ⟨id lane,7⟩ ∧ mc = call lane := by
  obtain ⟨t,ht,hid,hi⟩ := eventAt_trace he
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
  rcases event with ⟨thread,serial⟩
  change id lane = thread at hid
  subst thread
  have hs : serial < 12 := by
    have hh := (List.getElem?_eq_some_iff.mp hi).1
    fin_cases lane <;> exact hh
  have hs7 : serial = 7 := by
    by_contra hne
    interval_cases serial <;> first | omega | (fin_cases lane <;> cases hi)
  subst serial
  refine ⟨lane,rfl,?_⟩
  have hh : (trace lane).events[7]? = some (.mmaReturn (call lane)) := by fin_cases lane <;> rfl
  rw [hh] at hi
  exact (Event.mmaReturn.inj (Option.some.inj hi)).symm

theorem arithmetic (lane : Mma.Lane) (slot : Fin 4) :
    (call lane).output slot = Mma.packedResults (fun p => (call p.1).inputs.a p.2)
      (fun p => (call p.1).inputs.b p.2) (fun p => (call p.1).inputs.c p.2) (lane,slot) := by
  rw [output]
  have ha : (fun p : Mma.Lane × Fin 4 => (call p.1).inputs.a p.2) = fun _ => (⟨1,1⟩ : PackedF16) := by
    funext p
    exact input_a p.1 p.2
  have hb : (fun p : Mma.Lane × Fin 2 => (call p.1).inputs.b p.2) = fun _ => (⟨1,1⟩ : PackedF16) := by
    funext p
    exact input_b p.1 p.2
  have hc : (fun p : Mma.Lane × Mma.CSlot => (call p.1).inputs.c p.2) = fun _ => (0 : ℝ) := by
    funext p
    exact input_c p.1 p.2
  rw [ha,hb,hc]
  simp [Mma.packedResults,Mma.results,Mma.unpackA,Mma.unpackB,Mma.gatherC,Mma.matrixStep,
    Mma.scatterA,Mma.scatterB,Mma.scatterC]

set_option maxHeartbeats 2000000 in
theorem mma_conditions : MmaConditions Generated.mma_probe.program launch candidate := by
  intro event mc he
  obtain ⟨lane,rfl,rfl⟩ := return_origin he
  refine ⟨participant,?_,?_,?_,arithmetic⟩
  · simp only [call_lane,participant]
  · simp only [call_lane,participant]
  · intro other
    exact ⟨participant_valid other,call_lane other,rfl,
      (call_keys other).2.2.trans (call_keys lane).2.2.symm,
      (call_keys other).2.1.trans (call_keys lane).2.1.symm,
      (call_keys other).1.trans (call_keys lane).1.symm⟩

end
end Ptx.MmaWarpTests
