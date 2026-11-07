import Ptx.Kernels.MoeExpertsWitness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Multi-CTA mixed-route expert results and unselected-plane preservation.
The legal complete execution witness is independent of universal correctness. -/
namespace Ptx.MoeExpertsMemoryTests
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeExperts Ptx.MoeExpertsLoop Ptx.MoeExpertsEvent
noncomputable section

def input : Inputs := {
  x := 0, w := 64, r := 128, h := 256, m := 3, n := 3, k := 2
  x64 := by decide, w64 := by decide, r64 := by decide, h64 := by decide
  m32 := by decide, n32 := by decide, k32 := by decide
}
def geometry : Geometry := ⟨⟨2,2,1⟩,⟨2,2,1⟩⟩
def cfg : Config := {
  input := input, geometry := geometry
  valid := by norm_num [geometry,Geometry.Valid,Dim3.Positive]
  gridZ := rfl, blockZ := rfl
  gridX32 := by decide, gridY32 := by decide, blockX32 := by decide, blockY32 := by decide
  extentX32 := by decide, extentY32 := by decide, coversRows := by decide, coversCols := by decide
  rEnd := by intro _; decide, xEnd := by intro _; decide, wEnd := by intro _; decide, hEnd := by decide
  rAligned := by intro _ _; decide, xAligned := by intro _ _ _; decide
  wAligned := by intro _ _ _; decide, hAligned := by intro _ _; decide
  separateR := by unfold WordsDisjoint; decide
  separateX := by unfold WordsDisjoint; decide
  separateW := by unfold WordsDisjoint; decide
}
def gates : Moe.Matrix := fun row gate => if row = 1 ∧ gate = 1 then 1 else 0
def x : Moe.Matrix := fun _ _ => 2
def weights : Moe.Weights := fun e _ _ => if e = 0 then 3 else 5
def initial (loc : Location) : Symbolic.Byte :=
  if loc.space = .global ∧ loc.address < 24 then .realPart .f32 2 (loc.address%4)
  else if loc.space = .global ∧ 64 ≤ loc.address ∧ loc.address < 112 then
    .realPart .f32 (if loc.address < 88 then 3 else 5) ((loc.address-64)%4)
  else if loc.space = .global ∧ 128 ≤ loc.address ∧ loc.address < 140 then
    u32Byte (Moe.selected gates ((loc.address-128)/4)) ((loc.address-128)%4)
  else .bits (byte 165)
def launch : Scalar.Launch :=
  ⟨geometry,[("X",0),("W",64),("R",128),("H",256),("M",3),("N",3),("K",2)],initial⟩
def domain : List Location := (List.range 512).map (fun address => ⟨.global,address⟩)

theorem initialized : Initialized cfg gates x weights initial := by
  refine ⟨?_,?_,?_⟩
  · intro row hr _ offset ho
    change row < 3 at hr
    change offset < 4 at ho
    change initial ⟨.global,128+4*row+offset⟩ = u32Byte (Moe.selected gates row) offset
    have hx : ¬ 128+4*row+offset < 24 := by omega
    have hw : ¬ 128+4*row+offset < 112 := by omega
    have hend : 128+4*row+offset < 140 := by omega
    have hlow : 128 ≤ 128+4*row+offset := by omega
    have hmod : (128+4*row+offset-128)%4 = offset := by omega
    have hdiv : (128+4*row+offset-128)/4 = row := by omega
    simp [initial,hx,hw,hend,hlow,hmod,hdiv]
  · intro row k hr hk _ offset ho
    change row < 3 at hr
    change k < 2 at hk
    change offset < 4 at ho
    change initial ⟨.global,0+4*(row*2+k)+offset⟩ = .realPart .f32 2 offset
    have hend : 4*(row*2+k)+offset < 24 := by omega
    have hmod : (4*(row*2+k)+offset)%4 = offset := by omega
    simp [initial,hend,hmod]
  · intro e k c he hk hc _ offset ho
    change k < 2 at hk
    change c < 3 at hc
    change offset < 4 at ho
    change initial ⟨.global,64+4*((e*2+k)*3+c)+offset⟩ = .realPart .f32 (if e = 0 then 3 else 5) offset
    have hlow : 64 ≤ 64+4*((e*2+k)*3+c)+offset := by omega
    have hx : ¬ 64+4*((e*2+k)*3+c)+offset < 24 := by omega
    have hend : 64+4*((e*2+k)*3+c)+offset < 112 := by omega
    have hmod : (64+4*((e*2+k)*3+c)+offset-64)%4 = offset := by omega
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
    · have hb : 64+4*((0*2+k)*3+c)+offset < 88 := by omega
      simp only [Nat.zero_mul,Nat.zero_add] at *
      simp [initial,hx,hlow,hend,hmod,hb]
    · have hb : ¬ 64+4*((1*2+k)*3+c)+offset < 88 := by omega
      simp only [Nat.one_mul] at *
      simp [initial,hx,hlow,hend,hmod,hb]

theorem pre : Pre cfg gates x weights launch := by
  refine ⟨rfl,?_,initialized⟩
  constructor <;> rfl
theorem covers : CoversOutput cfg gates domain := by
  intro r c hr hc offset ho
  have hidx := Moe.selected_index_bound gates hr hc
  change (Moe.selected gates r*3+r)*3+c < 18 at hidx
  exact List.mem_map.mpr ⟨256+4*((Moe.selected gates r*3+r)*3+c)+offset,List.mem_range.mpr (by omega),rfl⟩
theorem domain_global : ∀ loc ∈ domain, loc.space = .global := by
  intro loc hm
  obtain ⟨address,_,rfl⟩ := List.mem_map.mp hm
  rfl

theorem experts {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution)
    (hm : GenericMemoryConditions execution initial rf co)
    (ho : ObserverConditions execution initial rf co o) (hd : o.domain = domain) :
    Moe.Experts gates x weights 3 3 2 256 o.output :=
  (Scalar.triple_apply (correct cfg gates x weights domain covers) pre hw hm ho hd).1

theorem mixed_results {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution)
    (hm : GenericMemoryConditions execution initial rf co)
    (ho : ObserverConditions execution initial rf co o) (hd : o.domain = domain) :
    RepresentsReal .f32 o.output ⟨.global,256⟩ 12 ∧
    RepresentsReal .f32 o.output ⟨.global,304⟩ 20 ∧
    RepresentsReal .f32 o.output ⟨.global,280⟩ 12 := by
  have h := experts hw hm ho hd
  refine ⟨?_,?_,?_⟩
  · have hh := h 0 0 (by decide) (by decide)
    norm_num [Moe.output,Moe.linear,Moe.selected,gates,x,weights] at hh
    exact hh
  · have hh := h 1 0 (by decide) (by decide)
    norm_num [Moe.output,Moe.linear,Moe.selected,gates,x,weights] at hh
    exact hh
  · have hh := h 2 0 (by decide) (by decide)
    norm_num [Moe.output,Moe.linear,Moe.selected,gates,x,weights] at hh
    exact hh

theorem unselected_frame {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution)
    (hm : GenericMemoryConditions execution initial rf co)
    (ho : ObserverConditions execution initial rf co o) (hd : o.domain = domain) :
    o.output ⟨.global,268⟩ = .bits (byte 165) ∧ o.output ⟨.global,292⟩ = .bits (byte 165) := by
  have ha : ¬ SelectedByte cfg gates ⟨.global,268⟩ :=
    unselected_byte cfg gates (e := 0) (r := 1) (c := 0) (offset := 0) (by decide) (by decide) (by decide) (by norm_num [Moe.selected,gates])
  have hb : ¬ SelectedByte cfg gates ⟨.global,292⟩ :=
    unselected_byte cfg gates (e := 1) (r := 0) (c := 0) (offset := 0) (by decide) (by decide) (by decide) (by norm_num [Moe.selected,gates])
  constructor
  · simpa [launch,initial] using frame hw pre.1 pre.2.1 initialized hm ho (loc := ⟨.global,268⟩)
      (by rw [hd]; simp [domain]) ha
  · simpa [launch,initial] using frame hw pre.1 pre.2.1 initialized hm ho (loc := ⟨.global,292⟩)
      (by rw [hd]; simp [domain]) hb

theorem legal_execution : ∃ execution rf co o,
    Scalar.CheckedConditions code launch execution rf co ∧
    ObserverConditions execution initial rf co o ∧ o.domain = domain :=
  checked_nonvacuous cfg gates x weights domain domain_global launch pre

theorem legal_results_and_frame : ∃ execution rf co o,
    Scalar.CheckedConditions code launch execution rf co ∧
    ObserverConditions execution initial rf co o ∧ o.domain = domain ∧
    RepresentsReal .f32 o.output ⟨.global,256⟩ 12 ∧ RepresentsReal .f32 o.output ⟨.global,304⟩ 20 ∧
    RepresentsReal .f32 o.output ⟨.global,280⟩ 12 ∧
    o.output ⟨.global,268⟩ = .bits (byte 165) ∧ o.output ⟨.global,292⟩ = .bits (byte 165) := by
  obtain ⟨execution,rf,co,o,hw,ho,hd⟩ := legal_execution
  obtain ⟨h0,h1,h2⟩ := mixed_results hw.provenance hw.memory ho hd
  obtain ⟨hf0,hf1⟩ := unselected_frame hw.provenance hw.memory ho hd
  exact ⟨execution,rf,co,o,hw,ho,hd,h0,h1,h2,hf0,hf1⟩

theorem wrong_route_rejected {execution : Scalar.Candidate} {rf co} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id)
    (hwrong : expert t.oracle ≠ Moe.selected gates (row cfg.geometry.block t.id)) :
    ¬ GenericMemoryConditions execution initial rf co := by
  intro hm
  exact hwrong (expert_correct hw hd pre.1 pre.2.1 initialized hm ht ha)

theorem wrong_x_reply_rejected {execution : Scalar.Candidate} {rf co} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) (hwrong : FmaLoop.realReply t.oracle 1 = 3) :
    ¬ GenericMemoryConditions execution initial rf co := by
  intro hm
  have h := x_read_value hw hd pre.1 pre.2.1 initialized hm ht ha (k := 0) (by decide)
  change FmaLoop.realReply t.oracle 1 = 2 at h
  linarith

def badGates : Moe.Matrix := fun _ gate => if gate = 1 then 1 else 0
def firstId : ThreadId := ⟨.zero,.zero⟩
theorem first_valid : firstId.Valid geometry := by norm_num [firstId,geometry,ThreadId.Valid,Dim3.Within,Dim3.zero]
def badCandidate : Scalar.Candidate := canonical cfg badGates x weights launch.params pre.2.1
theorem bad_locally_complete : Scalar.WellFormed code launch badCandidate ∧ badCandidate.Complete :=
  ⟨canonical_wellFormed cfg badGates x weights pre.1 pre.2.1,canonical_complete cfg badGates x weights launch.params pre.2.1⟩
theorem bad_memory_rejected (rf : ReadsFrom) (co : Coherence) :
    ¬ GenericMemoryConditions badCandidate initial rf co := by
  apply wrong_route_rejected bad_locally_complete.1 bad_locally_complete.2
    (canonical_member cfg badGates x weights launch.params pre.2.1 first_valid)
  · simp [Active,canonical_trace_id,firstId,row,col,cfg,input,geometry,Dim3.zero]
  · simp [canonical_trace_oracle,canonical_trace_id,expertOracle_expert,Moe.selected,gates,badGates,firstId,row,cfg,geometry,Dim3.zero]

end
end Ptx.MoeExpertsMemoryTests
