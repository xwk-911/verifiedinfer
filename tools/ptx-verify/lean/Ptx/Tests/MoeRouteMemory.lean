import Ptx.Kernels.MoeRouteWitness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Multi-CTA mixed routing, tie and observed frame contracts, with independent
complete legal witnesses. Empty routing permits unaligned aliased unused data.
The three-stage expert/combine contract is not claimed by these regressions. -/
namespace Ptx.MoeRouteMemoryTests
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeRouteThread Ptx.MoeRouteEvent
noncomputable section

def input : Inputs := ⟨0,128,3,by decide,by decide,by decide⟩
def geometry : Geometry := ⟨⟨2,1,1⟩,⟨2,1,1⟩⟩
def cfg : Config := {
  input := input, geometry := geometry
  valid := by norm_num [geometry,Geometry.Valid,Dim3.Positive]
  gridY := rfl, gridZ := rfl, blockY := rfl, blockZ := rfl
  gridX32 := by decide, blockX32 := by decide, extent32 := by decide
  covers := by decide, gEnd := by decide, rEnd := by decide
  gAligned := by intro _; decide, rAligned := by intro _; decide
  separate := by unfold WordsDisjoint; decide
}
def score (i : Nat) : ℝ := if i = 0 then 4 else if i = 1 then 1 else if i = 2 then -2 else if i = 3 then 3 else 7
def gates : Moe.Matrix := fun row gate => score (2*row+gate)
def initial (loc : Location) : Symbolic.Byte :=
  if loc.space = .global ∧ loc.address < 24 then .realPart .f32 (score (loc.address/4)) (loc.address%4)
  else .bits (byte 165)
def launch : Scalar.Launch := ⟨geometry,[("G",0),("R",128),("M",3)],initial⟩
def domain : List Location := (List.range 256).map (fun address => ⟨.global,address⟩)

theorem initialized : Initialized cfg gates initial := by
  intro row gate hr hg offset ho
  change row < 3 at hr
  change gate < 2 at hg
  change offset < 4 at ho
  change initial ⟨.global,0+4*(2*row+gate)+offset⟩ = .realPart .f32 (score (2*row+gate)) offset
  have hh : 4*(2*row+gate)+offset < 24 := by omega
  have hm : (4*(2*row+gate)+offset)%4 = offset := by omega
  have hd : (4*(2*row+gate)+offset)/4 = 2*row+gate := by omega
  simp [initial,hh,hm,hd]
theorem pre : Pre cfg gates launch := by
  refine ⟨rfl,?_,initialized⟩
  constructor <;> rfl
theorem covers : CoversOutput cfg domain := by
  intro row hr offset ho
  change row < 3 at hr
  exact List.mem_map.mpr ⟨128+4*row+offset,List.mem_range.mpr (by omega),rfl⟩
theorem domain_global : ∀ loc ∈ domain, loc.space = .global := by
  intro loc hm
  obtain ⟨address,_,rfl⟩ := List.mem_map.mp hm
  rfl

theorem routes {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution)
    (hm : GenericMemoryConditions execution initial rf co)
    (ho : ObserverConditions execution initial rf co o) (hd : o.domain = domain) :
    Moe.Routes gates 3 128 o.output :=
  (Scalar.triple_apply (correct cfg gates domain covers) pre hw hm ho hd).1

theorem mixed_and_tie_routes {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution)
    (hm : GenericMemoryConditions execution initial rf co)
    (ho : ObserverConditions execution initial rf co o) (hd : o.domain = domain) :
    RepresentsU32 o.output ⟨.global,128⟩ 0 ∧ RepresentsU32 o.output ⟨.global,132⟩ 1 ∧
      RepresentsU32 o.output ⟨.global,136⟩ 0 := by
  have h := routes hw hm ho hd
  exact ⟨by simpa [Moe.selected,gates,score] using h 0 (by decide),
    by have h1 := h 1 (by decide); norm_num [Moe.selected,gates,score] at h1; exact h1,
    by simpa [Moe.selected,gates,score] using h 2 (by decide)⟩

theorem observed_frame {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution)
    (ho : ObserverConditions execution initial rf co o) (hd : o.domain = domain) :
    o.output ⟨.global,250⟩ = .bits (byte 165) := by
  have hmem : (⟨.global,250⟩ : Location) ∈ o.domain := by rw [hd]; simp [domain]
  have hout : ¬ InWords cfg.input.r cfg.input.m ⟨.global,250⟩ := by norm_num [InWords,cfg,input]
  have h := frame hw pre.1 pre.2.1 ho hmem hout
  simpa [launch,initial] using h

theorem wrong_route_rejected {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution)
    (hm : GenericMemoryConditions execution initial rf co)
    (ho : ObserverConditions execution initial rf co o) (hd : o.domain = domain) :
    ¬ RepresentsU32 o.output ⟨.global,132⟩ 0 := by
  intro hwrong
  have hright := (mixed_and_tie_routes hw hm ho hd).2.1
  have he := u32_bytes_injective (a := 1) (b := 0) (by decide) (by decide)
    (fun offset hb => (hright offset hb).symm.trans (hwrong offset hb))
  omega

theorem wrong_gate_reply_rejected {execution : Scalar.Candidate} {rf co} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id)
    (hwrong : replyReal t.oracle 0 = gates (index cfg t.id) 0+1) :
    ¬ GenericMemoryConditions execution initial rf co := by
  intro hm
  have h := gate_read_value hw hd pre.1 pre.2.1 initialized hm ht ha (gate := 0) (by decide)
  linarith

theorem legal_execution : ∃ execution rf co o,
    Scalar.CheckedConditions code launch execution rf co ∧
    ObserverConditions execution initial rf co o ∧ o.domain = domain :=
  checked_nonvacuous cfg gates domain domain_global launch pre

theorem legal_mixed_routes_and_frame : ∃ execution rf co o,
    Scalar.CheckedConditions code launch execution rf co ∧
    ObserverConditions execution initial rf co o ∧ o.domain = domain ∧
    RepresentsU32 o.output ⟨.global,128⟩ 0 ∧ RepresentsU32 o.output ⟨.global,132⟩ 1 ∧
    RepresentsU32 o.output ⟨.global,136⟩ 0 ∧ o.output ⟨.global,250⟩ = .bits (byte 165) := by
  obtain ⟨execution,rf,co,o,hw,ho,hd⟩ := legal_execution
  obtain ⟨h0,h1,h2⟩ := mixed_and_tie_routes hw.provenance hw.memory ho hd
  exact ⟨execution,rf,co,o,hw,ho,hd,h0,h1,h2,observed_frame hw.provenance ho hd⟩

def badGates : Moe.Matrix := fun row gate => if gate = 0 then gates row gate+1 else gates row gate
def firstId : ThreadId := ⟨.zero,.zero⟩
theorem first_valid : firstId.Valid geometry := by norm_num [firstId,geometry,ThreadId.Valid,Dim3.Within,Dim3.zero]
def badCandidate : Scalar.Candidate := canonical cfg badGates launch.params pre.2.1
theorem bad_locally_complete : Scalar.WellFormed code launch badCandidate ∧ badCandidate.Complete :=
  ⟨canonical_wellFormed cfg badGates pre.1 pre.2.1,canonical_complete cfg badGates launch.params pre.2.1⟩

/-- The actual source can locally consume a typed but wrong score, even without
changing the selected expert. Global value agreement must reject the candidate. -/
theorem bad_memory_rejected (rf : ReadsFrom) (co : Coherence) :
    ¬ GenericMemoryConditions badCandidate initial rf co := by
  apply wrong_gate_reply_rejected bad_locally_complete.1 bad_locally_complete.2
    (canonical_member cfg badGates launch.params pre.2.1 first_valid)
  · simp [Active,index,canonical_trace_id,firstId,col,cfg,input,geometry,Dim3.zero]
  · simp only [canonical_trace_oracle,canonical_trace_id,gateOracle,replyReal,badGates,ite_true]

def emptyInput : Inputs := ⟨1,1,0,by decide,by decide,by decide⟩
def emptyCfg : Config := {
  input := emptyInput, geometry := geometry
  valid := cfg.valid
  gridY := rfl, gridZ := rfl, blockY := rfl, blockZ := rfl
  gridX32 := by decide, blockX32 := by decide, extent32 := by decide
  covers := by decide, gEnd := by decide, rEnd := by decide
  gAligned := by intro h; change 0 < 0 at h; omega
  rAligned := by intro h; change 0 < 0 at h; omega
  separate := by unfold WordsDisjoint; decide
}
def emptyInitial : Scalar.ByteMap := fun _ => .bits (byte 165)
def emptyLaunch : Scalar.Launch := ⟨geometry,[("G",1),("R",1),("M",0)],emptyInitial⟩
theorem empty_pre : Pre emptyCfg gates emptyLaunch := by
  refine ⟨rfl,?_,?_⟩
  · constructor <;> rfl
  · intro row gate hr _
    change row < 0 at hr
    omega
theorem empty_covers : CoversOutput emptyCfg domain := by
  intro row hr
  change row < 0 at hr
  omega
theorem empty_uninitialized : ¬ RepresentsReal .f32 emptyInitial ⟨.global,1⟩ 7 := by
  intro h
  have hh := h 0 (by decide)
  cases hh
theorem empty_legal_preserves : ∃ execution rf co o,
    Scalar.CheckedConditions code emptyLaunch execution rf co ∧
    ObserverConditions execution emptyInitial rf co o ∧ o.domain = domain ∧
    ∀ loc ∈ domain, o.output loc = .bits (byte 165) := by
  obtain ⟨execution,rf,co,o,hw,ho,hd⟩ := checked_nonvacuous emptyCfg gates domain domain_global emptyLaunch empty_pre
  refine ⟨execution,rf,co,o,hw,ho,hd,?_⟩
  intro loc hl
  apply frame hw.provenance empty_pre.1 empty_pre.2.1 ho (by rw [hd]; exact hl)
  intro h
  change loc.space = .global ∧ 1 ≤ loc.address ∧ loc.address < 1+4*0 at h
  omega

end
end Ptx.MoeRouteMemoryTests
