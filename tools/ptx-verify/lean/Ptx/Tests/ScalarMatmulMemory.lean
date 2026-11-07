import Ptx.Kernels.ScalarMatmulWitness
import Mathlib.Tactic.NormNum

/-! Concrete multi-CTA contract and a separate complete consistent launch/
observation witness, plus memory/frame rejection regressions.
-/
namespace Ptx.ScalarMatmulMemoryTests
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.ScalarMatmul Ptx.ScalarMatmulEvent
noncomputable section

def input : Inputs := {
  a := 0, b := 64, c := 128, m := 3, n := 3, k := 2
  a64 := by decide, b64 := by decide, c64 := by decide
  m32 := by decide, n32 := by decide, k32 := by decide
}
def geometry : Geometry := ⟨⟨2,2,1⟩,⟨2,2,1⟩⟩
def cfg : Config := {
  input := input, geometry := geometry
  valid := by norm_num [geometry,Geometry.Valid,Dim3.Positive]
  gridZ := rfl, blockZ := rfl
  gridX32 := by decide, gridY32 := by decide, blockX32 := by decide, blockY32 := by decide
  extentX32 := by decide, extentY32 := by decide
  coversRows := by decide, coversCols := by decide
  aEnd := by decide, bEnd := by decide, cEnd := by decide
  aAligned := by decide, bAligned := by decide, cAligned := by decide
  separateA := by unfold WordsDisjoint; decide
  separateB := by unfold WordsDisjoint; decide
}
def a : Matrix := fun _ _ => 2
def b : Matrix := fun _ _ => 3
def initial (loc : Location) : Symbolic.Byte :=
  if loc.space = .global ∧ loc.address < 24 then .realPart .f32 2 (loc.address%4)
  else if loc.space = .global ∧ 64 ≤ loc.address ∧ loc.address < 88 then .realPart .f32 3 ((loc.address-64)%4)
  else .bits (byte 165)
def launch : Scalar.Launch := ⟨geometry,[("A",0),("B",64),("C",128),("M",3),("N",3),("K",2)],initial⟩
def domain : List Location := (List.range 256).map (fun address => ⟨.global,address⟩)

theorem initialized : Initialized cfg a b initial := by
  constructor
  · intro r k hr hk offset ho
    change r < 3 at hr
    change k < 2 at hk
    change offset < 4 at ho
    change initial ⟨.global,0+4*(r*2+k)+offset⟩ = .realPart .f32 2 offset
    have hh : 4*(r*2+k)+offset < 24 := by omega
    have hm : (4*(r*2+k)+offset)%4 = offset := by omega
    simp [initial,hh,hm]
  · intro k c hk hc offset ho
    change k < 2 at hk
    change c < 3 at hc
    change offset < 4 at ho
    change initial ⟨.global,64+4*(k*3+c)+offset⟩ = .realPart .f32 3 offset
    have hlow : ¬ 64+4*(k*3+c)+offset < 24 := by omega
    have hstart : 64 ≤ 64+4*(k*3+c)+offset := by omega
    have hend : 64+4*(k*3+c)+offset < 88 := by omega
    have hm : (64+4*(k*3+c)+offset-64)%4 = offset := by omega
    simp [initial,hlow,hstart,hend,hm]

theorem pre : Pre cfg a b launch := by
  refine ⟨rfl,?_,initialized⟩
  constructor <;> rfl

theorem covers : CoversOutput cfg domain := by
  intro r c hr hc offset ho
  change r < 3 at hr
  change c < 3 at hc
  apply List.mem_map.mpr
  refine ⟨128+4*(r*3+c)+offset,List.mem_range.mpr (by omega),rfl⟩

theorem contract : Scalar.Triple code (Pre cfg a b) (fun _ => domain)
    (fun launch output => Post a b cfg.input.m cfg.input.n cfg.input.k cfg.input.c output ∧
      ∀ loc ∈ domain, ¬ InWords cfg.input.c (cfg.input.m*cfg.input.n) loc → output loc = launch.initial loc) :=
  correct cfg a b domain covers

theorem observed_cell {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution)
    (hm : GenericMemoryConditions execution initial rf co)
    (ho : ObserverConditions execution initial rf co o) (hd : o.domain = domain) :
    readReal .f32 o.output (cLoc cfg 0 0) = some 12 := by
  have hresult := Scalar.triple_apply contract pre hw hm ho hd
  have hrepr := hresult.1 0 0 (by decide) (by decide)
  have hread := represents_read hrepr
  norm_num [cfg,input,a,b,prefixProduct] at hread
  exact hread

theorem observed_frame {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution)
    (ho : ObserverConditions execution initial rf co o) (hd : o.domain = domain) :
    o.output ⟨.global,250⟩ = .bits (byte 165) := by
  have hmem : (⟨.global,250⟩ : Location) ∈ o.domain := by rw [hd]; simp [domain]
  have hout : ¬ InWords cfg.input.c (cfg.input.m*cfg.input.n) ⟨.global,250⟩ := by
    norm_num [InWords,cfg,input]
  have h := frame hw pre.1 pre.2.1 ho hmem hout
  simpa [launch,initial] using h

theorem wrong_observation_rejected {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution)
    (hm : GenericMemoryConditions execution initial rf co)
    (ho : ObserverConditions execution initial rf co o) (hd : o.domain = domain) :
    readReal .f32 o.output (cLoc cfg 0 0) ≠ some 11 := by
  rw [observed_cell hw hm ho hd]
  norm_num

theorem zeroed_frame_rejected {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution)
    (ho : ObserverConditions execution initial rf co o) (hd : o.domain = domain) :
    o.output ⟨.global,250⟩ ≠ .bits (byte 0) := by
  rw [observed_frame hw ho hd]
  intro he
  exact (show byte 165 ≠ byte 0 by decide) (Symbolic.Byte.bits.inj he)

theorem wrong_input_reply_rejected {execution : Scalar.Candidate} {rf co} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id)
    (hwrong : ScalarMatmulLoop.realReply t.oracle 0 = 17) :
    ¬ GenericMemoryConditions execution initial rf co := by
  intro hm
  have h := a_read_value hw hd pre.1 pre.2.1 initialized hm ht ha (k := 0) (by decide)
  norm_num [a,hwrong] at h

theorem empty_input_may_alias_output : WordsDisjoint 128 0 128 9 := by unfold WordsDisjoint; decide
theorem nonempty_input_overlap_rejected : ¬ WordsDisjoint 128 6 128 9 := by unfold WordsDisjoint; decide

theorem domain_global : ∀ loc ∈ domain, loc.space = .global := by
  intro loc hm
  obtain ⟨address,_,rfl⟩ := List.mem_map.mp hm
  rfl

theorem legal_execution : ∃ execution rf co o,
    Scalar.WellFormed code launch execution ∧
    GenericMemoryConditions execution initial rf co ∧
    ObserverConditions execution initial rf co o ∧ o.domain = domain :=
  nonvacuous cfg a b domain domain_global launch pre

theorem legal_execution_observes_twelve : ∃ execution rf co o,
    Scalar.WellFormed code launch execution ∧
    GenericMemoryConditions execution initial rf co ∧
    ObserverConditions execution initial rf co o ∧ o.domain = domain ∧
    readReal .f32 o.output (cLoc cfg 0 0) = some 12 ∧
    o.output ⟨.global,250⟩ = .bits (byte 165) := by
  obtain ⟨execution,rf,co,o,hw,hm,ho,hd⟩ := legal_execution
  exact ⟨execution,rf,co,o,hw,hm,ho,hd,observed_cell hw hm ho hd,observed_frame hw ho hd⟩

def zeroInput : Inputs := {
  a := 128, b := 128, c := 128, m := 3, n := 3, k := 0
  a64 := by decide, b64 := by decide, c64 := by decide
  m32 := by decide, n32 := by decide, k32 := by decide
}
def zeroCfg : Config := {
  input := zeroInput, geometry := geometry
  valid := cfg.valid
  gridZ := rfl, blockZ := rfl
  gridX32 := by decide, gridY32 := by decide, blockX32 := by decide, blockY32 := by decide
  extentX32 := by decide, extentY32 := by decide
  coversRows := by decide, coversCols := by decide
  aEnd := by decide, bEnd := by decide, cEnd := by decide
  aAligned := by decide, bAligned := by decide, cAligned := by decide
  separateA := by unfold WordsDisjoint; decide
  separateB := by unfold WordsDisjoint; decide
}
def zeroLaunch : Scalar.Launch :=
  ⟨geometry,[("A",128),("B",128),("C",128),("M",3),("N",3),("K",0)],initial⟩

theorem zero_pre : Pre zeroCfg a b zeroLaunch := by
  refine ⟨rfl,?_,?_,?_⟩
  · constructor <;> rfl
  · intro r k _ hk
    have hh : k < 0 := hk
    omega
  · intro k c hk _
    have hh : k < 0 := hk
    omega

theorem zero_covers : CoversOutput zeroCfg domain := by
  simpa only [CoversOutput,zeroCfg,zeroInput,cfg,input,cLoc] using covers

/-- K=0 needs no input representation, permits A=B=C, and has a legal completed
global witness that writes zero. No pre-initialized zero output is assumed. -/
theorem zero_inner_legal_output : ∃ execution rf co o,
    Scalar.WellFormed code zeroLaunch execution ∧
    GenericMemoryConditions execution initial rf co ∧
    ObserverConditions execution initial rf co o ∧ o.domain = domain ∧
    readReal .f32 o.output (cLoc zeroCfg 0 0) = some 0 := by
  obtain ⟨execution,rf,co,o,hw,hm,ho,hd⟩ := nonvacuous zeroCfg a b domain domain_global zeroLaunch zero_pre
  refine ⟨execution,rf,co,o,hw,hm,ho,hd,?_⟩
  have hc := Scalar.triple_apply (correct zeroCfg a b domain zero_covers) zero_pre hw hm ho hd
  exact represents_read (hc.1 0 0 (by decide) (by decide))

end
end Ptx.ScalarMatmulMemoryTests
