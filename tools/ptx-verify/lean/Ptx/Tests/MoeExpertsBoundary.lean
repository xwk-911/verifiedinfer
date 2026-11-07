import Ptx.Tests.MoeExpertsMemory

/-! Empty/dead footprints are tested without fabricated X/W initialization.
K=0 aliases unused X/W with H; either outer dimension zero permits all bases
unaligned and aliased, even with the largest u32 inner dimension. -/
namespace Ptx.MoeExpertsMemoryTests
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeExperts Ptx.MoeExpertsLoop Ptx.MoeExpertsEvent
noncomputable section

def zeroInput : Inputs := {input with x := 256,w := 256,k := 0,x64 := by decide,w64 := by decide,k32 := by decide}
def zeroCfg : Config := {
  input := zeroInput, geometry := geometry, valid := cfg.valid
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
def zeroLaunch : Scalar.Launch :=
  ⟨geometry,[("X",256),("W",256),("R",128),("H",256),("M",3),("N",3),("K",0)],initial⟩
theorem zero_pre : Pre zeroCfg gates x weights zeroLaunch := by
  refine ⟨rfl,?_,initialized.1,?_,?_⟩
  · constructor <;> rfl
  · intro r k hr hk
    change k < 0 at hk
    omega
  · intro e k c he hk
    change k < 0 at hk
    omega
theorem zero_unused_uninitialized (value : ℝ) : ¬ RepresentsReal .f32 initial ⟨.global,256⟩ value := by
  intro hi
  have h := hi 0 (by decide)
  norm_num [initial,Location.add] at h
theorem zero_covers : CoversOutput zeroCfg gates domain := covers
theorem zero_legal : ∃ execution rf co o,
    Scalar.CheckedConditions code zeroLaunch execution rf co ∧
    ObserverConditions execution initial rf co o ∧ o.domain = domain ∧
    RepresentsReal .f32 o.output ⟨.global,304⟩ 0 := by
  obtain ⟨execution,rf,co,o,hw,ho,hd⟩ := checked_nonvacuous zeroCfg gates x weights domain domain_global zeroLaunch zero_pre
  have hout := (Scalar.triple_apply (correct zeroCfg gates x weights domain zero_covers)
    zero_pre hw.provenance hw.memory ho hd).1 1 0 (by decide) (by decide)
  refine ⟨execution,rf,co,o,hw,ho,hd,?_⟩
  simpa [Moe.output,Moe.linear,Moe.selected,gates,zeroCfg,zeroInput,input] using hout

def emptyInput (zeroCols : Bool) : Inputs := {
  x := 1,w := 1,r := 1,h := 1
  m := if zeroCols then 3 else 0, n := if zeroCols then 0 else 3, k := 2^32-1
  x64 := by decide,w64 := by decide,r64 := by decide,h64 := by decide
  m32 := by cases zeroCols <;> decide,n32 := by cases zeroCols <;> decide,k32 := by decide
}
def emptyCfg (zeroCols : Bool) : Config := {
  input := emptyInput zeroCols,geometry := geometry,valid := cfg.valid
  gridZ := rfl,blockZ := rfl
  gridX32 := by decide,gridY32 := by decide,blockX32 := by decide,blockY32 := by decide
  extentX32 := by decide,extentY32 := by decide
  coversRows := by cases zeroCols <;> decide,coversCols := by cases zeroCols <;> decide
  rEnd := by cases zeroCols <;> decide,xEnd := by cases zeroCols <;> decide
  wEnd := by cases zeroCols <;> decide,hEnd := by cases zeroCols <;> decide
  rAligned := by cases zeroCols <;> decide,xAligned := by cases zeroCols <;> decide
  wAligned := by cases zeroCols <;> decide,hAligned := by cases zeroCols <;> decide
  separateR := by cases zeroCols <;> unfold WordsDisjoint <;> decide
  separateX := by cases zeroCols <;> unfold WordsDisjoint <;> decide
  separateW := by cases zeroCols <;> unfold WordsDisjoint <;> decide
}
def emptyInitial : Scalar.ByteMap := fun _ => .bits (byte 165)
def emptyLaunch (zeroCols : Bool) : Scalar.Launch :=
  ⟨geometry,[("X",1),("W",1),("R",1),("H",1),("M",if zeroCols then 3 else 0),
    ("N",if zeroCols then 0 else 3),("K",2^32-1)],emptyInitial⟩
theorem empty_pre (zeroCols : Bool) : Pre (emptyCfg zeroCols) gates x weights (emptyLaunch zeroCols) := by
  refine ⟨rfl,?_,?_,?_,?_⟩
  · constructor <;> rfl
  · intro r hr hn
    cases zeroCols <;> simp_all [emptyCfg,emptyInput]
  · intro r k hr _ hn
    cases zeroCols <;> simp_all [emptyCfg,emptyInput]
  · intro e k c he hk hc hm
    cases zeroCols <;> simp_all [emptyCfg,emptyInput]
theorem empty_legal_preserves (zeroCols : Bool) : ∃ execution rf co o,
    Scalar.CheckedConditions code (emptyLaunch zeroCols) execution rf co ∧
    ObserverConditions execution emptyInitial rf co o ∧ o.domain = domain ∧
    ∀ loc ∈ domain, o.output loc = .bits (byte 165) := by
  obtain ⟨execution,rf,co,o,hw,ho,hd⟩ :=
    checked_nonvacuous (emptyCfg zeroCols) gates x weights domain domain_global (emptyLaunch zeroCols) (empty_pre zeroCols)
  refine ⟨execution,rf,co,o,hw,ho,hd,?_⟩
  intro loc hl
  apply frame hw.provenance (empty_pre zeroCols).1 (empty_pre zeroCols).2.1 (empty_pre zeroCols).2.2 hw.memory ho
    (by rw [hd]; exact hl)
  rintro ⟨r,c,offset,hr,hc,_⟩
  cases zeroCols <;> simp_all [emptyCfg,emptyInput]

end
end Ptx.MoeExpertsMemoryTests
