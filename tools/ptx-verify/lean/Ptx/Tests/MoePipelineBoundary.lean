import Ptx.Tests.MoePipeline
import Ptx.Tests.MoeExpertsBoundary

/-! Whole-stream K=0 and empty outer dimensions, without initializing dead
regions. N=0 still executes route, so its live R/G bases remain aligned. -/
namespace Ptx.MoePipelineTests
open Ptx.ISA Ptx.Scalar Ptx.Scalar.Stream
open Ptx.MoeExpertsMemoryTests (gates x weights)
noncomputable section

def zeroCfg : MoePipeline.Config := {cfg with
  experts := MoeExpertsMemoryTests.zeroCfg
  expertParams := MoeExpertsMemoryTests.zeroLaunch.params
  expertBindings := MoeExpertsMemoryTests.zero_pre.2.1
  separateXR := by intro _; unfold WordsDisjoint; decide
  separateWR := by intro _; unfold WordsDisjoint; decide
}
theorem zero_ready : MoePipeline.Pre zeroCfg gates x weights heap := by
  refine ⟨input_ready.1,?_,?_⟩
  · intro r k hr hk
    change k < 0 at hk
    omega
  · intro e k c he hk
    change k < 0 at hk
    omega
theorem zero_legal : ∃ after, Runs (MoePipeline.commands zeroCfg) heap after ∧ Represents .f32 after 396 0 := by
  obtain ⟨after,hr⟩ := MoePipeline.nonvacuous zeroCfg gates x weights heap zero_ready
  have hp := MoePipeline.correct zeroCfg gates x weights heap after zero_ready hr
  refine ⟨after,hr,?_⟩
  simpa [MoePipeline.values,Moe.output,Moe.linear,zeroCfg,cfg,MoeExpertsMemoryTests.zeroCfg,MoeExpertsMemoryTests.zeroInput,
    MoeExpertsMemoryTests.input,MoeCombineEvent.yLoc,combineCfg,combineInput] using hp.1 1 0 (by decide) (by decide)

def emptyR (zeroCols : Bool) : Nat := if zeroCols then 128 else 1
def emptyG (zeroCols : Bool) : Nat := if zeroCols then 512 else 1
def emptyExpertInput (zeroCols : Bool) : MoeExperts.Inputs :=
  {MoeExpertsMemoryTests.emptyInput zeroCols with r := emptyR zeroCols,r64 := by cases zeroCols <;> decide}
def emptyExpertCfg (zeroCols : Bool) : MoeExpertsEvent.Config := {MoeExpertsMemoryTests.emptyCfg zeroCols with
  input := emptyExpertInput zeroCols
  rEnd := by cases zeroCols <;> decide
  rAligned := by cases zeroCols <;> decide
  separateR := by cases zeroCols <;> unfold WordsDisjoint <;> decide
}
def emptyCombineInput (zeroCols : Bool) : MoeCombine.Inputs := {
  r := emptyR zeroCols,h := 1,y := 1,m := if zeroCols then 3 else 0,n := if zeroCols then 0 else 3
  r64 := by cases zeroCols <;> decide,h64 := by decide,y64 := by decide
  m32 := by cases zeroCols <;> decide,n32 := by cases zeroCols <;> decide
}
def emptyCombineCfg (zeroCols : Bool) : MoeCombineEvent.Config := {combineCfg with
  input := emptyCombineInput zeroCols
  coversRows := by cases zeroCols <;> decide,coversCols := by cases zeroCols <;> decide
  rEnd := by cases zeroCols <;> decide,hEnd := by cases zeroCols <;> decide,yEnd := by cases zeroCols <;> decide
  rAligned := by cases zeroCols <;> decide,hAligned := by cases zeroCols <;> decide,yAligned := by cases zeroCols <;> decide
  separateR := by cases zeroCols <;> unfold WordsDisjoint <;> decide
  separateH := by cases zeroCols <;> unfold WordsDisjoint <;> decide
}
def emptyRouteInput (zeroCols : Bool) : MoeRouteThread.Inputs := {
  g := emptyG zeroCols,r := emptyR zeroCols,m := if zeroCols then 3 else 0
  g64 := by cases zeroCols <;> decide,r64 := by cases zeroCols <;> decide,m32 := by cases zeroCols <;> decide
}
def emptyRouteCfg (zeroCols : Bool) : MoeRouteEvent.Config := {routeCfg with
  input := emptyRouteInput zeroCols
  covers := by cases zeroCols <;> decide,gEnd := by cases zeroCols <;> decide,rEnd := by cases zeroCols <;> decide
  gAligned := by cases zeroCols <;> decide,rAligned := by cases zeroCols <;> decide
  separate := by cases zeroCols <;> unfold WordsDisjoint <;> decide
}
def emptyCfg (zeroCols : Bool) : MoePipeline.Config := {cfg with
  route := emptyRouteCfg zeroCols,experts := emptyExpertCfg zeroCols,combine := emptyCombineCfg zeroCols
  routeRows := rfl,combineRows := rfl,combineCols := rfl,routeR := rfl,combineR := rfl,combineH := rfl
  separateXR := by cases zeroCols <;> decide,separateWR := by cases zeroCols <;> decide
  routeParams := [("G",emptyG zeroCols),("R",emptyR zeroCols),("M",if zeroCols then 3 else 0)]
  expertParams := [("X",1),("W",1),("R",emptyR zeroCols),("H",1),("M",if zeroCols then 3 else 0),
    ("N",if zeroCols then 0 else 3),("K",2^32-1)]
  combineParams := [("R",emptyR zeroCols),("H",1),("Y",1),("M",if zeroCols then 3 else 0),("N",if zeroCols then 0 else 3)]
  routeBindings := by constructor <;> rfl
  expertBindings := by constructor <;> rfl
  combineBindings := by constructor <;> rfl
  routeDomain := domain,expertDomain := domain,combineDomain := domain
  routeGlobal := by intro loc hl; obtain ⟨_,_,rfl⟩ := List.mem_map.mp hl; rfl
  expertGlobal := by intro loc hl; obtain ⟨_,_,rfl⟩ := List.mem_map.mp hl; rfl
  combineGlobal := by intro loc hl; obtain ⟨_,_,rfl⟩ := List.mem_map.mp hl; rfl
  routeCover := by
    intro r hr offset ho
    cases zeroCols with
    | false => change r < 0 at hr; omega
    | true =>
      change r < 3 at hr
      exact List.mem_map.mpr ⟨128+4*r+offset,List.mem_range.mpr (by omega),rfl⟩
  expertCover := by
    intro g r c hr hc
    change r < (if zeroCols then 3 else 0) at hr
    change c < (if zeroCols then 0 else 3) at hc
    cases zeroCols <;> simp_all
  combineCover := by
    intro r c hr hc
    change r < (if zeroCols then 3 else 0) at hr
    change c < (if zeroCols then 0 else 3) at hc
    cases zeroCols <;> simp_all
}
def emptyHeap (zeroCols : Bool) : Heap := if zeroCols then heap else fun _ => .bits (byte 165)
theorem empty_ready (zeroCols : Bool) : MoePipeline.Pre (emptyCfg zeroCols) gates x weights (emptyHeap zeroCols) := by
  refine ⟨?_,?_,?_⟩
  · intro r g hr hg
    cases zeroCols with
    | false => change r < 0 at hr; omega
    | true => exact input_ready.1 r g hr hg
  · intro r k hr hk hn
    change r < (if zeroCols then 3 else 0) at hr
    change 0 < (if zeroCols then 0 else 3) at hn
    cases zeroCols <;> simp_all
  · intro e k c he hk hc hm
    change c < (if zeroCols then 0 else 3) at hc
    change 0 < (if zeroCols then 3 else 0) at hm
    cases zeroCols <;> simp_all
theorem empty_legal (zeroCols : Bool) : ∃ after, Runs (MoePipeline.commands (emptyCfg zeroCols)) (emptyHeap zeroCols) after :=
  MoePipeline.nonvacuous (emptyCfg zeroCols) gates x weights (emptyHeap zeroCols) (empty_ready zeroCols)
theorem zero_rows_preserves_all : ∃ after, Runs (MoePipeline.commands (emptyCfg false)) (emptyHeap false) after ∧
    ∀ address, after address = .bits (byte 165) := by
  obtain ⟨after,hr⟩ := empty_legal false
  have hp := MoePipeline.correct (emptyCfg false) gates x weights (emptyHeap false) after (empty_ready false) hr
  refine ⟨after,hr,?_⟩
  intro address
  apply hp.2 address
  rintro (h | h | h)
  · norm_num [InWords,emptyCfg,emptyRouteCfg,emptyRouteInput] at h <;> omega
  · obtain ⟨r,c,offset,hr,_,_⟩ := h
    change r < 0 at hr
    omega
  · norm_num [InWords,emptyCfg,emptyCombineCfg,emptyCombineInput] at h <;> omega

end
end Ptx.MoePipelineTests
