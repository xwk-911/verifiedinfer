import Ptx.Kernels.MoePipeline
import Ptx.Tests.MoeExpertsMemory
import Ptx.Tests.MoeRouteMemory

/-! Three real source stages with poisoned R/H/Y at entry, mixed routes, two
dimensional expert/combine launches and an independent legal stream witness. -/
namespace Ptx.MoePipelineTests
open Ptx.ISA Ptx.Scalar Ptx.Scalar.Stream
open Ptx.MoeExpertsMemoryTests (gates x weights)
noncomputable section

def routeInput : MoeRouteThread.Inputs := ⟨512,128,3,by decide,by decide,by decide⟩
def routeCfg : MoeRouteEvent.Config := {
  input := routeInput,geometry := MoeRouteMemoryTests.geometry,valid := MoeRouteMemoryTests.cfg.valid
  gridY := rfl,gridZ := rfl,blockY := rfl,blockZ := rfl
  gridX32 := by decide,blockX32 := by decide,extent32 := by decide,covers := by decide
  gEnd := by decide,rEnd := by decide,gAligned := by intro _; decide,rAligned := by intro _; decide
  separate := by unfold WordsDisjoint; decide
}
def combineInput : MoeCombine.Inputs := ⟨128,256,384,3,3,by decide,by decide,by decide,by decide,by decide⟩
def combineCfg : MoeCombineEvent.Config := {
  input := combineInput,geometry := MoeExpertsMemoryTests.geometry,valid := MoeExpertsMemoryTests.cfg.valid
  gridZ := rfl,blockZ := rfl
  gridX32 := by decide,gridY32 := by decide,blockX32 := by decide,blockY32 := by decide
  extentX32 := by decide,extentY32 := by decide,coversRows := by decide,coversCols := by decide
  rEnd := by intro _; decide,hEnd := by decide,yEnd := by decide
  rAligned := by intro _ _; decide,hAligned := by intro _ _; decide,yAligned := by intro _ _; decide
  separateR := by unfold WordsDisjoint; decide,separateH := by unfold WordsDisjoint; decide
}
def domain : List Location := (List.range 1024).map (fun address => ⟨.global,address⟩)
def shared : SharedInitial := fun _ _ => .bits (byte 23)
def cfg : MoePipeline.Config := {
  route := routeCfg,experts := MoeExpertsMemoryTests.cfg,combine := combineCfg
  routeRows := rfl,combineRows := rfl,combineCols := rfl,routeR := rfl,combineR := rfl,combineH := rfl
  separateXR := by intro _; unfold WordsDisjoint; decide,separateWR := by intro _; unfold WordsDisjoint; decide
  routeParams := [("G",512),("R",128),("M",3)]
  expertParams := MoeExpertsMemoryTests.launch.params
  combineParams := [("R",128),("H",256),("Y",384),("M",3),("N",3)]
  routeBindings := by constructor <;> rfl
  expertBindings := MoeExpertsMemoryTests.pre.2.1
  combineBindings := by constructor <;> rfl
  routeShared := shared,expertShared := shared,combineShared := shared
  routeDomain := domain,expertDomain := domain,combineDomain := domain
  routeCover := by
    intro r hr offset ho
    change r < 3 at hr
    exact List.mem_map.mpr ⟨128+4*r+offset,List.mem_range.mpr (by omega),rfl⟩
  expertCover := by
    intro g r c hr hc offset ho
    have hi := Moe.selected_index_bound g hr hc
    change (Moe.selected g r*3+r)*3+c < 18 at hi
    exact List.mem_map.mpr ⟨256+4*((Moe.selected g r*3+r)*3+c)+offset,List.mem_range.mpr (by omega),rfl⟩
  combineCover := by
    intro r c hr hc offset ho
    change r < 3 at hr
    change c < 3 at hc
    exact List.mem_map.mpr ⟨384+4*(r*3+c)+offset,List.mem_range.mpr (by omega),rfl⟩
  routeGlobal := by intro loc hl; obtain ⟨_,_,rfl⟩ := List.mem_map.mp hl; rfl
  expertGlobal := by intro loc hl; obtain ⟨_,_,rfl⟩ := List.mem_map.mp hl; rfl
  combineGlobal := by intro loc hl; obtain ⟨_,_,rfl⟩ := List.mem_map.mp hl; rfl
}

def heap (address : Nat) : Symbolic.Byte :=
  if 512 ≤ address ∧ address < 536 then
    .realPart .f32 (gates ((address-512)/8) (((address-512)/4)%2)) ((address-512)%4)
  else if address < 128 then MoeExpertsMemoryTests.initial ⟨.global,address⟩ else .bits (byte 165)

theorem input_ready : MoePipeline.Pre cfg gates x weights heap := by
  refine ⟨?_,?_,?_⟩
  · intro r g hr hg offset ho
    change r < 3 at hr
    change g < 2 at hg
    change offset < 4 at ho
    change heap (512+4*(2*r+g)+offset) = .realPart .f32 (gates r g) offset
    have hlo : 512 ≤ 512+4*(2*r+g)+offset := by omega
    have hhi : 512+4*(2*r+g)+offset < 536 := by omega
    have hrdiv : (512+4*(2*r+g)+offset-512)/8 = r := by omega
    have hgdiv : ((512+4*(2*r+g)+offset-512)/4)%2 = g := by omega
    have hmod : (512+4*(2*r+g)+offset-512)%4 = offset := by omega
    simp [heap,hlo,hhi,hrdiv,hgdiv,hmod]
  · intro r k hr hk hn offset ho
    have hi := MoeExpertsMemoryTests.initialized.2.1 r k hr hk hn offset ho
    change r < 3 at hr
    change k < 2 at hk
    change offset < 4 at ho
    change heap (0+4*(r*2+k)+offset) = _
    have hlow : 0+4*(r*2+k)+offset < 128 := by omega
    have hnot : ¬ (512 ≤ 0+4*(r*2+k)+offset ∧ 0+4*(r*2+k)+offset < 536) := by omega
    simpa only [heap,hnot,ite_false,hlow,ite_true,MoeExpertsEvent.xLoc,MoeExpertsMemoryTests.cfg,MoeExpertsMemoryTests.input,Location.add] using hi
  · intro e k c he hk hc hm offset ho
    have hi := MoeExpertsMemoryTests.initialized.2.2 e k c he hk hc hm offset ho
    change k < 2 at hk
    change c < 3 at hc
    change offset < 4 at ho
    change heap (64+4*((e*2+k)*3+c)+offset) = _
    have hlow : 64+4*((e*2+k)*3+c)+offset < 128 := by omega
    have hnot : ¬ (512 ≤ 64+4*((e*2+k)*3+c)+offset ∧ 64+4*((e*2+k)*3+c)+offset < 536) := by omega
    simpa only [heap,hnot,ite_false,hlow,ite_true,MoeExpertsEvent.wLoc,MoeExpertsMemoryTests.cfg,MoeExpertsMemoryTests.input,Location.add] using hi

theorem no_route_initialization : ¬ RepresentsWord heap 132 1 := by
  intro h
  have hh := h 0 (by decide)
  change Symbolic.Byte.bits (byte 165) = Symbolic.Byte.bits (byte 1) at hh
  exact (show byte 165 ≠ byte 1 by decide) (Symbolic.Byte.bits.inj hh)
theorem no_expert_initialization : ¬ Represents .f32 heap 304 20 := by
  intro h
  have hh := h 0 (by decide)
  cases hh
theorem no_output_initialization : ¬ Represents .f32 heap 396 20 := by
  intro h
  have hh := h 0 (by decide)
  cases hh

theorem mixed_results {after : Heap} (hr : Runs (MoePipeline.commands cfg) heap after) :
    Represents .f32 after 384 12 ∧ Represents .f32 after 396 20 ∧ Represents .f32 after 408 12 := by
  have hp := MoePipeline.correct cfg gates x weights heap after input_ready hr
  refine ⟨?_,?_,?_⟩
  · have h := hp.1 0 0 (by decide) (by decide)
    norm_num [MoePipeline.values,Moe.output,Moe.linear,Moe.selected,gates,x,weights,MoeCombineEvent.yLoc,cfg,combineCfg,combineInput,
      MoeExpertsMemoryTests.cfg,MoeExpertsMemoryTests.input] at h
    exact h
  · have h := hp.1 1 0 (by decide) (by decide)
    norm_num [MoePipeline.values,Moe.output,Moe.linear,Moe.selected,gates,x,weights,MoeCombineEvent.yLoc,cfg,combineCfg,combineInput,
      MoeExpertsMemoryTests.cfg,MoeExpertsMemoryTests.input] at h
    exact h
  · have h := hp.1 2 0 (by decide) (by decide)
    norm_num [MoePipeline.values,Moe.output,Moe.linear,Moe.selected,gates,x,weights,MoeCombineEvent.yLoc,cfg,combineCfg,combineInput,
      MoeExpertsMemoryTests.cfg,MoeExpertsMemoryTests.input] at h
    exact h

theorem preserved_unselected {after : Heap} (hr : Runs (MoePipeline.commands cfg) heap after) :
    after 268 = .bits (byte 165) ∧ after 292 = .bits (byte 165) ∧ after 1000 = .bits (byte 165) := by
  have hp := (MoePipeline.correct cfg gates x weights heap after input_ready hr).2
  have outsideR (a : Nat) (ha : 140 ≤ a) : ¬ InWords cfg.route.input.r cfg.route.input.m ⟨.global,a⟩ := by
    simp only [InWords,cfg,routeCfg,routeInput]
    omega
  have outsideY (a : Nat) (ha : a < 384 ∨ 420 ≤ a) : ¬ InWords cfg.combine.input.y (cfg.combine.input.m*cfg.combine.input.n) ⟨.global,a⟩ := by
    simp only [InWords,cfg,combineCfg,combineInput]
    omega
  have hs0 : ¬ MoeExpertsEvent.SelectedByte cfg.experts gates ⟨.global,268⟩ :=
    MoeExpertsEvent.unselected_byte cfg.experts gates (e := 0) (r := 1) (c := 0) (offset := 0)
      (by decide) (by decide) (by decide) (by norm_num [Moe.selected,gates])
  have hs1 : ¬ MoeExpertsEvent.SelectedByte cfg.experts gates ⟨.global,292⟩ :=
    MoeExpertsEvent.unselected_byte cfg.experts gates (e := 1) (r := 0) (c := 0) (offset := 0)
      (by decide) (by decide) (by decide) (by norm_num [Moe.selected,gates])
  have hs2 : ¬ MoeExpertsEvent.SelectedByte cfg.experts gates ⟨.global,1000⟩ := by
    intro h
    have hh := MoePipeline.selected_region h
    norm_num [InWords,cfg,MoeExpertsMemoryTests.cfg,MoeExpertsMemoryTests.input] at hh
  refine ⟨?_,?_,?_⟩
  · simpa [heap] using hp 268 (fun h => h.elim (outsideR 268 (by decide)) (fun h => h.elim hs0 (outsideY 268 (by decide))))
  · simpa [heap] using hp 292 (fun h => h.elim (outsideR 292 (by decide)) (fun h => h.elim hs1 (outsideY 292 (by decide))))
  · simpa [heap] using hp 1000 (fun h => h.elim (outsideR 1000 (by decide)) (fun h => h.elim hs2 (outsideY 1000 (by decide))))

theorem legal_pipeline : ∃ after, Runs (MoePipeline.commands cfg) heap after ∧
    Represents .f32 after 384 12 ∧ Represents .f32 after 396 20 ∧ Represents .f32 after 408 12 ∧
    after 268 = .bits (byte 165) ∧ after 292 = .bits (byte 165) ∧ after 1000 = .bits (byte 165) := by
  obtain ⟨after,hr⟩ := MoePipeline.nonvacuous cfg gates x weights heap input_ready
  obtain ⟨h0,h1,h2⟩ := mixed_results hr
  obtain ⟨f0,f1,f2⟩ := preserved_unselected hr
  exact ⟨after,hr,h0,h1,h2,f0,f1,f2⟩

theorem stale_heap_rejected : ¬ Runs (MoePipeline.commands cfg) heap heap := by
  intro h
  exact no_output_initialization (mixed_results h).2.1

end
end Ptx.MoePipelineTests
