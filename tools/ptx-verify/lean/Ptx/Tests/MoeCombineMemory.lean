import Ptx.Tests.MoePipeline

/-! Standalone gather consistency witnesses, including typed-but-wrong input
oracles that finish locally and are rejected globally. -/
namespace Ptx.MoeCombineMemoryTests
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeCombine Ptx.MoeCombineEvent
open Ptx.MoeExpertsMemoryTests (gates)
noncomputable section

def cfg : Config := MoePipelineTests.combineCfg
def values : Moe.Matrix := fun r _ => if r = 1 then 20 else 12
def initial (loc : Location) : Symbolic.Byte :=
  if loc.space = .global ∧ 128 ≤ loc.address ∧ loc.address < 140 then
    u32Byte (Moe.selected gates ((loc.address-128)/4)) ((loc.address-128)%4)
  else if loc.space = .global ∧ 256 ≤ loc.address ∧ loc.address < 328 ∧
      (loc.address-256)/36 = Moe.selected gates (((loc.address-256)/12)%3) then
    .realPart .f32 (values (((loc.address-256)/12)%3) (((loc.address-256)/4)%3)) ((loc.address-256)%4)
  else .bits (byte 165)
def launch : Scalar.Launch := ⟨cfg.geometry,[("R",128),("H",256),("Y",384),("M",3),("N",3)],initial⟩
def domain : List Location := MoePipelineTests.domain

theorem initialized : Initialized cfg gates values initial := by
  constructor
  · intro r hr _ offset ho
    change r < 3 at hr
    change offset < 4 at ho
    change initial ⟨.global,128+4*r+offset⟩ = u32Byte (Moe.selected gates r) offset
    have hlo : 128 ≤ 128+4*r+offset := by omega
    have hhi : 128+4*r+offset < 140 := by omega
    have hd : (128+4*r+offset-128)/4 = r := by omega
    have hm : (128+4*r+offset-128)%4 = offset := by omega
    simp [initial,hlo,hhi,hd,hm]
  · intro r c hr hc offset ho
    change r < 3 at hr
    change c < 3 at hc
    change offset < 4 at ho
    let e := Moe.selected gates r
    have he : e < 2 := Moe.selected_bound gates r
    change initial ⟨.global,256+4*((e*3+r)*3+c)+offset⟩ = .realPart .f32 (values r c) offset
    have hlo : 256 ≤ 256+4*((e*3+r)*3+c)+offset := by omega
    have hhi : 256+4*((e*3+r)*3+c)+offset < 328 := by omega
    have hn : ¬ 256+4*((e*3+r)*3+c)+offset < 140 := by omega
    have hre : ((256+4*((e*3+r)*3+c)+offset-256)/12)%3 = r := by omega
    have hce : ((256+4*((e*3+r)*3+c)+offset-256)/4)%3 = c := by omega
    have hee : (256+4*((e*3+r)*3+c)+offset-256)/36 = e := by omega
    have hm : (256+4*((e*3+r)*3+c)+offset-256)%4 = offset := by omega
    simp [initial,hlo,hhi,hn,hre,hce,hee,hm,e]
theorem pre : Pre cfg gates values launch := by
  refine ⟨rfl,?_,initialized⟩
  constructor <;> rfl
theorem covers : CoversOutput cfg domain := by
  intro r c hr hc offset ho
  change r < 3 at hr
  change c < 3 at hc
  exact List.mem_map.mpr ⟨384+4*(r*3+c)+offset,List.mem_range.mpr (by omega),rfl⟩
theorem domain_global : ∀ loc ∈ domain, loc.space = .global := by
  intro loc hm
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp hm
  rfl

theorem legal_execution : ∃ execution rf co o,
    Scalar.CheckedConditions code launch execution rf co ∧
    ObserverConditions execution initial rf co o ∧ o.domain = domain :=
  checked_nonvacuous cfg gates values domain domain_global launch pre
theorem legal_results : ∃ execution rf co o,
    Scalar.CheckedConditions code launch execution rf co ∧
    ObserverConditions execution initial rf co o ∧ o.domain = domain ∧
    RepresentsReal .f32 o.output ⟨.global,396⟩ 20 ∧ o.output ⟨.global,268⟩ = .bits (byte 165) := by
  obtain ⟨execution,rf,co,o,hw,ho,hd⟩ := legal_execution
  have hp := Scalar.triple_apply (correct cfg gates values domain covers) pre hw.provenance hw.memory ho hd
  refine ⟨execution,rf,co,o,hw,ho,hd,?_,?_⟩
  · simpa [Post,yLoc,cfg,MoePipelineTests.combineCfg,MoePipelineTests.combineInput,values] using hp.1 1 0 (by decide) (by decide)
  · have hloc : (⟨.global,268⟩ : Location) ∈ domain := by simp [domain,MoePipelineTests.domain]
    have hout : ¬ InWords cfg.input.y (cfg.input.m*cfg.input.n) ⟨.global,268⟩ := by
      norm_num [InWords,cfg,MoePipelineTests.combineCfg,MoePipelineTests.combineInput]
    have hf := hp.2 _ hloc hout
    norm_num [launch,initial,Moe.selected,gates] at hf
    exact hf

def firstId : ThreadId := ⟨.zero,.zero⟩
theorem first_valid : firstId.Valid cfg.geometry := by
  norm_num [firstId,cfg,MoePipelineTests.combineCfg,MoeExpertsMemoryTests.geometry,ThreadId.Valid,Dim3.Within,Dim3.zero]
theorem first_active : Active cfg firstId := by
  norm_num [Active,cfg,firstId,MoePipelineTests.combineCfg,MoePipelineTests.combineInput,
    MoeExpertsMemoryTests.geometry,row,col,Dim3.zero]
def badValues : Moe.Matrix := fun r c => values r c+1
def badCandidate : Scalar.Candidate := canonical cfg gates badValues launch.params pre.2.1
theorem bad_locally_complete : Scalar.WellFormed code launch badCandidate ∧ badCandidate.Complete :=
  ⟨canonical_wellFormed cfg gates badValues pre.1 pre.2.1,canonical_complete cfg gates badValues launch.params pre.2.1⟩
theorem wrong_h_memory_rejected (rf : ReadsFrom) (co : Coherence) :
    ¬ GenericMemoryConditions badCandidate initial rf co := by
  intro hm
  have ht := canonical_member cfg gates badValues launch.params pre.2.1 first_valid
  have ha : Active cfg (canonicalTrace cfg gates badValues launch.params pre.2.1 firstId).id := by simpa using first_active
  have hh := answer_correct bad_locally_complete.1 bad_locally_complete.2 pre.1 pre.2.1 initialized hm ht ha
  simp only [canonical_trace_id,canonical_trace_oracle,answer,Scalar.replyReal_of_typed (expertOracle_value cfg gates badValues firstId),badValues] at hh
  linarith

def badGates : Moe.Matrix := fun _ gate => if gate = 1 then 1 else 0
def badRouteCandidate : Scalar.Candidate := canonical cfg badGates values launch.params pre.2.1
theorem bad_route_locally_complete : Scalar.WellFormed code launch badRouteCandidate ∧ badRouteCandidate.Complete :=
  ⟨canonical_wellFormed cfg badGates values pre.1 pre.2.1,canonical_complete cfg badGates values launch.params pre.2.1⟩
theorem wrong_route_memory_rejected (rf : ReadsFrom) (co : Coherence) :
    ¬ GenericMemoryConditions badRouteCandidate initial rf co := by
  intro hm
  have ht := canonical_member cfg badGates values launch.params pre.2.1 first_valid
  have ha : Active cfg (canonicalTrace cfg badGates values launch.params pre.2.1 firstId).id := by simpa using first_active
  have hh := expert_correct bad_route_locally_complete.1 bad_route_locally_complete.2 pre.1 pre.2.1 initialized hm ht ha
  norm_num [canonical_trace_id,canonical_trace_oracle,expertOracle_expert,Moe.selected,gates,badGates,firstId,row,cfg,
    MoePipelineTests.combineCfg,MoeExpertsMemoryTests.geometry,Dim3.zero] at hh

theorem invalid_route_source : ∃ last, Scalar.run (context cfg launch.params firstId) (fun _ => .integer 17) code 25 {} =
    .ok (last,[routeEvent cfg.input (context cfg launch.params firstId) 17]) ∧ last.core.thread.status = .done ∧ last.core.queries = 1 := by
  exact invalid_route_execution cfg.input (context cfg launch.params firstId) (fun _ => .integer 17) 17 pre.2.1
    (index_bounds cfg first_valid launch.params) first_active.1 first_active.2 (route_pointer_bound cfg first_active) rfl (by decide)

def shortDomain : List Location := (List.range 3).map (fun offset => ⟨.global,384+offset⟩)
theorem incomplete_publication_rejected : ¬ CoversOutput cfg shortDomain := by
  intro hc
  have hh := hc 0 0 (by decide) (by decide) 3 (by decide)
  exact (show (⟨.global,387⟩ : Location) ∉ shortDomain by decide) hh

end
end Ptx.MoeCombineMemoryTests
