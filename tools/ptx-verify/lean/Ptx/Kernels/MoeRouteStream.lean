import Ptx.Kernels.MoeRouteWitness
import Ptx.Scalar.Stream

/-! The actual route stage publishes u32 routing to its successor's global
memory. This is one MoE component; no expert/combine composition is claimed. -/
namespace Ptx.MoeRouteEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeRouteThread
noncomputable section

theorem covers_global_writes {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    {domain : List Location} (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params) (hc : CoversOutput cfg domain) :
    CoversGlobalWrites execution domain := by
  intro writer loc value _ hwrite
  obtain ⟨_,ha,_,answer,hpayload⟩ := write_shape hw hd hg hp hwrite
  obtain ⟨offset,hb,rfl⟩ := payload_location hpayload
  exact hc _ ha offset (by simpa only [u32_bytes_size] using hb)

def invocation (cfg : Config) (params : Bindings) (shared : Stream.SharedInitial) (domain : List Location) : Stream.Invocation :=
  ⟨code,cfg.geometry,params,shared,domain⟩
def HeapPre (cfg : Config) (gates : Moe.Matrix) (heap : Stream.Heap) : Prop :=
  ∀ row gate, row < cfg.input.m → gate < 2 →
    Stream.Represents .f32 heap (gLoc cfg row gate).address (gates row gate)
def HeapPost (cfg : Config) (gates : Moe.Matrix) (before after : Stream.Heap) : Prop :=
  (∀ row, row < cfg.input.m → Stream.RepresentsWord after (rLoc cfg row).address (Moe.selected gates row)) ∧
  ∀ address, ¬ InWords cfg.input.r cfg.input.m ⟨.global,address⟩ → after address = before address

theorem heap_pre (cfg : Config) (gates : Moe.Matrix) (params : Bindings) (hp : Params cfg.input params)
    (shared : Stream.SharedInitial) (domain : List Location) {heap : Stream.Heap} (hi : HeapPre cfg gates heap) :
    Pre cfg gates ((invocation cfg params shared domain).launch heap) := ⟨rfl,hp,hi⟩

theorem stream_correct (cfg : Config) (gates : Moe.Matrix) (params : Bindings) (hp : Params cfg.input params)
    (shared : Stream.SharedInitial) (domain : List Location) (hc : CoversOutput cfg domain) :
    Stream.Triple [invocation cfg params shared domain] (HeapPre cfg gates) (HeapPost cfg gates) := by
  apply Stream.single_correct (pre := HeapPre cfg gates) (post := HeapPost cfg gates)
    (kernelPre := Pre cfg gates) (kernelPost := fun launch output =>
    Moe.Routes gates cfg.input.m cfg.input.r output ∧
      ∀ loc ∈ domain, ¬ InWords cfg.input.r cfg.input.m loc → output loc = launch.initial loc)
    (invocation cfg params shared domain) (checked_correct cfg gates domain hc)
    (fun _ hi => heap_pre cfg gates params hp shared domain hi)
  intro heap o hi hd hpost
  change o.domain = domain at hd
  constructor
  · intro row hr
    apply Stream.publish_word (hpost.1 row hr)
    intro offset ho
    rw [hd]
    exact hc row hr offset ho
  · intro address hout
    by_cases hm : (⟨.global,address⟩ : Location) ∈ o.domain
    · rw [Stream.publish_on hm]
      exact hpost.2 _ (by simpa only [hd] using hm) hout
    · exact Stream.publish_outside hm

theorem stream_nonvacuous (cfg : Config) (gates : Moe.Matrix) (params : Bindings) (hp : Params cfg.input params)
    (shared : Stream.SharedInitial) (domain : List Location) (hc : CoversOutput cfg domain)
    (hg : ∀ loc ∈ domain, loc.space = .global) :
    Stream.Nonvacuous [invocation cfg params shared domain] (HeapPre cfg gates) := by
  apply Stream.single_nonvacuous (invocation cfg params shared domain) (checked_nonvacuous cfg gates domain hg)
    (fun _ hi => heap_pre cfg gates params hp shared domain hi)
  intro heap c rf co o hi hchecked ho _
  exact covers_global_writes hchecked.provenance ho.complete rfl hp hc

end
end Ptx.MoeRouteEvent
