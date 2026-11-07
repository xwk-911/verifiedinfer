import Ptx.Kernels.MoeCombineWitness
import Ptx.Scalar.Stream

/-! Completed ordinary-memory gather publication, covering every actual Y write
and preserving all global bytes outside Y. -/
namespace Ptx.MoeCombineEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeCombine
noncomputable section

theorem covers_global_writes {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    {domain : List Location}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hc : CoversOutput cfg domain) : CoversGlobalWrites execution domain := by
  intro writer loc value _ hwrite
  obtain ⟨_,ha,_,answer,hpayload⟩ := write_shape hw hd hg hp hwrite
  obtain ⟨offset,hb,rfl⟩ := payload_location hpayload
  exact hc _ _ ha.1 ha.2 offset (by simpa only [Symbolic.encode_length,Symbolic.Format.bytes] using hb)

def invocation (cfg : Config) (params : Bindings) (shared : Stream.SharedInitial) (domain : List Location) : Stream.Invocation :=
  ⟨code,cfg.geometry,params,shared,domain⟩
def HeapPre (cfg : Config) (gates values : Moe.Matrix) (heap : Stream.Heap) : Prop :=
  (∀ r, r < cfg.input.m → 0 < cfg.input.n → Stream.RepresentsWord heap (rLoc cfg r).address (Moe.selected gates r)) ∧
  (∀ r c, r < cfg.input.m → c < cfg.input.n →
    Stream.Represents .f32 heap (hLoc cfg (Moe.selected gates r) r c).address (values r c))
def HeapPost (cfg : Config) (values : Moe.Matrix) (before after : Stream.Heap) : Prop :=
  (∀ r c, r < cfg.input.m → c < cfg.input.n →
    Stream.Represents .f32 after (yLoc cfg r c).address (values r c)) ∧
  ∀ address, ¬ InWords cfg.input.y (cfg.input.m*cfg.input.n) ⟨.global,address⟩ → after address = before address

theorem heap_pre (cfg : Config) (gates values : Moe.Matrix) (params : Bindings)
    (hp : Params cfg.input params) (shared : Stream.SharedInitial) (domain : List Location)
    {heap : Stream.Heap} (hi : HeapPre cfg gates values heap) :
    Pre cfg gates values ((invocation cfg params shared domain).launch heap) := ⟨rfl,hp,hi⟩

theorem stream_correct (cfg : Config) (gates values : Moe.Matrix) (params : Bindings)
    (hp : Params cfg.input params) (shared : Stream.SharedInitial) (domain : List Location)
    (hc : CoversOutput cfg domain) :
    Stream.Triple [invocation cfg params shared domain] (HeapPre cfg gates values) (HeapPost cfg values) := by
  apply Stream.single_correct (pre := HeapPre cfg gates values) (post := HeapPost cfg values)
    (kernelPre := Pre cfg gates values) (kernelPost := fun launch output =>
    Post cfg values output ∧
      ∀ loc ∈ domain, ¬ InWords cfg.input.y (cfg.input.m*cfg.input.n) loc → output loc = launch.initial loc)
    (invocation cfg params shared domain) (checked_correct cfg gates values domain hc)
    (fun _ hi => heap_pre cfg gates values params hp shared domain hi)
  intro heap o hi hd hpost
  change o.domain = domain at hd
  constructor
  · intro r c hr hcol
    apply Stream.publish_represents (hpost.1 r c hr hcol)
    intro offset ho
    rw [hd]
    exact hc r c hr hcol offset ho
  · intro address hout
    by_cases hm : (⟨.global,address⟩ : Location) ∈ o.domain
    · rw [Stream.publish_on hm]
      exact hpost.2 _ (by simpa only [hd] using hm) hout
    · exact Stream.publish_outside hm

theorem stream_nonvacuous (cfg : Config) (gates values : Moe.Matrix) (params : Bindings)
    (hp : Params cfg.input params) (shared : Stream.SharedInitial) (domain : List Location)
    (hc : CoversOutput cfg domain) (hg : ∀ loc ∈ domain, loc.space = .global) :
    Stream.Nonvacuous [invocation cfg params shared domain] (HeapPre cfg gates values) := by
  apply Stream.single_nonvacuous (invocation cfg params shared domain)
    (checked_nonvacuous cfg gates values domain hg)
    (fun _ hi => heap_pre cfg gates values params hp shared domain hi)
  intro heap c rf co o hi hchecked ho _
  exact covers_global_writes hchecked.provenance ho.complete rfl hp hc

end
end Ptx.MoeCombineEvent
