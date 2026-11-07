import Ptx.Kernels.MoeExpertsWitness
import Ptx.Scalar.Stream

/-! Completed ordinary-memory expert publication, with every actual write
covered and all nonselected bytes preserved. Combine composition is separate. -/
namespace Ptx.MoeExpertsEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeExperts Ptx.MoeExpertsLoop
noncomputable section

theorem covers_global_writes {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    {rf : ReadsFrom} {co : Coherence} {gates x : Moe.Matrix} {weights : Moe.Weights} {domain : List Location}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (hi : Initialized cfg gates x weights launch.initial) (hm : GenericMemoryConditions execution launch.initial rf co)
    (hc : CoversOutput cfg gates domain) : CoversGlobalWrites execution domain := by
  intro writer loc value _ hwrite
  obtain ⟨r,c,offset,hr,hcol,hb,rfl⟩ := write_selected hw hd hg hp hi hm hwrite
  exact hc r c hr hcol offset hb

def invocation (cfg : Config) (params : Bindings) (shared : Stream.SharedInitial) (domain : List Location) : Stream.Invocation :=
  ⟨code,cfg.geometry,params,shared,domain⟩
def HeapPre (cfg : Config) (gates x : Moe.Matrix) (weights : Moe.Weights) (heap : Stream.Heap) : Prop :=
  (∀ r, r < cfg.input.m → 0 < cfg.input.n → Stream.RepresentsWord heap (rLoc cfg r).address (Moe.selected gates r)) ∧
  (∀ r k, r < cfg.input.m → k < cfg.input.k → 0 < cfg.input.n → Stream.Represents .f32 heap (xLoc cfg r k).address (x r k)) ∧
  (∀ e k c, e < 2 → k < cfg.input.k → c < cfg.input.n → 0 < cfg.input.m →
    Stream.Represents .f32 heap (wLoc cfg e k c).address (weights e k c))
def HeapPost (cfg : Config) (gates x : Moe.Matrix) (weights : Moe.Weights) (before after : Stream.Heap) : Prop :=
  (∀ r c, r < cfg.input.m → c < cfg.input.n →
    Stream.Represents .f32 after (hLoc cfg (Moe.selected gates r) r c).address (Moe.output gates x weights r c cfg.input.k)) ∧
  ∀ address, ¬ SelectedByte cfg gates ⟨.global,address⟩ → after address = before address

theorem heap_pre (cfg : Config) (gates x : Moe.Matrix) (weights : Moe.Weights) (params : Bindings)
    (hp : Params cfg.input params) (shared : Stream.SharedInitial) (domain : List Location)
    {heap : Stream.Heap} (hi : HeapPre cfg gates x weights heap) :
    Pre cfg gates x weights ((invocation cfg params shared domain).launch heap) := ⟨rfl,hp,hi⟩

theorem stream_correct (cfg : Config) (gates x : Moe.Matrix) (weights : Moe.Weights) (params : Bindings)
    (hp : Params cfg.input params) (shared : Stream.SharedInitial) (domain : List Location)
    (hc : CoversOutput cfg gates domain) :
    Stream.Triple [invocation cfg params shared domain] (HeapPre cfg gates x weights) (HeapPost cfg gates x weights) := by
  apply Stream.single_correct (pre := HeapPre cfg gates x weights) (post := HeapPost cfg gates x weights)
    (kernelPre := Pre cfg gates x weights) (kernelPost := fun launch output =>
    Moe.Experts gates x weights cfg.input.m cfg.input.n cfg.input.k cfg.input.h output ∧
      ∀ loc ∈ domain, ¬ SelectedByte cfg gates loc → output loc = launch.initial loc)
    (invocation cfg params shared domain) (checked_correct cfg gates x weights domain hc)
    (fun _ hi => heap_pre cfg gates x weights params hp shared domain hi)
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

theorem stream_nonvacuous (cfg : Config) (gates x : Moe.Matrix) (weights : Moe.Weights) (params : Bindings)
    (hp : Params cfg.input params) (shared : Stream.SharedInitial) (domain : List Location)
    (hc : CoversOutput cfg gates domain) (hg : ∀ loc ∈ domain, loc.space = .global) :
    Stream.Nonvacuous [invocation cfg params shared domain] (HeapPre cfg gates x weights) := by
  apply Stream.single_nonvacuous (invocation cfg params shared domain)
    (checked_nonvacuous cfg gates x weights domain hg)
    (fun _ hi => heap_pre cfg gates x weights params hp shared domain hi)
  intro heap c rf co o hi hchecked ho _
  exact covers_global_writes hchecked.provenance ho.complete rfl hp hi hchecked.memory hc

end
end Ptx.MoeExpertsEvent
