import Ptx.Kernels.MoeRouteStream
import Ptx.Kernels.MoeExpertsStream
import Ptx.Kernels.MoeCombineStream

/-! Three actual kernels, joined through completed ordinary-memory stream
publication. Successor R/H initialization follows prior outputs and frames;
initial R/H/Y contents are unrestricted. This is not concurrent-kernel/runtime
or IEEE bit-equivalence verification. -/
namespace Ptx.MoePipeline
open Ptx.ISA Ptx.Scalar Ptx.Scalar.Stream
noncomputable section

structure Config where
  route : MoeRouteEvent.Config
  experts : MoeExpertsEvent.Config
  combine : MoeCombineEvent.Config
  routeRows : route.input.m = experts.input.m
  combineRows : combine.input.m = experts.input.m
  combineCols : combine.input.n = experts.input.n
  routeR : route.input.r = experts.input.r
  combineR : combine.input.r = experts.input.r
  combineH : combine.input.h = experts.input.h
  separateXR : 0 < experts.input.n → WordsDisjoint experts.input.x (experts.input.m*experts.input.k) route.input.r route.input.m
  separateWR : 0 < experts.input.m → WordsDisjoint experts.input.w ((2*experts.input.k)*experts.input.n) route.input.r route.input.m
  routeParams : Bindings
  expertParams : Bindings
  combineParams : Bindings
  routeBindings : MoeRouteThread.Params route.input routeParams
  expertBindings : MoeExperts.Params experts.input expertParams
  combineBindings : MoeCombine.Params combine.input combineParams
  routeShared : SharedInitial
  expertShared : SharedInitial
  combineShared : SharedInitial
  routeDomain : List Location
  expertDomain : List Location
  combineDomain : List Location
  routeCover : MoeRouteEvent.CoversOutput route routeDomain
  expertCover : ∀ gates, MoeExpertsEvent.CoversOutput experts gates expertDomain
  combineCover : MoeCombineEvent.CoversOutput combine combineDomain
  routeGlobal : ∀ loc ∈ routeDomain, loc.space = .global
  expertGlobal : ∀ loc ∈ expertDomain, loc.space = .global
  combineGlobal : ∀ loc ∈ combineDomain, loc.space = .global

def routeInvocation (cfg : Config) : Invocation :=
  MoeRouteEvent.invocation cfg.route cfg.routeParams cfg.routeShared cfg.routeDomain
def expertInvocation (cfg : Config) : Invocation :=
  MoeExpertsEvent.invocation cfg.experts cfg.expertParams cfg.expertShared cfg.expertDomain
def combineInvocation (cfg : Config) : Invocation :=
  MoeCombineEvent.invocation cfg.combine cfg.combineParams cfg.combineShared cfg.combineDomain
def commands (cfg : Config) : List Invocation := [routeInvocation cfg,expertInvocation cfg,combineInvocation cfg]
def values (cfg : Config) (gates x : Moe.Matrix) (weights : Moe.Weights) : Moe.Matrix :=
  fun r c => Moe.output gates x weights r c cfg.experts.input.k
def Pre (cfg : Config) (gates x : Moe.Matrix) (weights : Moe.Weights) (heap : Heap) : Prop :=
  MoeRouteEvent.HeapPre cfg.route gates heap ∧
  (∀ r k, r < cfg.experts.input.m → k < cfg.experts.input.k → 0 < cfg.experts.input.n →
    Represents .f32 heap (MoeExpertsEvent.xLoc cfg.experts r k).address (x r k)) ∧
  (∀ e k c, e < 2 → k < cfg.experts.input.k → c < cfg.experts.input.n → 0 < cfg.experts.input.m →
    Represents .f32 heap (MoeExpertsEvent.wLoc cfg.experts e k c).address (weights e k c))
def Changed (cfg : Config) (gates : Moe.Matrix) (loc : Location) : Prop :=
  InWords cfg.route.input.r cfg.route.input.m loc ∨
  MoeExpertsEvent.SelectedByte cfg.experts gates loc ∨
  InWords cfg.combine.input.y (cfg.combine.input.m*cfg.combine.input.n) loc
def Post (cfg : Config) (gates x : Moe.Matrix) (weights : Moe.Weights) (before after : Heap) : Prop :=
  (∀ r c, r < cfg.experts.input.m → c < cfg.experts.input.n →
    Represents .f32 after (MoeCombineEvent.yLoc cfg.combine r c).address (values cfg gates x weights r c)) ∧
  ∀ address, ¬ Changed cfg gates ⟨.global,address⟩ → after address = before address

theorem experts_ready {cfg : Config} {gates x : Moe.Matrix} {weights : Moe.Weights} {before routed : Heap}
    (hp : Pre cfg gates x weights before) (hr : MoeRouteEvent.HeapPost cfg.route gates before routed) :
    MoeExpertsEvent.HeapPre cfg.experts gates x weights routed := by
  refine ⟨?_,?_,?_⟩
  · intro r hrow _
    have h := hr.1 r (by simpa only [cfg.routeRows] using hrow)
    simpa only [MoeExpertsEvent.rLoc,MoeRouteEvent.rLoc,cfg.routeR] using h
  · intro r k hrow hk hn offset ho
    rw [hr.2 _ ?_]
    · exact hp.2.1 r k hrow hk hn offset ho
    · intro hout
      apply words_disjoint (cfg.separateXR hn) ?_ hout
      exact word_in_region (MoeExpertsEvent.x_index_bound cfg.experts hrow hk) (by dsimp [MoeExpertsEvent.xLoc]; omega)
        (by change offset < 4 at ho; dsimp [MoeExpertsEvent.xLoc]; omega)
  · intro e k c he hk hc hm offset ho
    rw [hr.2 _ ?_]
    · exact hp.2.2 e k c he hk hc hm offset ho
    · intro hout
      apply words_disjoint (cfg.separateWR hm) ?_ hout
      exact word_in_region (MoeExpertsEvent.w_index_bound cfg.experts he hk hc) (by dsimp [MoeExpertsEvent.wLoc]; omega)
        (by change offset < 4 at ho; dsimp [MoeExpertsEvent.wLoc]; omega)

theorem selected_region {cfg : MoeExpertsEvent.Config} {gates : Moe.Matrix} {loc : Location}
    (hs : MoeExpertsEvent.SelectedByte cfg gates loc) : InWords cfg.input.h ((2*cfg.input.m)*cfg.input.n) loc := by
  obtain ⟨r,c,offset,hr,hc,ho,rfl⟩ := hs
  exact word_in_region (MoeExpertsEvent.h_index_bound cfg (Moe.selected_bound gates r) hr hc)
    (by dsimp [MoeExpertsEvent.hLoc,Location.add]; omega) (by dsimp [MoeExpertsEvent.hLoc,Location.add]; omega)

theorem combine_ready {cfg : Config} {gates x : Moe.Matrix} {weights : Moe.Weights} {before routed experted : Heap}
    (hr : MoeRouteEvent.HeapPost cfg.route gates before routed)
    (he : MoeExpertsEvent.HeapPost cfg.experts gates x weights routed experted) :
    MoeCombineEvent.HeapPre cfg.combine gates (values cfg gates x weights) experted := by
  constructor
  · intro r hrow hn offset ho
    have hrowE : r < cfg.experts.input.m := by simpa only [cfg.combineRows] using hrow
    have hrowR : r < cfg.route.input.m := by simpa only [cfg.routeRows] using hrowE
    have hsame : (MoeCombineEvent.rLoc cfg.combine r).address = (MoeExpertsEvent.rLoc cfg.experts r).address := by
      simp only [MoeCombineEvent.rLoc,MoeExpertsEvent.rLoc,cfg.combineR]
    rw [hsame,he.2 _ ?_]
    · simpa only [MoeExpertsEvent.rLoc,MoeRouteEvent.rLoc,cfg.routeR] using hr.1 r hrowR offset ho
    · intro hs
      apply words_disjoint cfg.experts.separateR ?_ (selected_region hs)
      exact word_in_region hrowE (by dsimp [MoeExpertsEvent.rLoc]; omega)
        (by dsimp [MoeExpertsEvent.rLoc]; omega)
  · intro r c hrow hc
    have hrowE : r < cfg.experts.input.m := by simpa only [cfg.combineRows] using hrow
    have hcE : c < cfg.experts.input.n := by simpa only [cfg.combineCols] using hc
    simpa only [MoeCombineEvent.hLoc,MoeExpertsEvent.hLoc,cfg.combineRows,cfg.combineCols,cfg.combineH,values] using he.1 r c hrowE hcE

theorem post_of_stages {cfg : Config} {gates x : Moe.Matrix} {weights : Moe.Weights} {before routed experted after : Heap}
    (hr : MoeRouteEvent.HeapPost cfg.route gates before routed)
    (he : MoeExpertsEvent.HeapPost cfg.experts gates x weights routed experted)
    (hc : MoeCombineEvent.HeapPost cfg.combine (values cfg gates x weights) experted after) :
    Post cfg gates x weights before after := by
  constructor
  · intro r c hrow hcol
    exact hc.1 r c (by simpa only [cfg.combineRows] using hrow) (by simpa only [cfg.combineCols] using hcol)
  · intro address hout
    rw [hc.2 address (fun h => hout (.inr (.inr h))),he.2 address (fun h => hout (.inr (.inl h))),
      hr.2 address (fun h => hout (.inl h))]

theorem moe_output {cfg : Config} {gates x : Moe.Matrix} {weights : Moe.Weights} {before after : Heap}
    (hp : Post cfg gates x weights before after) :
    Moe.Post gates x weights cfg.experts.input.m cfg.experts.input.n cfg.experts.input.k cfg.combine.input.y
      (fun loc => after loc.address) := by
  intro r c hr hc offset ho
  simpa only [MoeCombineEvent.yLoc,cfg.combineCols,values,Location.add] using hp.1 r c hr hc offset ho

theorem correct (cfg : Config) (gates x : Moe.Matrix) (weights : Moe.Weights) :
    Stream.Triple (commands cfg) (Pre cfg gates x weights) (Post cfg gates x weights) := by
  intro before after hp hex
  obtain ⟨routed,hr,htail⟩ := runs_split (first := [routeInvocation cfg]) (rest := [expertInvocation cfg,combineInvocation cfg]) hex
  obtain ⟨experted,he,hc⟩ := runs_split (first := [expertInvocation cfg]) (rest := [combineInvocation cfg]) htail
  have routePost := MoeRouteEvent.stream_correct cfg.route gates cfg.routeParams cfg.routeBindings cfg.routeShared cfg.routeDomain
    cfg.routeCover before routed hp.1 hr
  have expertPost := MoeExpertsEvent.stream_correct cfg.experts gates x weights cfg.expertParams cfg.expertBindings cfg.expertShared
    cfg.expertDomain (cfg.expertCover gates) routed experted (experts_ready hp routePost) he
  have combinePost := MoeCombineEvent.stream_correct cfg.combine gates (values cfg gates x weights) cfg.combineParams cfg.combineBindings
    cfg.combineShared cfg.combineDomain cfg.combineCover experted after (combine_ready routePost expertPost) hc
  exact post_of_stages routePost expertPost combinePost

theorem nonvacuous (cfg : Config) (gates x : Moe.Matrix) (weights : Moe.Weights) :
    Stream.Nonvacuous (commands cfg) (Pre cfg gates x weights) := by
  intro before hp
  obtain ⟨routed,hr⟩ := MoeRouteEvent.stream_nonvacuous cfg.route gates cfg.routeParams cfg.routeBindings cfg.routeShared cfg.routeDomain
    cfg.routeCover cfg.routeGlobal before hp.1
  have routePost := MoeRouteEvent.stream_correct cfg.route gates cfg.routeParams cfg.routeBindings cfg.routeShared cfg.routeDomain
    cfg.routeCover before routed hp.1 hr
  obtain ⟨experted,he⟩ := MoeExpertsEvent.stream_nonvacuous cfg.experts gates x weights cfg.expertParams cfg.expertBindings cfg.expertShared
    cfg.expertDomain (cfg.expertCover gates) cfg.expertGlobal routed (experts_ready hp routePost)
  have expertPost := MoeExpertsEvent.stream_correct cfg.experts gates x weights cfg.expertParams cfg.expertBindings cfg.expertShared
    cfg.expertDomain (cfg.expertCover gates) routed experted (experts_ready hp routePost) he
  obtain ⟨after,hc⟩ := MoeCombineEvent.stream_nonvacuous cfg.combine gates (values cfg gates x weights) cfg.combineParams cfg.combineBindings
    cfg.combineShared cfg.combineDomain cfg.combineCover cfg.combineGlobal experted (combine_ready routePost expertPost)
  exact ⟨after,runs_append hr (runs_append he hc)⟩

end
end Ptx.MoePipeline
