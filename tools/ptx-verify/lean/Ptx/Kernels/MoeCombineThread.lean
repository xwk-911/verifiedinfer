import Ptx.Kernels.MoeCombineBody

/-! Full actual gather execution from PC0 and reconstruction of arbitrary
completed replies, without assuming initial-memory correspondence. -/
namespace Ptx.MoeCombine
open Ptx.ISA Ptx.Scalar
noncomputable section

def routeEvent (i : Inputs) (ctx : Scalar.Context) (value : Nat) : Scalar.Kind :=
  .read ⟨.global,i.r+4*row ctx.block ctx.id⟩ (u32Bytes (wrap 32 value))

theorem route_prefix (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) (value : Nat)
    (hp : Params i ctx.params) (hb : IndexBounds ctx) (hr : row ctx.block ctx.id < i.m)
    (hc : col ctx.block ctx.id < i.n) (hptr : i.r+4*row ctx.block ctx.id < 2^64)
    (hq : oracle 0 = .integer value) :
    Scalar.run ctx oracle code 22 {} = .ok
      (loadedInteger (beforeRoute i ctx) "%e" value,[routeEvent i ctx value]) ∧
      Loaded i ctx (wrap 32 value) 22 (loadedInteger (beforeRoute i ctx) "%e" value) := by
  obtain ⟨hprefix,hi⟩ := route_pointer_run i ctx oracle hp hb hr hc hptr
  have hs := route_load i ctx oracle hi hptr hq
  have hload : Scalar.run ctx oracle code 1 (beforeRoute i ctx) = .ok
      (loadedInteger (beforeRoute i ctx) "%e" value,[routeEvent i ctx value]) := by
    simp [Scalar.run,hs,routeEvent,Except.bind]
  exact ⟨run_append hprefix hload,loaded_facts i ctx value hi⟩

theorem active_initialization (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) (value : Nat)
    (hp : Params i ctx.params) (hb : IndexBounds ctx) (hr : row ctx.block ctx.id < i.m)
    (hc : col ctx.block ctx.id < i.n) (hptr : i.r+4*row ctx.block ctx.id < 2^64)
    (hq : oracle 0 = .integer value) (he : wrap 32 value < 2) (ha : AddressBounds i ctx (wrap 32 value)) :
    ∃ entry, Scalar.run ctx oracle code (31+selectSteps (wrap 32 value)) {} =
      .ok (entry,[routeEvent i ctx value]) ∧ Ready i ctx (wrap 32 value) entry := by
  obtain ⟨hprefix,hi⟩ := route_prefix i ctx oracle value hp hb hr hc hptr hq
  obtain ⟨selected,hselect,hselected⟩ := select_run i ctx oracle hi he
  obtain ⟨entry,haddr,hinv⟩ := address_run i ctx oracle (wrap 32 value) hselected hb ha
  have hfull := run_append (run_append hprefix hselect) haddr
  refine ⟨entry,?_,hinv⟩
  have hn : 22+selectSteps (wrap 32 value)+9 = 31+selectSteps (wrap 32 value) := by omega
  simpa only [hn,List.append_nil] using hfull

def activeCount (expert : Nat) : Nat := 34+selectSteps expert

theorem active_execution (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) (route : Nat) (value : ℝ)
    (hp : Params i ctx.params) (hb : IndexBounds ctx) (hr : row ctx.block ctx.id < i.m)
    (hc : col ctx.block ctx.id < i.n) (hptr : i.r+4*row ctx.block ctx.id < 2^64)
    (hq : oracle 0 = .integer route) (he : wrap 32 route < 2) (ha : AddressBounds i ctx (wrap 32 route))
    (hv : oracle 1 = .real .f32 value) :
    ∃ last, Scalar.run ctx oracle code (activeCount (wrap 32 route)) {} = .ok
      (last,[routeEvent i ctx route] ++ bodyEvents i ctx (wrap 32 route) value) ∧
      last.core.thread.status = .done ∧ last.core.queries = 2 := by
  obtain ⟨entry,hprefix,hi⟩ := active_initialization i ctx oracle route hp hb hr hc hptr hq he ha
  obtain ⟨hbody,hd,hqueries⟩ := body_run i ctx oracle (wrap 32 route) value hi ha hv
  refine ⟨_,?_,hd,hqueries⟩
  have hn : (31+selectSteps (wrap 32 route))+3 = activeCount (wrap 32 route) := by unfold activeCount; omega
  simpa only [hn] using run_append hprefix hbody

theorem completed_route_reply (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : IndexBounds ctx) (hr : row ctx.block ctx.id < i.m)
    (hc : col ctx.block ctx.id < i.n) (hptr : i.r+4*row ctx.block ctx.id < 2^64)
    {n last events} (hn : Scalar.run ctx oracle code n {} = .ok (last,events))
    (hd : last.core.thread.status = .done) : ∃ value, oracle 0 = .integer value := by
  obtain ⟨hprefix,hi⟩ := route_pointer_run i ctx oracle hp hb hr hc hptr
  obtain ⟨next,emitted,hs⟩ := step_after_running_prefix hn hd hprefix hi.running
  obtain ⟨value,hq⟩ := integer_reply_of_successful_load hi.running
    (show code[(beforeRoute i ctx).core.thread.pc]? = some (.integer (.load .global "%e" {base := .reg "%rp"})) by
      rw [hi.pcValue]; rfl) hs
  exact ⟨value,by simpa only [hi.queries] using hq⟩

theorem invalid_route_execution (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) (value : Nat)
    (hp : Params i ctx.params) (hb : IndexBounds ctx) (hr : row ctx.block ctx.id < i.m)
    (hc : col ctx.block ctx.id < i.n) (hptr : i.r+4*row ctx.block ctx.id < 2^64)
    (hq : oracle 0 = .integer value) (he : 2 ≤ wrap 32 value) :
    ∃ last, Scalar.run ctx oracle code 25 {} = .ok (last,[routeEvent i ctx value]) ∧
      last.core.thread.status = .done ∧ last.core.queries = 1 := by
  obtain ⟨hprefix,hi⟩ := route_prefix i ctx oracle value hp hb hr hc hptr hq
  have h32 : wrap 32 value < 2^32 := Nat.mod_lt _ (by decide)
  have hguard : Scalar.run ctx oracle code 2 (loadedInteger (beforeRoute i ctx) "%e" value) =
      .ok (afterGuard (loadedInteger (beforeRoute i ctx) "%e" value) 1 40,[]) := by
    simpa only [ite_eq_left he] using route_guard i ctx oracle hi h32
  have hf := loaded_guard_facts hi 1 40
  obtain ⟨last,hret,hd,hqueries⟩ := masked_return ctx oracle hf.running hf.pcValue
  have hfull := run_append (run_append hprefix hguard) hret
  exact ⟨last,by simpa [he] using hfull,hd,hqueries.trans hf.queries⟩

theorem reconstruct_active (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) (value : Nat)
    (hp : Params i ctx.params) (hb : IndexBounds ctx) (hr : row ctx.block ctx.id < i.m)
    (hc : col ctx.block ctx.id < i.n) (hptr : i.r+4*row ctx.block ctx.id < 2^64)
    (hq : oracle 0 = .integer value) (he : wrap 32 value < 2) (ha : AddressBounds i ctx (wrap 32 value))
    {n last events} (hn : Scalar.run ctx oracle code n {} = .ok (last,events))
    (hd : last.core.thread.status = .done) :
    n = activeCount (wrap 32 value) ∧ oracle 1 = .real .f32 (Scalar.replyReal oracle 1) ∧
      events = [routeEvent i ctx value] ++ bodyEvents i ctx (wrap 32 value) (Scalar.replyReal oracle 1) := by
  obtain ⟨entry,hprefix,hi⟩ := active_initialization i ctx oracle value hp hb hr hc hptr hq he ha
  obtain ⟨remaining,tailEvents,hcount,htail,htrace⟩ := complete_after_prefix hn hd hprefix hi.running
  obtain ⟨hq1,hsize,hevents⟩ := completed_body hi ha htail hd
  refine ⟨?_,hq1,?_⟩
  · unfold activeCount
    omega
  · simpa only [hevents] using htrace

end
end Ptx.MoeCombine
