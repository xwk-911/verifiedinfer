import Ptx.Kernels.MoeExpertsAddress
import Ptx.Scalar.Replies

/-! Full PC=0 parameterized expert execution and arbitrary completed-source
reconstruction. Typed replies are derived; initial-memory agreement, ownership
and complete legal launch witnesses remain separate global proof obligations. -/
namespace Ptx.MoeExperts
open Ptx.ISA Ptx.Scalar Ptx.MoeExpertsLoop
noncomputable section

def routeEvent (i : Inputs) (ctx : Scalar.Context) (value : Nat) : Scalar.Kind :=
  .read ⟨.global,i.r+4*row ctx.block ctx.id⟩ (u32Bytes (wrap 32 value))

theorem route_prefix (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) (value : Nat)
    (hp : Params i ctx.params) (hb : IndexBounds ctx) (hr : row ctx.block ctx.id < i.m)
    (hc : col ctx.block ctx.id < i.n) (hptr : i.r+4*row ctx.block ctx.id < 2^64)
    (hq : oracle 0 = .integer value) :
    Scalar.run ctx oracle code 24 {} = .ok
      (loadedInteger (beforeRoute i ctx) "%e" value,[routeEvent i ctx value]) ∧
      Loaded i ctx (wrap 32 value) 24 (loadedInteger (beforeRoute i ctx) "%e" value) := by
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
    ∃ entry, Scalar.run ctx oracle code (36+selectSteps (wrap 32 value)) {} =
      .ok (entry,[routeEvent i ctx value]) ∧ FmaLoop.Inv 46 1 (threadLayout i ctx (wrap 32 value) ha) 0 0 entry := by
  obtain ⟨hprefix,hi⟩ := route_prefix i ctx oracle value hp hb hr hc hptr hq
  obtain ⟨selected,hselect,hselected⟩ := select_run i ctx oracle hi he
  obtain ⟨entry,haddr,hinv⟩ := address_run i ctx oracle (wrap 32 value) hselected hb ha
  have hfull := run_append (run_append hprefix hselect) haddr
  refine ⟨entry,?_,hinv⟩
  have hn : 24+selectSteps (wrap 32 value)+12 = 36+selectSteps (wrap 32 value) := by omega
  simpa only [hn,List.append_nil] using hfull

def activeCount (i : Inputs) (expert : Nat) : Nat := 40+selectSteps expert+9*i.k

theorem active_execution (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) (value : Nat)
    (x : Moe.Matrix) (weights : Moe.Weights)
    (hp : Params i ctx.params) (hb : IndexBounds ctx) (hr : row ctx.block ctx.id < i.m)
    (hc : col ctx.block ctx.id < i.n) (hptr : i.r+4*row ctx.block ctx.id < 2^64)
    (hq : oracle 0 = .integer value) (he : wrap 32 value < 2) (ha : AddressBounds i ctx (wrap 32 value))
    (hx : ∀ k, k < i.k → oracle (1+2*k) = .real .f32 (x (row ctx.block ctx.id) k))
    (hw : ∀ k, k < i.k → oracle (1+2*k+1) = .real .f32 (weights (wrap 32 value) k (col ctx.block ctx.id))) :
    ∃ last, Scalar.run ctx oracle code (activeCount i (wrap 32 value)) {} = .ok
      (last,[routeEvent i ctx value] ++
        FmaLoop.loopReads (threadLayout i ctx (wrap 32 value) ha) x (expertMatrix weights (wrap 32 value))
          (row ctx.block ctx.id) (col ctx.block ctx.id) 0 i.k ++
        [.write ⟨.global,(threadLayout i ctx (wrap 32 value) ha).output⟩
          (Symbolic.encode .f32 (Moe.linear x weights (wrap 32 value) (row ctx.block ctx.id) (col ctx.block ctx.id) i.k))]) ∧
      FmaLoop.Finished 46 1 (threadLayout i ctx (wrap 32 value) ha)
        (Moe.linear x weights (wrap 32 value) (row ctx.block ctx.id) (col ctx.block ctx.id) i.k) last := by
  obtain ⟨entry,hprefix,hi⟩ := active_initialization i ctx oracle value hp hb hr hc hptr hq he ha
  obtain ⟨last,hloop,hf⟩ := MoeExpertsLoop.complete (threadLayout i ctx (wrap 32 value) ha) ctx oracle x weights
    (wrap 32 value) (row ctx.block ctx.id) (col ctx.block ctx.id) hx hw hi
  have hfull := run_append hprefix hloop
  have hn : (36+selectSteps (wrap 32 value))+(9*i.k+4) = activeCount i (wrap 32 value) := by unfold activeCount; omega
  exact ⟨last,by simpa only [threadLayout,hn,List.append_assoc] using hfull,hf⟩

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
    ∃ last, Scalar.run ctx oracle code 27 {} = .ok (last,[routeEvent i ctx value]) ∧
      last.core.thread.status = .done ∧ last.core.queries = 1 := by
  obtain ⟨hprefix,hi⟩ := route_prefix i ctx oracle value hp hb hr hc hptr hq
  have h32 : wrap 32 value < 2^32 := Nat.mod_lt _ (by decide)
  have hguard : Scalar.run ctx oracle code 2 (loadedInteger (beforeRoute i ctx) "%e" value) =
      .ok (afterGuard (loadedInteger (beforeRoute i ctx) "%e" value) 1 56,[]) := by
    simpa only [ite_eq_left he] using route_guard i ctx oracle hi h32
  have hf := loaded_guard_facts hi 1 56
  obtain ⟨last,hret,hd,hqueries⟩ := masked_return ctx oracle hf.running hf.pcValue
  have hfull := run_append (run_append hprefix hguard) hret
  exact ⟨last,by simpa [he] using hfull,hd,hqueries.trans hf.queries⟩

theorem reconstruct_active (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) (value : Nat)
    (hp : Params i ctx.params) (hb : IndexBounds ctx) (hr : row ctx.block ctx.id < i.m)
    (hc : col ctx.block ctx.id < i.n) (hptr : i.r+4*row ctx.block ctx.id < 2^64)
    (hq : oracle 0 = .integer value) (he : wrap 32 value < 2) (ha : AddressBounds i ctx (wrap 32 value))
    {n last events} (hn : Scalar.run ctx oracle code n {} = .ok (last,events))
    (hd : last.core.thread.status = .done) :
    n = activeCount i (wrap 32 value) ∧
      events = [routeEvent i ctx value] ++
        (FmaLoop.loopReads (threadLayout i ctx (wrap 32 value) ha) (FmaLoop.replyA 1 oracle) (FmaLoop.replyB 1 oracle) 0 0 0 i.k ++
          [.write ⟨.global,(threadLayout i ctx (wrap 32 value) ha).output⟩ (Symbolic.encode .f32
            (ScalarMatmul.prefixProduct (FmaLoop.replyA 1 oracle) (FmaLoop.replyB 1 oracle) 0 0 i.k))]) := by
  obtain ⟨entry,hprefix,hi⟩ := active_initialization i ctx oracle value hp hb hr hc hptr hq he ha
  obtain ⟨remaining,tailEvents,hcount,htail,htrace⟩ := complete_after_prefix hn hd hprefix hi.running
  have hs := FmaLoop.completed_shape MoeExpertsLoop.fragment (threadLayout i ctx (wrap 32 value) ha) ctx oracle hi htail hd
  refine ⟨?_,?_⟩
  · have hsize := hs.1
    change remaining = 9*i.k+4 at hsize
    unfold activeCount
    omega
  · simpa only [hs.2.1,threadLayout] using htrace

theorem completed_source_cases (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : IndexBounds ctx)
    (hptr : row ctx.block ctx.id < i.m → col ctx.block ctx.id < i.n → i.r+4*row ctx.block ctx.id < 2^64)
    (ha : row ctx.block ctx.id < i.m → col ctx.block ctx.id < i.n → ∀ expert, expert < 2 → AddressBounds i ctx expert)
    {n last events} (hn : Scalar.run ctx oracle code n {} = .ok (last,events))
    (hd : last.core.thread.status = .done) :
    (i.m ≤ row ctx.block ctx.id ∧ n = 20 ∧ events = []) ∨
    (row ctx.block ctx.id < i.m ∧ i.n ≤ col ctx.block ctx.id ∧ n = 22 ∧ events = []) ∨
    (∃ hr : row ctx.block ctx.id < i.m, ∃ hc : col ctx.block ctx.id < i.n, ∃ value, oracle 0 = .integer value ∧
      ((2 ≤ wrap 32 value ∧ n = 27 ∧ events = [routeEvent i ctx value]) ∨
       (∃ he : wrap 32 value < 2, n = activeCount i (wrap 32 value) ∧
        events = [routeEvent i ctx value] ++
          (FmaLoop.loopReads (threadLayout i ctx (wrap 32 value) (ha hr hc _ he))
            (FmaLoop.replyA 1 oracle) (FmaLoop.replyB 1 oracle) 0 0 0 i.k ++
            [.write ⟨.global,(threadLayout i ctx (wrap 32 value) (ha hr hc _ he)).output⟩ (Symbolic.encode .f32
              (ScalarMatmul.prefixProduct (FmaLoop.replyA 1 oracle) (FmaLoop.replyB 1 oracle) 0 0 i.k))])))) := by
  by_cases hr : row ctx.block ctx.id < i.m
  · by_cases hc : col ctx.block ctx.id < i.n
    · obtain ⟨value,hq⟩ := completed_route_reply i ctx oracle hp hb hr hc (hptr hr hc) hn hd
      refine .inr (.inr ⟨hr,hc,value,hq,?_⟩)
      by_cases he : wrap 32 value < 2
      · exact .inr ⟨he,reconstruct_active i ctx oracle value hp hb hr hc (hptr hr hc) hq he (ha hr hc _ he) hn hd⟩
      · obtain ⟨last',hrun,hd',_⟩ := invalid_route_execution i ctx oracle value hp hb hr hc (hptr hr hc) hq (Nat.le_of_not_gt he)
        have h := complete_run_unique hn hd hrun hd'
        exact .inl ⟨Nat.le_of_not_gt he,h.1,h.2.2⟩
    · obtain ⟨last',hrun,hd',_⟩ := masked_col i ctx oracle hp hb hr (Nat.le_of_not_gt hc)
      have h := complete_run_unique hn hd hrun hd'
      exact .inr (.inl ⟨hr,Nat.le_of_not_gt hc,h.1,h.2.2⟩)
  · obtain ⟨last',hrun,hd',_⟩ := masked_row i ctx oracle hp hb (Nat.le_of_not_gt hr)
    have h := complete_run_unique hn hd hrun hd'
    exact .inl ⟨Nat.le_of_not_gt hr,h.1,h.2.2⟩

end
end Ptx.MoeExperts
