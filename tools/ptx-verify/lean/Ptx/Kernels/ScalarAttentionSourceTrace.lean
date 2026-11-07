import Ptx.Kernels.ScalarAttentionThread
import Ptx.Kernels.ScalarAttentionTrace

/-! Full PC=0 source reconstruction for arbitrary oracles/completion counts.
Scale and Q/K/V reply types follow from actual successful loads. Values remain
candidate-local until a separate global memory proof identifies initial inputs. -/
namespace Ptx.ScalarAttentionInit
open Ptx.ISA Ptx.Scalar Ptx.ScalarAttention
noncomputable section

theorem completed_scale_reply (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : IndexBounds ctx)
    (hr : row ctx.block ctx.id < i.m) (hc : col ctx.block ctx.id < i.dim)
    (hn : 0 < i.n) (hout : outputAddress i ctx < 2^64)
    {n final events} (hfull : Scalar.run ctx oracle code n {} = .ok (final,events))
    (hd : final.core.thread.status = .done) : ∃ scale, oracle 0 = .real .f32 scale := by
  obtain ⟨ready,hprefix,hi⟩ := output_prefix i ctx oracle hp hb hr hc hout
  have hguard : Scalar.run ctx oracle code 2 ready = .ok (afterGuard ready 0 30,[]) := by
    simpa only [ite_eq_right hn.ne'] using empty_guard_run i ctx oracle hi
  have hg := after_guard_ready hi 0 30
  have h30 := Scalar.run_append hprefix hguard
  obtain ⟨next,emitted,hstep⟩ := step_after_running_prefix hfull hd h30 hg.running
  obtain ⟨scale,hs⟩ := real_reply_of_successful_load hg.running
    (show code[(afterGuard ready 0 30).core.thread.pc]? =
      some (.load .f32 .global "%scale" {base := .reg "%sp"}) from rfl) hstep
  exact ⟨scale,by simpa only [hg.queries] using hs⟩

theorem active_completed_replies (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : IndexBounds ctx)
    (hr : row ctx.block ctx.id < i.m) (hc : col ctx.block ctx.id < i.dim)
    (hn : 0 < i.n) (ha : AddressBounds i ctx)
    {n final events} (hfull : Scalar.run ctx oracle code n {} = .ok (final,events))
    (hd : final.core.thread.status = .done) :
    ∃ scale, oracle 0 = .real .f32 scale ∧
      ∀ j, j < i.n →
        (∀ k, k < i.dim →
          oracle (ScalarAttentionOuter.queryIndex (threadLayout i ctx ha) j+2*k) =
            .real .f32 (ScalarAttentionTrace.qValues (threadLayout i ctx ha) oracle j k) ∧
          oracle (ScalarAttentionOuter.queryIndex (threadLayout i ctx ha) j+2*k+1) =
            .real .f32 (ScalarAttentionTrace.keyValues (threadLayout i ctx ha) oracle j k)) ∧
        oracle (ScalarAttentionOuter.queryIndex (threadLayout i ctx ha) j+2*i.dim) =
          .real .f32 (ScalarAttentionTrace.values (threadLayout i ctx ha) oracle j) := by
  obtain ⟨scale,hs⟩ := completed_scale_reply i ctx oracle hp hb hr hc hn ha.output64 hfull hd
  let l := threadLayout i ctx ha
  obtain ⟨entry,hprefix,hi⟩ := active_initialization i ctx oracle hp hb hr hc hn ha scale hs
    (ScalarAttentionTrace.scores l oracle scale) (ScalarAttentionTrace.values l oracle)
  obtain ⟨rest,tail,_,ht,_⟩ := complete_after_prefix hfull hd hprefix hi.running
  have hqueries := ScalarAttentionTrace.completed_replies l ctx oracle scale i.n (by simp [l,threadLayout]) hi ht hd
  exact ⟨scale,hs,fun j hj => hqueries j (Nat.zero_le _) hj⟩

theorem active_completed_shape (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : IndexBounds ctx)
    (hr : row ctx.block ctx.id < i.m) (hc : col ctx.block ctx.id < i.dim)
    (hn : 0 < i.n) (ha : AddressBounds i ctx)
    {n final events} (hfull : Scalar.run ctx oracle code n {} = .ok (final,events))
    (hd : final.core.thread.status = .done) :
    ∃ scale, oracle 0 = .real .f32 scale ∧ n = 35+i.n*(9*i.dim+26) ∧
      events = [.read ⟨.global,i.scale⟩ (Symbolic.encode .f32 scale)] ++
        (ScalarAttentionReads.reads (threadLayout i ctx ha)
          (ScalarAttentionTrace.qValues (threadLayout i ctx ha) oracle)
          (ScalarAttentionTrace.keyValues (threadLayout i ctx ha) oracle)
          (ScalarAttentionTrace.values (threadLayout i ctx ha) oracle) 0 i.n ++
        [.write ⟨.global,outputAddress i ctx⟩ (Symbolic.encode .f32
          (OnlineSoftmax.average (ScalarAttentionTrace.scores (threadLayout i ctx ha) oracle scale)
            (ScalarAttentionTrace.values (threadLayout i ctx ha) oracle) i.n))]) := by
  obtain ⟨scale,hs⟩ := completed_scale_reply i ctx oracle hp hb hr hc hn ha.output64 hfull hd
  let l := threadLayout i ctx ha
  obtain ⟨entry,hprefix,hi⟩ := active_initialization i ctx oracle hp hb hr hc hn ha scale hs
    (ScalarAttentionTrace.scores l oracle scale) (ScalarAttentionTrace.values l oracle)
  obtain ⟨rest,tail,he,ht,hev⟩ := complete_after_prefix hfull hd hprefix hi.running
  have hshape := ScalarAttentionTrace.completed_shape l ctx oracle scale hn hi ht hd
  have hrest : rest = i.n*(9*i.dim+26)-2 := hshape.1
  have hlarge := Nat.mul_le_mul_right (9*i.dim+26) (by omega : 1 ≤ i.n)
  simp only [Nat.one_mul] at hlarge
  have hcount : n = 35+i.n*(9*i.dim+26) := by omega
  rw [hshape.2] at hev
  exact ⟨scale,hs,hcount,hev⟩

theorem completed_source_cases (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : IndexBounds ctx)
    (hout : row ctx.block ctx.id < i.m → col ctx.block ctx.id < i.dim → outputAddress i ctx < 2^64)
    (ha : row ctx.block ctx.id < i.m → col ctx.block ctx.id < i.dim → 0 < i.n → AddressBounds i ctx)
    {n final events} (hfull : Scalar.run ctx oracle code n {} = .ok (final,events))
    (hd : final.core.thread.status = .done) :
    (i.m ≤ row ctx.block ctx.id ∧ n = 21 ∧ events = []) ∨
    (row ctx.block ctx.id < i.m ∧ i.dim ≤ col ctx.block ctx.id ∧ n = 23 ∧ events = []) ∨
    (row ctx.block ctx.id < i.m ∧ col ctx.block ctx.id < i.dim ∧ i.n = 0 ∧ n = 32 ∧
      events = [.write ⟨.global,outputAddress i ctx⟩ (Symbolic.encode .f32 0)]) ∨
    ∃ (hr : row ctx.block ctx.id < i.m) (hc : col ctx.block ctx.id < i.dim) (hn : 0 < i.n) (scale : ℝ),
      oracle 0 = .real .f32 scale ∧ n = 35+i.n*(9*i.dim+26) ∧
      events = [.read ⟨.global,i.scale⟩ (Symbolic.encode .f32 scale)] ++
        (ScalarAttentionReads.reads (threadLayout i ctx (ha hr hc hn))
          (ScalarAttentionTrace.qValues (threadLayout i ctx (ha hr hc hn)) oracle)
          (ScalarAttentionTrace.keyValues (threadLayout i ctx (ha hr hc hn)) oracle)
          (ScalarAttentionTrace.values (threadLayout i ctx (ha hr hc hn)) oracle) 0 i.n ++
        [.write ⟨.global,outputAddress i ctx⟩ (Symbolic.encode .f32
          (OnlineSoftmax.average (ScalarAttentionTrace.scores (threadLayout i ctx (ha hr hc hn)) oracle scale)
            (ScalarAttentionTrace.values (threadLayout i ctx (ha hr hc hn)) oracle) i.n))]) := by
  by_cases hr : row ctx.block ctx.id < i.m
  · by_cases hc : col ctx.block ctx.id < i.dim
    · by_cases hn : 0 < i.n
      · obtain ⟨scale,hs,hcount,hev⟩ := active_completed_shape i ctx oracle hp hb hr hc hn (ha hr hc hn) hfull hd
        exact .inr (.inr (.inr ⟨hr,hc,hn,scale,hs,hcount,hev⟩))
      · have hz : i.n = 0 := by omega
        obtain ⟨hcount,hev⟩ := empty_completed_shape i ctx oracle hp hb hr hc hz (hout hr hc) hfull hd
        exact .inr (.inr (.inl ⟨hr,hc,hz,hcount,hev⟩))
    · have hmask := Nat.le_of_not_gt hc
      obtain ⟨last,hmasked,hmd,_⟩ := masked_col i ctx oracle hp hb hr hmask
      have he := Scalar.complete_run_unique hfull hd hmasked hmd
      exact .inr (.inl ⟨hr,hmask,he.1,he.2.2⟩)
  · have hmask := Nat.le_of_not_gt hr
    obtain ⟨last,hmasked,hmd,_⟩ := masked_row i ctx oracle hp hb hmask
    have he := Scalar.complete_run_unique hfull hd hmasked hmd
    exact .inl ⟨hmask,he.1,he.2.2⟩

end
end Ptx.ScalarAttentionInit
