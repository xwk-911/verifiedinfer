import Ptx.Kernels.ScalarMatmulAddress

/-! Full-source local execution and completed-trace reconstruction for arbitrary
threads and dimensions. Bounds and parameter matching are explicit. These local
traces do not assert initial matrix memory, global consistency or observer output.
-/
namespace Ptx.ScalarMatmulInit
open Ptx.ISA Ptx.Scalar Ptx.ScalarMatmul Ptx.ScalarMatmulLoop
noncomputable section

theorem active_initialization (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : IndexBounds ctx)
    (hr : row ctx.block ctx.id < i.m) (hn : col ctx.block ctx.id < i.n) (ha : AddressBounds i ctx) :
    ∃ entry, Scalar.run ctx oracle code 32 {} = .ok (entry,[]) ∧ Inv (threadLayout i ctx ha) 0 0 entry := by
  obtain ⟨hprefix,hfacts⟩ := active_prefix i ctx oracle hp hb hr hn
  obtain ⟨entry,haddress,hinv⟩ := address_run i ctx oracle hfacts hb ha
  exact ⟨entry,Scalar.run_append hprefix haddress,hinv⟩

theorem active_execution (i : Inputs) (ctx : Scalar.Context) (a b : Matrix)
    (hp : Params i ctx.params) (hb : IndexBounds ctx)
    (hr : row ctx.block ctx.id < i.m) (hn : col ctx.block ctx.id < i.n) (ha : AddressBounds i ctx) :
    ∃ final, Scalar.run ctx (inputOracle a b (row ctx.block ctx.id) (col ctx.block ctx.id)) code (36+9*i.k) {} =
      .ok (final,loopReads (threadLayout i ctx ha) a b (row ctx.block ctx.id) (col ctx.block ctx.id) 0 i.k ++
        [.write ⟨.global,(threadLayout i ctx ha).output⟩
          (Symbolic.encode .f32 (prefixProduct a b (row ctx.block ctx.id) (col ctx.block ctx.id) i.k))]) ∧
      Finished (threadLayout i ctx ha) (prefixProduct a b (row ctx.block ctx.id) (col ctx.block ctx.id) i.k) final := by
  let r := row ctx.block ctx.id
  let c := col ctx.block ctx.id
  let answers := inputOracle a b r c
  obtain ⟨entry,hprefix,hi⟩ := active_initialization i ctx answers hp hb hr hn ha
  obtain ⟨final,hloop,hf⟩ := complete_from_entry (threadLayout i ctx ha) ctx answers a b r c
    (fun k _ => inputOracle_even a b r c k) (fun k _ => inputOracle_odd a b r c k) hi
  have hfull := Scalar.run_append hprefix hloop
  have hcount : 32+(9*(threadLayout i ctx ha).count+4) = 36+9*i.k := by change 32+(9*i.k+4) = _; omega
  rw [hcount,List.nil_append] at hfull
  exact ⟨final,hfull,hf⟩

theorem active_completed_shape (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : IndexBounds ctx)
    (hr : row ctx.block ctx.id < i.m) (hn : col ctx.block ctx.id < i.n) (ha : AddressBounds i ctx)
    {n : Nat} {final : Scalar.State} {events : List Scalar.Kind}
    (hfull : Scalar.run ctx oracle code n {} = .ok (final,events)) (hd : final.core.thread.status = .done) :
    n = 36+9*i.k ∧
      events = loopReads (threadLayout i ctx ha) (replyA oracle) (replyB oracle) 0 0 0 i.k ++
        [.write ⟨.global,(threadLayout i ctx ha).output⟩
          (Symbolic.encode .f32 (prefixProduct (replyA oracle) (replyB oracle) 0 0 i.k))] := by
  obtain ⟨entry,hprefix,hi⟩ := active_initialization i ctx oracle hp hb hr hn ha
  have hcount := completed_after_running_prefix hfull hd hprefix hi.running
  obtain ⟨remaining,tailEvents,he,hrest,hev⟩ := successful_suffix (by omega : 32 ≤ n) hprefix hfull
  have hs := completed_shape (threadLayout i ctx ha) ctx oracle hi hrest hd
  refine ⟨?_,?_⟩
  · have hrestcount : remaining = 9*i.k+4 := hs.1
    omega
  · simpa only [List.nil_append,hs.2.1,show (threadLayout i ctx ha).count = i.k from rfl] using hev

theorem completed_source_cases (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : IndexBounds ctx)
    (ha : row ctx.block ctx.id < i.m → col ctx.block ctx.id < i.n → AddressBounds i ctx)
    {n : Nat} {final : Scalar.State} {events : List Scalar.Kind}
    (hfull : Scalar.run ctx oracle code n {} = .ok (final,events)) (hd : final.core.thread.status = .done) :
    (i.m ≤ row ctx.block ctx.id ∧ n = 19 ∧ events = []) ∨
    (row ctx.block ctx.id < i.m ∧ i.n ≤ col ctx.block ctx.id ∧ n = 21 ∧ events = []) ∨
    ∃ (hr : row ctx.block ctx.id < i.m) (hn : col ctx.block ctx.id < i.n), n = 36+9*i.k ∧
      events = loopReads (threadLayout i ctx (ha hr hn)) (replyA oracle) (replyB oracle) 0 0 0 i.k ++
        [.write ⟨.global,(threadLayout i ctx (ha hr hn)).output⟩
          (Symbolic.encode .f32 (prefixProduct (replyA oracle) (replyB oracle) 0 0 i.k))] := by
  by_cases hr : row ctx.block ctx.id < i.m
  · by_cases hn : col ctx.block ctx.id < i.n
    · exact .inr (.inr ⟨hr,hn,active_completed_shape i ctx oracle hp hb hr hn (ha hr hn) hfull hd⟩)
    · have hmask := Nat.le_of_not_gt hn
      obtain ⟨last,hmasked,hmd,_⟩ := masked_col i ctx oracle hp hb hr hmask
      have he := Scalar.complete_run_unique hfull hd hmasked hmd
      exact .inr (.inl ⟨hr,hmask,he.1,he.2.2⟩)
  · have hmask := Nat.le_of_not_gt hr
    obtain ⟨last,hmasked,hmd,_⟩ := masked_row i ctx oracle hp hb hmask
    have he := Scalar.complete_run_unique hfull hd hmasked hmd
    exact .inl ⟨hmask,he.1,he.2.2⟩

end
end Ptx.ScalarMatmulInit
