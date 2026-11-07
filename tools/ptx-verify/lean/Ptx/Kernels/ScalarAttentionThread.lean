import Ptx.Kernels.ScalarAttentionEntry
import Ptx.Kernels.ScalarAttentionOracle

/-! Parameterized PC=0 source execution, with both masks, empty keys and the
nonempty nested loop. This is local source completion, not a consistent global
candidate or a universal observed-memory contract. -/
namespace Ptx.ScalarAttentionInit
open Ptx.ISA Ptx.Scalar Ptx.ScalarAttention
noncomputable section

theorem output_prefix (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : IndexBounds ctx)
    (hr : row ctx.block ctx.id < i.m) (hc : col ctx.block ctx.id < i.dim)
    (hout : outputAddress i ctx < 2^64) :
    ∃ ready, Scalar.run ctx oracle code 28 {} = .ok (ready,[]) ∧ Ready i ctx 28 ready := by
  obtain ⟨hprefix,hi⟩ := active_prefix i ctx oracle hp hb hr hc
  obtain ⟨ready,haddr,hready⟩ := output_initialization i ctx oracle hi hb hout
  exact ⟨ready,Scalar.run_append hprefix haddr,hready⟩

theorem empty_execution (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : IndexBounds ctx)
    (hr : row ctx.block ctx.id < i.m) (hc : col ctx.block ctx.id < i.dim)
    (hz : i.n = 0) (hout : outputAddress i ctx < 2^64) :
    ∃ final, Scalar.run ctx oracle code 32 {} = .ok
      (final,[.write ⟨.global,outputAddress i ctx⟩ (Symbolic.encode .f32 0)]) ∧
      final.core.thread.status = .done ∧ final.core.queries = 0 := by
  obtain ⟨ready,hprefix,hi⟩ := output_prefix i ctx oracle hp hb hr hc hout
  have hguard : Scalar.run ctx oracle code 2 ready = .ok (afterGuard ready 1 74,[]) := by
    simpa only [hz,ite_true] using empty_guard_run i ctx oracle hi
  have hg := after_guard_ready hi 1 74
  obtain ⟨final,ht,hd,hq⟩ := empty_store_return i ctx oracle hg hout
  exact ⟨final,Scalar.run_append (Scalar.run_append hprefix hguard) ht,hd,hq⟩

theorem empty_completed_shape (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : IndexBounds ctx)
    (hr : row ctx.block ctx.id < i.m) (hc : col ctx.block ctx.id < i.dim)
    (hz : i.n = 0) (hout : outputAddress i ctx < 2^64)
    {n final events} (hfull : Scalar.run ctx oracle code n {} = .ok (final,events))
    (hd : final.core.thread.status = .done) : n = 32 ∧
      events = [.write ⟨.global,outputAddress i ctx⟩ (Symbolic.encode .f32 0)] := by
  obtain ⟨last,he,hld,_⟩ := empty_execution i ctx oracle hp hb hr hc hz hout
  have h := Scalar.complete_run_unique hfull hd he hld
  exact ⟨h.1,h.2.2⟩

theorem active_initialization (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (hp : Params i ctx.params) (hb : IndexBounds ctx)
    (hr : row ctx.block ctx.id < i.m) (hc : col ctx.block ctx.id < i.dim)
    (hn : 0 < i.n) (ha : AddressBounds i ctx) (scale : ℝ) (ho : oracle 0 = .real .f32 scale)
    (score value : Nat → ℝ) :
    ∃ entry, Scalar.run ctx oracle code 37 {} = .ok
      (entry,[.read ⟨.global,i.scale⟩ (Symbolic.encode .f32 scale)]) ∧
      ScalarAttentionOuter.Inv (threadLayout i ctx ha) score value scale 0 entry := by
  obtain ⟨ready,hprefix,hi⟩ := output_prefix i ctx oracle hp hb hr hc ha.output64
  have hguard : Scalar.run ctx oracle code 2 ready = .ok (afterGuard ready 0 30,[]) := by
    simpa only [ite_eq_right hn.ne'] using empty_guard_run i ctx oracle hi
  have hg := after_guard_ready hi 0 30
  obtain ⟨entry,ht,hentry⟩ := loop_initialization i ctx oracle hg hb ha scale ho score value
  exact ⟨entry,Scalar.run_append (Scalar.run_append hprefix hguard) ht,hentry⟩

theorem active_execution (i : Inputs) (ctx : Scalar.Context) (q key value : Attention.Matrix) (scale : ℝ)
    (hp : Params i ctx.params) (hb : IndexBounds ctx)
    (hr : row ctx.block ctx.id < i.m) (hc : col ctx.block ctx.id < i.dim)
    (hn : 0 < i.n) (ha : AddressBounds i ctx) :
    ∃ final, Scalar.run ctx (ScalarAttentionOracle.answers q key value (row ctx.block ctx.id) (col ctx.block ctx.id) i.dim scale)
      code (35+i.n*(9*i.dim+26)) {} = .ok
        (final,[.read ⟨.global,i.scale⟩ (Symbolic.encode .f32 scale)] ++
          (ScalarAttentionOuter.suffixReads (threadLayout i ctx ha) q key value (row ctx.block ctx.id) (col ctx.block ctx.id) 0 i.n ++
            [.write ⟨.global,outputAddress i ctx⟩ (Symbolic.encode .f32
              (Attention.output q key value (Real.log 2*scale) (row ctx.block ctx.id) (col ctx.block ctx.id) i.n i.dim))])) ∧
      final.core.thread.status = .done := by
  let l := threadLayout i ctx ha
  let r := row ctx.block ctx.id
  let c := col ctx.block ctx.id
  let answers := ScalarAttentionOracle.answers q key value r c i.dim scale
  obtain ⟨entry,hprefix,hi⟩ := active_initialization i ctx answers hp hb hr hc hn ha scale rfl
    (ScalarAttentionOuter.scores l q key scale r) (fun item => value item c)
  obtain ⟨final,hloop,hf⟩ := ScalarAttentionOuter.complete_from_loop_entry l ctx answers q key value r c scale hn
    (fun j k _ hk => ScalarAttentionOracle.q_reply q key value r c i.dim j k scale hk)
    (fun j k _ hk => ScalarAttentionOracle.key_reply q key value r c i.dim j k scale hk)
    (fun j _ => ScalarAttentionOracle.value_reply q key value r c i.dim j scale) hi
  have hfull := Scalar.run_append hprefix hloop
  have hlarge := Nat.mul_le_mul_right (9*i.dim+26) (by omega : 1 ≤ i.n)
  simp only [Nat.one_mul] at hlarge
  have hcount : 37+(i.n*(9*i.dim+26)-2) = 35+i.n*(9*i.dim+26) := by omega
  change Scalar.run ctx answers code (37+(i.n*(9*i.dim+26)-2)) {} = _ at hfull
  rw [hcount] at hfull
  exact ⟨final,hfull,hf⟩

end
end Ptx.ScalarAttentionInit
