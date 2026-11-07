import Ptx.Kernels.ScalarAttentionDot
import Ptx.Scalar.Replies

/-! Extract typed load replies from arbitrary successful completed executions.
No correct-input oracle or execution bound is assumed. Initial loop invariants
and layout bounds remain explicit; global memory contracts are separate.
-/
namespace Ptx.ScalarAttentionDot
open Ptx.ISA Ptx.Scalar
noncomputable section

def guarded (s : Scalar.State) : Scalar.State := intPC (intAssign s "%p" 0) 45

theorem guard_run (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {k : Nat} {acc : ℝ} {s : Scalar.State} (hi : Inv l k acc s) (hk : k < l.count) :
    Scalar.run ctx oracle code 2 s = .ok (guarded s,[]) := by
  have hk32 : wrap 32 k = k := Nat.mod_eq_of_lt (by have := l.count32; omega)
  have hK32 : wrap 32 l.count = l.count := Nat.mod_eq_of_lt l.count32
  have h43 : Scalar.step ctx oracle code s = .ok (intAssign s "%p" 0,[]) := by
    apply Scalar.integer_local_step hi.running (by rw [hi.pc]; rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,hi.index,hi.bound,hk32,hK32,Nat.not_le_of_lt hk,
      bind,Except.bind,pure,Except.pure]
  have h44 : Scalar.step ctx oracle code (intAssign s "%p" 0) = .ok (guarded s,[]) := by
    apply Scalar.integer_local_step (instruction := .branch "%p" true 52)
      (by simpa [intAssign,finishInteger,assign,advance] using hi.running)
      (by simp [intAssign,finishInteger,assign,advance,hi.pc,code,Generated.scalar_flash_attention.program])
      rfl (by intro bid h; cases h)
    simp [localStep,intAssign,finishInteger,assign,advance,hi.pc,bind,Except.bind,pure,Except.pure]
  simp [Scalar.run,h43,h44,Except.bind]

theorem completed_iteration_replies (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {k n : Nat} {acc : ℝ} {s final : Scalar.State} {events : List Scalar.Kind}
    (hi : Inv l k acc s) (hk : k < l.count)
    (hr : Scalar.run ctx oracle code n s = .ok (final,events)) (hd : final.core.thread.status = .done) :
    ∃ a b, oracle (l.firstQuery+2*k) = .real .f32 a ∧ oracle (l.firstQuery+2*k+1) = .real .f32 b := by
  have hguard := guard_run l ctx oracle hi hk
  have hgr : (guarded s).core.thread.status = .running := by
    simpa [guarded,intPC,intAssign,finishInteger,assign,advance] using hi.running
  obtain ⟨mid,emitted,hstep⟩ := step_after_running_prefix hr hd hguard hgr
  obtain ⟨a,hquery⟩ := real_reply_of_successful_load hgr (show code[(guarded s).core.thread.pc]? =
    some (.load .f32 .global "%qv" {base := .reg "%qp"}) from rfl) hstep
  have hqa : oracle (l.firstQuery+2*k) = .real .f32 a := by
    simpa [guarded,intPC,intAssign,finishInteger,hi.queries] using hquery
  let loaded := loadedFloat (guarded s) "%qv" a
  have hload : Scalar.step ctx oracle code (guarded s) =
      .ok (loaded,[.read ⟨.global,l.qBase+4*k⟩ (Symbolic.encode .f32 a)]) := by
    apply Scalar.load_step (space := .global) (format := .f32) (dst := "%qv")
      (address := {base := .reg "%qp"}) (addr := l.qBase+4*k) (value := a)
    · exact hgr
    · rfl
    · have h64 : wrap 64 (l.qBase+4*k) = l.qBase+4*k := Nat.mod_eq_of_lt (l.qRead64 k hk)
      simp [evalAddr,Ptx.eval,guarded,hi.qPointer,h64,bind,Except.bind,pure,Except.pure]
    · exact hquery
  have h3 : Scalar.run ctx oracle code 3 s =
      .ok (loaded,[.read ⟨.global,l.qBase+4*k⟩ (Symbolic.encode .f32 a)]) := by
    rw [show 3 = 2+1 by decide,Scalar.run_add,hguard]
    simp [Scalar.run,hload,Except.bind]
  have hlr : loaded.core.thread.status = .running := by
    simpa [loaded,loadedFloat,writeFloat,advance] using hgr
  obtain ⟨next,more,hsecond⟩ := step_after_running_prefix hr hd h3 hlr
  obtain ⟨b,hqb⟩ := real_reply_of_successful_load hlr (show code[loaded.core.thread.pc]? =
    some (.load .f32 .global "%kv" {base := .reg "%kp"}) from rfl) hsecond
  refine ⟨a,b,hqa,?_⟩
  simpa [loaded,loadedFloat,writeFloat,guarded,intPC,intAssign,finishInteger,hi.queries] using hqb

/-- Completion of the whole source forces f32 replies for every remaining
inner-loop load. The instruction count and oracle are not preselected. -/
theorem completed_replies (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (remaining : Nat) : ∀ {start n acc s final events}, l.count = start+remaining → Inv l start acc s →
      Scalar.run ctx oracle code n s = .ok (final,events) → final.core.thread.status = .done →
      ∀ k, start ≤ k → k < l.count →
        oracle (l.firstQuery+2*k) = .real .f32 (replyReal oracle (l.firstQuery+2*k)) ∧
        oracle (l.firstQuery+2*k+1) = .real .f32 (replyReal oracle (l.firstQuery+2*k+1)) := by
  induction remaining with
  | zero => intro start n acc s final events he hi hr hd k hstart hk; omega
  | succ count ih =>
    intro start n acc s final events he hi hr hd k hstart hk
    have hactive : start < l.count := by omega
    obtain ⟨a,b,ha,hb⟩ := completed_iteration_replies l ctx oracle hi hactive hr hd
    by_cases heq : k = start
    · subst k
      exact ⟨typed_reply_projection ⟨a,ha⟩,typed_reply_projection ⟨b,hb⟩⟩
    · obtain ⟨mid,hm,hmid,_⟩ := iteration l ctx oracle hi hactive ha hb
      obtain ⟨rest,tail,_,ht,_⟩ := complete_after_prefix hr hd hm hmid.running
      exact ih (by omega : l.count = (start+1)+count) hmid ht hd k (by omega) hk

end
end Ptx.ScalarAttentionDot
