import Ptx.Kernels.ScalarAttentionReads
import Ptx.Kernels.ScalarAttentionDotTrace

/-! Reconstruction of EVERY successful completed nonempty attention suffix.
The actual oracle and count remain arbitrary. Per-item Q replies need not agree
until memory reasoning establishes immutable input correspondence. -/
namespace Ptx.ScalarAttentionTrace
open Ptx.ISA Ptx.Scalar Ptx.ScalarAttentionOuter
noncomputable section

def qValues (l : Layout) (oracle : Scalar.Oracle) : Attention.Matrix :=
  fun j k => replyReal oracle (queryIndex l j+2*k)
def keyValues (l : Layout) (oracle : Scalar.Oracle) : Attention.Matrix :=
  fun j k => replyReal oracle (queryIndex l j+2*k+1)
def values (l : Layout) (oracle : Scalar.Oracle) : Nat → ℝ :=
  fun j => replyReal oracle (queryIndex l j+2*l.dim)
def scores (l : Layout) (oracle : Scalar.Oracle) (scale : ℝ) : Nat → ℝ :=
  ScalarAttentionReads.score l (qValues l oracle) (keyValues l oracle) scale

theorem completed_iteration_replies (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {score value scale j s n final events} (hi : Inv l score value scale j s) (hj : j < l.keys)
    (hr : Scalar.run ctx oracle code n s = .ok (final,events)) (hd : final.core.thread.status = .done) :
    (∀ k, k < l.dim →
      oracle (queryIndex l j+2*k) = .real .f32 (qValues l oracle j k) ∧
      oracle (queryIndex l j+2*k+1) = .real .f32 (keyValues l oracle j k)) ∧
      oracle (queryIndex l j+2*l.dim) = .real .f32 (values l oracle j) := by
  obtain ⟨ready,hstart,hready,hframe⟩ := start_dot l ctx oracle hi hj
  obtain ⟨remaining,tail,_,ht,_⟩ := complete_after_prefix hr hd hstart hready.running
  have hqueries := ScalarAttentionDot.completed_replies (dotLayout l j hj) ctx oracle l.dim
    (by simp [dotLayout]) hready ht hd
  have hq : ∀ k, k < l.dim → oracle (queryIndex l j+2*k) = .real .f32 (qValues l oracle j k) := by
    intro k hk
    exact (hqueries k (Nat.zero_le _) hk).1
  have hk : ∀ k, k < l.dim → oracle (queryIndex l j+2*k+1) = .real .f32 (keyValues l oracle j k) := by
    intro k hk
    exact (hqueries k (Nat.zero_le _) hk).2
  have hscale : declarationLookup "%scale" ready.floats = some (.f32,scale) :=
    ((hframe "%scale" (by decide)).2).trans hi.scaling
  obtain ⟨scored,hdot,hscored,_⟩ := ScalarAttentionDot.complete_scaled_score (dotLayout l j hj)
    ctx oracle (qValues l oracle) (keyValues l oracle) j j scale hq hk hready hscale
  have hprefix := Scalar.run_append hstart hdot
  obtain ⟨next,emitted,hstep⟩ := step_after_running_prefix hr hd hprefix hscored.running
  obtain ⟨v,hv⟩ := real_reply_of_successful_load hscored.running
    (show code[scored.core.thread.pc]? = some (.load .f32 .global "%vv" {base := .reg "%vp"}) from by rw [hscored.pc]; rfl) hstep
  refine ⟨fun k hk0 => ⟨hq k hk0,hk k hk0⟩,?_⟩
  apply typed_reply_projection
  exact ⟨v,by simpa only [hscored.queries,dotLayout] using hv⟩

theorem completed_replies (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle) (scale : ℝ)
    (remaining : Nat) : ∀ {start n s final events}, l.keys = start+remaining →
      Inv l (scores l oracle scale) (values l oracle) scale start s →
      Scalar.run ctx oracle code n s = .ok (final,events) → final.core.thread.status = .done →
      ∀ j, start ≤ j → j < l.keys →
        (∀ k, k < l.dim → oracle (queryIndex l j+2*k) = .real .f32 (qValues l oracle j k) ∧
          oracle (queryIndex l j+2*k+1) = .real .f32 (keyValues l oracle j k)) ∧
        oracle (queryIndex l j+2*l.dim) = .real .f32 (values l oracle j) := by
  induction remaining with
  | zero => intro start n s final events he hi hr hd j hstart hj; omega
  | succ count ih =>
    intro start n s final events he hi hr hd j hstart hj
    have hactive : start < l.keys := by omega
    obtain ⟨hcurrent,hvalue⟩ := completed_iteration_replies l ctx oracle hi hactive hr hd
    by_cases heq : j = start
    · subst j; exact ⟨hcurrent,hvalue⟩
    · obtain ⟨mid,hm,hmid,_⟩ := iteration_for_score l ctx oracle (qValues l oracle) (keyValues l oracle)
        (fun item _ => values l oracle item) start 0 scale (scores l oracle scale) hi hactive rfl
        (fun k hk => (hcurrent k hk).1) (fun k hk => (hcurrent k hk).2) hvalue
      obtain ⟨rest,tail,_,ht,_⟩ := complete_after_prefix hr hd hm hmid.running
      exact ih (by omega : l.keys = (start+1)+count) hmid ht hd j (by omega) hj

theorem completed_shape (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle) (scale : ℝ)
    (hkeys : 0 < l.keys) {n s final events}
    (hi : Inv l (scores l oracle scale) (values l oracle) scale 0 s)
    (hr : Scalar.run ctx oracle code n s = .ok (final,events)) (hd : final.core.thread.status = .done) :
    n = l.keys*(9*l.dim+26)-2 ∧
      events = ScalarAttentionReads.reads l (qValues l oracle) (keyValues l oracle) (values l oracle) 0 l.keys ++
        [.write ⟨.global,l.output⟩ (Symbolic.encode .f32 (OnlineSoftmax.average (scores l oracle scale) (values l oracle) l.keys))] := by
  have hqueries := completed_replies l ctx oracle scale l.keys (by omega : l.keys = 0+l.keys) hi hr hd
  obtain ⟨last,hfull,hfinish⟩ := ScalarAttentionReads.complete_from_entry l ctx oracle
    (qValues l oracle) (keyValues l oracle) (values l oracle) scale hkeys
    (fun j k hj hk => ((hqueries j (Nat.zero_le _) hj).1 k hk).1)
    (fun j k hj hk => ((hqueries j (Nat.zero_le _) hj).1 k hk).2)
    (fun j hj => (hqueries j (Nat.zero_le _) hj).2) hi
  have he := Scalar.complete_run_unique hr hd hfull hfinish
  exact ⟨he.1,he.2.2⟩

end
end Ptx.ScalarAttentionTrace
