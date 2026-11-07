import Ptx.Kernels.AtomicDispatchBody

/-! Arbitrary-oracle full-source completion and reconstruction. No memory
consistency is assumed here, so tickets other than 0/1 remain locally legal. -/
namespace Ptx.AtomicDispatchTrace
open Ptx.ISA Ptx.Scalar
noncomputable section

def events (counter x y value : Nat) : List Scalar.Kind :=
  [.rmw .gpu ⟨.global,counter⟩ (atomicAddBytes value 1)] ++ outputEvents x y (wrap 32 value)
def sourceCount (value : Nat) : Nat := 4+bodyCount (wrap 32 value)

theorem translated_trace (ctx : Scalar.Context) (oracle : Scalar.Oracle) (counter x y value : Nat)
    (hp : Params counter x y ctx.params) (hc : counter < 2^64) (hx : x < 2^64) (hy : y < 2^64)
    (ho : oracle 0 = .integer value) :
    Scalar.run ctx oracle code (sourceCount value) {} =
      .ok (finalState counter x y (wrap 32 value),events counter x y value) := by
  have hpref := translated_atomic_prefix ctx oracle counter x y value hp hc hx hy ho
  rw [after_atomic_entry] at hpref
  exact Scalar.run_append hpref (body_run ctx oracle counter x y (wrap 32 value) (Nat.mod_lt _ (by decide)) hx hy)

theorem completed_source_shape (ctx : Scalar.Context) (oracle : Scalar.Oracle) (counter x y : Nat)
    (hp : Params counter x y ctx.params) (hc : counter < 2^64) (hx : x < 2^64) (hy : y < 2^64)
    {count : Nat} {final : Scalar.State} {allEvents : List Scalar.Kind}
    (hrun : Scalar.run ctx oracle code count {} = .ok (final,allEvents)) (hd : final.core.thread.status = .done) :
    ∃ value, oracle 0 = .integer value ∧ count = sourceCount value ∧
      final = finalState counter x y (wrap 32 value) ∧ allEvents = events counter x y value := by
  have hpref := parameters_run ctx oracle counter x y hp hc hx hy
  obtain ⟨next,emitted,hstep⟩ := Scalar.step_after_running_prefix hrun hd hpref rfl
  obtain ⟨value,ho⟩ := Scalar.atom_add_reply_integer rfl rfl hstep
  have hfull := translated_trace ctx oracle counter x y value hp hc hx hy ho
  have he := Scalar.complete_run_unique hrun hd hfull (final_done counter x y (wrap 32 value))
  exact ⟨value,ho,he.1,he.2.1,he.2.2⟩

theorem source_count (value : Nat) : sourceCount value = if wrap 32 value = 1 then 11 else 10 := by
  simp only [sourceCount,bodyCount]
  split <;> rfl

theorem source_queries (counter x y value : Nat) : (finalState counter x y (wrap 32 value)).core.queries = 1 := by
  unfold finalState
  split
  · rfl
  · split <;> rfl

theorem completed_bad_reply_impossible (ctx : Scalar.Context) (oracle : Scalar.Oracle) (counter x y : Nat)
    (hp : Params counter x y ctx.params) (hc : counter < 2^64) (hx : x < 2^64) (hy : y < 2^64)
    {format : Symbolic.Format} {value : ℝ} (hbad : oracle 0 = .real format value)
    {count final allEvents} (hrun : Scalar.run ctx oracle code count {} = .ok (final,allEvents)) :
    final.core.thread.status ≠ .done := by
  intro hd
  obtain ⟨reply,ho,_,_,_⟩ := completed_source_shape ctx oracle counter x y hp hc hx hy hrun hd
  rw [hbad] at ho
  cases ho

end
end Ptx.AtomicDispatchTrace
