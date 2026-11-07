import Ptx.Scalar.Rules

/-! Local rules for GPU-scoped relaxed global u32 atomic addition. Return values
are oracle-driven and unconstrained by these rules; scoped memory consistency and
RMW atomicity must separately justify them. A single emitted event has both byte
projections. Evaluation precedes destination assignment, so operand aliasing is
allowed. These are not sequentially-consistent heap updates. -/
namespace Ptx.Scalar
open Ptx.ISA
noncomputable section

theorem atom_add_u32_step {ctx oracle code s dst address increment addr addend value}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.atomAddU32 dst address increment))
    (ha : evalAddr ctx.id.tid.x s.core.thread address = .ok addr)
    (hi : Ptx.eval ctx.id.tid.x s.core.thread increment = .ok addend)
    (ho : oracle s.core.queries = .integer value) :
    step ctx oracle code s = .ok
      (finishInteger s {s.core with thread := assign s.core.thread dst (wrap 32 value),queries := s.core.queries+1},
        [.rmw .gpu (Location.resolve .global ctx.id addr) (atomicAddBytes value addend)]) := by
  simp [step,hr,hc,ha,hi,ho,require,liftInteger,bind,Except.bind,pure,Except.pure]

theorem atom_add_reply_integer {ctx oracle code s dst address increment next events}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.atomAddU32 dst address increment))
    (hs : step ctx oracle code s = .ok (next,events)) :
    ∃ value, oracle s.core.queries = .integer value := by
  cases ha : evalAddr ctx.id.tid.x s.core.thread address with
  | error fault => simp [step,hr,hc,ha,require,liftInteger,bind,Except.bind] at hs
  | ok addr =>
    cases hi : Ptx.eval ctx.id.tid.x s.core.thread increment with
    | error fault => simp [step,hr,hc,ha,hi,require,liftInteger,bind,Except.bind] at hs
    | ok addend =>
      cases ho : oracle s.core.queries with
      | integer value => exact ⟨value,rfl⟩
      | real format value =>
        simp [step,hr,hc,ha,hi,ho,require,liftInteger,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs

theorem atomic_bytes_size (old increment : Nat) :
    (atomicAddBytes old increment).before.length = 4 ∧ (atomicAddBytes old increment).after.length = 4 := by
  simp [atomicAddBytes]

theorem atom_add_result {ctx oracle code s dst address increment addr addend value next events}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.atomAddU32 dst address increment))
    (ha : evalAddr ctx.id.tid.x s.core.thread address = .ok addr)
    (hi : Ptx.eval ctx.id.tid.x s.core.thread increment = .ok addend)
    (ho : oracle s.core.queries = .integer value)
    (hs : step ctx oracle code s = .ok (next,events)) :
    lookup dst next.core.thread.regs = some (wrap 32 value) ∧
    wrap 32 value < 2^32 ∧ declarationLookup dst next.floats = none ∧
    next.core.queries = s.core.queries+1 ∧ next.core.thread.pc = s.core.thread.pc+1 ∧
    events = [.rmw .gpu (Location.resolve .global ctx.id addr) (atomicAddBytes value addend)] := by
  rw [atom_add_u32_step hr hc ha hi ho] at hs
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj hs)
  refine ⟨lookup_put_same _ _ _,by exact Nat.mod_lt value (by decide),?_,rfl,rfl,rfl⟩
  apply finish_integer_invalidates_float
  simp [assign,lookup,put]

end
end Ptx.Scalar
