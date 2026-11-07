import Ptx.ISA.Launch

/-! Scopes for the current single-device launch model. GPU/system scope both
contain every launch thread; this is not a multi-device or host memory model. -/
namespace Ptx.ISA

inductive Scope
  | cta
  | gpu
  | sys
  deriving Repr, DecidableEq

def Scope.Includes : Scope → ThreadId → ThreadId → Prop
  | .cta, owner, peer => owner.cta = peer.cta
  | .gpu, _, _ | .sys, _, _ => True

instance (scope owner peer) : Decidable (Scope.Includes scope owner peer) := by
  cases scope <;> simp only [Scope.Includes] <;> infer_instance

theorem Scope.includes_self (scope : Scope) (owner : ThreadId) : scope.Includes owner owner := by
  cases scope <;> simp [Scope.Includes]

end Ptx.ISA
