import Ptx.Hopper.WgmmaTmaSteps
import Ptx.Scalar.Rules

/-! Source stores, barrier invalidation and return through the WGMMA layer.
Stores emit typed bytes without mutating a source heap. Memory/resource legality
and observable final values require separate graph admission. -/
namespace Ptx.Hopper.Wgmma
open Ptx.ISA
noncomputable section

theorem float_store_step {ctx oracle code s format space address value addr x}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.store format space address value))))
    (hp : pending s.ledger = [])
    (ha : evalAddr ctx.id.tid.x s.base.scalar.core.thread address = .ok addr)
    (hv : Scalar.eval format s.base.scalar value = .ok x) :
    step ctx oracle code s = .ok
      (advanceOrdinary s (.ampere (.scalar (.store format space address value))),
       [.base (.ampere (.ordinary (.write (Location.resolve space ctx.id addr) (Symbolic.encode format x))))]) := by
  have hs := Scalar.store_step (oracle := oracle.base.ampere.scalar) hr
    (Ampere.scalarSkeleton_slot (Hopper.ampereSkeleton_slot hi)) ha hv
  have ha' := Ampere.scalar_step (oracle := oracle.base.ampere) hr (Hopper.ampereSkeleton_slot hi) hs
  have hh := Hopper.embedded_step (oracle := oracle.base) hr hi ha'
  simpa [advanceOrdinary,ordinaryState,Ampere.finishScalar,Ampere.scalarWritten,Ampere.advance] using
    ordinary_step hr hi (by intro wg he; cases he) (no_pending_names hp _) hh

theorem invalidate_step {ctx oracle code s address addr}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some (.mbarrierInval address))
    (hp : pending s.ledger = [])
    (ha : evalAddr ctx.id.tid.x s.base.scalar.core.thread address = .ok addr) :
    step ctx oracle code s = .ok
      (advanceOrdinary s (.mbarrierInval address),[.base (.barrier ⟨⟨.shared ctx.id.cta,addr⟩,.inval⟩)]) := by
  have hh := Hopper.inval_step (oracle := oracle.base) hr hi ha
  simpa [advanceOrdinary,ordinaryState] using ordinary_step hr hi (by intro wg he; cases he) (no_pending_names hp _) hh

def returnState (s : State) : State :=
  ordinaryState s (.ampere (.scalar (.integer .ret)))
    (Ampere.finishScalar s.base (.integer .ret)
      (Scalar.finishInteger s.base.scalar {s.base.scalar.core with thread := {s.base.scalar.core.thread with status := .done}}))

theorem return_step {ctx oracle code s}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer .ret))))
    (hp : pending s.ledger = []) : step ctx oracle code s = .ok (returnState s,[]) := by
  exact integer_local_step hr hi hp rfl (by intro bid he; cases he) rfl

@[simp] theorem returnState_status (s : State) : (returnState s).base.scalar.core.thread.status = .done := rfl
@[simp] theorem returnState_pc (s : State) : (returnState s).base.scalar.core.thread.pc = s.base.scalar.core.thread.pc := rfl
@[simp] theorem returnState_queries (s : State) : (returnState s).base.scalar.core.queries = s.base.scalar.core.queries := rfl
@[simp] theorem returnState_pending (s : State) : pending (returnState s).ledger = pending s.ledger := rfl
@[simp] theorem returnState_nat (s : State) (name : String) :
    lookup name (returnState s).base.scalar.core.thread.regs = lookup name s.base.scalar.core.thread.regs := rfl

theorem return_complete (s : State) (hp : pending s.ledger = []) : Complete (returnState s) := ⟨rfl,hp⟩

end
end Ptx.Hopper.Wgmma
