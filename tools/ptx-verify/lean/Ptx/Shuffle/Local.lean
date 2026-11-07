import Ptx.Shuffle.Rules
import Ptx.Scalar.Rules
import Ptx.Scalar.Updates

/-! Conservative local delegation rules for ordinary scalar slots in an actual
shuffle program. Fetch PCs are retained; shuffle slots are never erased. -/
namespace Ptx.Shuffle
open Ptx.ISA
noncomputable section

def intAssign (state : State) (dst : String) (value : Nat) : State :=
  {state with base := Scalar.intAssign state.base dst value}
def intPC (state : State) (pc : Nat) : State :=
  {state with base := Scalar.intPC state.base pc}

theorem scalar_step {ctx oracle code state instruction next events}
    (hr : state.base.core.thread.status = .running)
    (hi : code[state.base.core.thread.pc]? = some (.scalar instruction))
    (hs : Scalar.step ctx oracle.memory (scalarSkeleton code) state.base = .ok (next,events)) :
    step ctx oracle code state = .ok ({state with base := next},events.map Kind.ordinary) := by
  simp [step,hr,hi,Scalar.require,hs,bind,Except.bind,pure,Except.pure]

theorem integer_local_step {ctx oracle code state instruction next}
    (hr : state.base.core.thread.status = .running)
    (hi : code[state.base.core.thread.pc]? = some (.scalar (.integer instruction)))
    (hl : isLocal instruction = true) (hb : ∀ bid, instruction ≠ .barrier bid)
    (hs : localStep ctx.params ctx.id.tid.x state.base.core.thread instruction = .ok next) :
    step ctx oracle code state = .ok
      ({state with base := Scalar.finishInteger state.base {state.base.core with thread := next}},[]) := by
  exact scalar_step hr hi (Scalar.integer_local_step hr (scalarSkeleton_slot hi) hl hb hs)

theorem read_special_step {ctx oracle code state dst source}
    (hr : state.base.core.thread.status = .running)
    (hi : code[state.base.core.thread.pc]? = some (.scalar (.readSpecial dst source))) :
    step ctx oracle code state = .ok (intAssign state dst (wrap 32 (source.value ctx)),[]) :=
  scalar_step hr hi (Scalar.read_special_step hr (scalarSkeleton_slot hi))

theorem integer_store_step {ctx oracle code state space address operand addr value}
    (hr : state.base.core.thread.status = .running)
    (hi : code[state.base.core.thread.pc]? = some (.scalar (.integer (.store space address operand))))
    (ha : evalAddr ctx.id.tid.x state.base.core.thread address = .ok addr)
    (hv : Ptx.eval ctx.id.tid.x state.base.core.thread operand = .ok value) :
    step ctx oracle code state = .ok
      ({state with base := Scalar.finishInteger state.base {state.base.core with thread := advance state.base.core.thread}},
        [.ordinary (.write (Location.resolve space ctx.id addr) ((encodeU32 value).map Symbolic.Byte.bits))]) :=
  scalar_step hr hi (Scalar.integer_store_step hr (scalarSkeleton_slot hi) ha hv)

end
end Ptx.Shuffle
