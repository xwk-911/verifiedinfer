import Ptx.Ampere.Updates

/-! Scalar control operations inside the extended source interpreter. These
rules retain integer/float bank filtering and dynamic barrier generations. -/
namespace Ptx.Ampere
open Ptx.ISA
noncomputable section

theorem integer_local_step {ctx oracle code s instruction next}
    (hr : s.scalar.core.thread.status = .running)
    (hi : code[s.scalar.core.thread.pc]? = some (.scalar (.integer instruction)))
    (hl : isLocal instruction = true) (hb : ∀ bid, instruction ≠ .barrier bid)
    (hs : localStep ctx.params ctx.id.tid.x s.scalar.core.thread instruction = .ok next) :
    step ctx oracle code s = .ok
      (finishScalar s (.integer instruction) (Scalar.finishInteger s.scalar {s.scalar.core with thread := next}),[]) := by
  simpa only [List.map_nil] using scalar_step hr hi
    (Scalar.integer_local_step hr (scalarSkeleton_slot hi) hl hb hs)

def barrierState (s : State) (bid : Nat) : State := {
  s with scalar := Scalar.finishInteger s.scalar {
    s.scalar.core with
    thread := Ptx.advance s.scalar.core.thread
    generations := (bid,Ptx.Event.generation s.scalar.core bid+1)::s.scalar.core.generations.filter (fun kv => kv.1 != bid)
  }
}

theorem barrier_step {ctx oracle code s bid}
    (hr : s.scalar.core.thread.status = .running)
    (hi : code[s.scalar.core.thread.pc]? = some (.scalar (.integer (.barrier bid)))) :
    step ctx oracle code s = .ok (barrierState s bid,
      [.ordinary (.barrierArrival bid (Ptx.Event.generation s.scalar.core bid)),
       .ordinary (.barrierReturn bid (Ptx.Event.generation s.scalar.core bid))]) := by
  have hs : Scalar.step ctx oracle.scalar (scalarSkeleton code) s.scalar =
      .ok ((barrierState s bid).scalar,
        [.barrierArrival bid (Ptx.Event.generation s.scalar.core bid),
         .barrierReturn bid (Ptx.Event.generation s.scalar.core bid)]) := by
    simp [Scalar.step,hr,Scalar.require,Scalar.integer_delegate_fetch,scalarSkeleton_slot hi,
      Scalar.liftInteger,Scalar.liftKind,Ptx.Event.step,barrierState,
      bind,Except.bind,pure,Except.pure]
  simpa [barrierState,finishScalar,scalarWritten] using scalar_step hr hi hs

@[simp] theorem barrier_pc (s : State) (bid : Nat) :
    (barrierState s bid).scalar.core.thread.pc = s.scalar.core.thread.pc+1 := rfl
@[simp] theorem barrier_queries (s : State) (bid : Nat) :
    (barrierState s bid).scalar.core.queries = s.scalar.core.queries := rfl
@[simp] theorem barrier_status (s : State) (bid : Nat) :
    (barrierState s bid).scalar.core.thread.status = s.scalar.core.thread.status := rfl
@[simp] theorem barrier_nat (s : State) (bid : Nat) (name : String) :
    lookup name (barrierState s bid).scalar.core.thread.regs = lookup name s.scalar.core.thread.regs := rfl

theorem barrier_float (s : State) (bid : Nat) (name : String)
    (hn : lookup name s.scalar.core.thread.regs = none) :
    declarationLookup name (barrierState s bid).scalar.floats = declarationLookup name s.scalar.floats := by
  unfold barrierState
  rw [Scalar.finish_integer_lookup]
  simpa only [Ptx.advance,hn,ite_true]

@[simp] theorem barrier_generation (s : State) (bid : Nat) :
    Ptx.Event.generation (barrierState s bid).scalar.core bid = Ptx.Event.generation s.scalar.core bid+1 := by
  simp [barrierState,Scalar.finishInteger,Ptx.Event.generation]

end
end Ptx.Ampere
