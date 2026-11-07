import Ptx.Kernels.ReleaseAcquireMessageSource
import Ptx.Ordered.Loop

/-! Arbitrary-state local semantics of the actual polling window. No canonical
oracle replies, memory consistency or bound on polling iterations is assumed. -/
namespace Ptx.Kernels.ReleaseAcquireMessage
open Ptx.ISA
noncomputable section

structure Pointers (state : Ordered.State) : Prop where
  data : lookup "%data" state.core.thread.regs = some 64
  flag : lookup "%flag" state.core.thread.regs = some 128
  out : lookup "%out" state.core.thread.regs = some 256

def AtPoll (state : Ordered.State) : Prop :=
  Pointers state ∧ state.core.thread.pc = 9 ∧ state.core.thread.status = .running
def AtTail (state : Ordered.State) : Prop :=
  Pointers state ∧ state.core.thread.pc = 12 ∧ state.core.thread.status = .running

def word (value : Nat) := wrap 32 value
def polled (state : Ordered.State) (value : Nat) : Ordered.State :=
  Scalar.finishInteger state {state.core with
    thread := assign state.core.thread "%seen" (word value)
    queries := state.core.queries+1}
def compared (state : Ordered.State) (value : Nat) : Ordered.State :=
  let loaded := polled state value
  Scalar.finishInteger loaded {loaded.core with thread := assign loaded.core.thread "%p" (if word value = 0 then 1 else 0)}
def branched (state : Ordered.State) (value : Nat) : Ordered.State :=
  let checked := compared state value
  Scalar.finishInteger checked {checked.core with thread := {checked.core.thread with pc := if word value = 0 then 9 else 12}}
def acquireEvent (value : Nat) : Ordered.Kind := ⟨.read flag (Scalar.u32Bytes (word value)),.acquire,some .gpu⟩

theorem poll_step {state : Ordered.State} {answers : Ordered.Oracle} {value : Nat}
    (hp : AtPoll state) (ha : answers state.core.queries = .integer value) :
    Ordered.step (context 1) answers code state = .ok (polled state value,[acquireEvent value]) := by
  simp [Ordered.step,Ordered.scalarSkeleton,Ordered.scalarSlot,Scalar.step,Scalar.integer_delegate_fetch,
    code,Generated.release_acquire_message.program,hp.2.1,hp.2.2,Scalar.require,Scalar.liftInteger,
    Ptx.Event.step,Scalar.integerOracle,Ptx.evalAddr,Ptx.eval,hp.1.flag,ha,polled,word,
    Scalar.finishInteger,Scalar.liftKind,Ordered.annotate,acquireEvent,flag,Location.resolve,
    bind,Except.bind,pure,Except.pure]
  simp [wrap,Scalar.u32Bytes]

theorem poll_step_real {state : Ordered.State} {answers : Ordered.Oracle} {format value}
    (hp : AtPoll state) (ha : answers state.core.queries = .real format value) :
    Ordered.step (context 1) answers code state = .error (.oracleType state.core.queries) := by
  simp [Ordered.step,Ordered.scalarSkeleton,Ordered.scalarSlot,Scalar.step,
    code,Generated.release_acquire_message.program,hp.2.1,hp.2.2,Scalar.require,ha,
    bind,Except.bind,pure,Except.pure,throw,throwThe,MonadExceptOf.throw]

theorem poll_reply {state : Ordered.State} {answers : Ordered.Oracle} {next events}
    (hp : AtPoll state) (hs : Ordered.step (context 1) answers code state = .ok (next,events)) :
    ∃ value, answers state.core.queries = .integer value := by
  cases ha : answers state.core.queries with
  | integer value => exact ⟨value,rfl⟩
  | real format value => rw [poll_step_real hp ha] at hs; cases hs

theorem compare_step {state : Ordered.State} {answers : Ordered.Oracle} (value : Nat) (hp : AtPoll state) :
    Ordered.step (context 1) answers code (polled state value) = .ok (compared state value,[]) := by
  simp [Ordered.step,Ordered.scalarSkeleton,Ordered.scalarSlot,Scalar.step,Scalar.integer_delegate_fetch,
    code,Generated.release_acquire_message.program,hp.2.1,hp.2.2,Scalar.require,Scalar.liftInteger,
    Ptx.Event.step,Ptx.localStep,Ptx.eval,polled,compared,Scalar.finishInteger,assign,advance,
    word,wrap,Nat.mod_mod,bind,Except.bind,pure,Except.pure]
  exact ⟨rfl,rfl⟩

theorem branch_step {state : Ordered.State} {answers : Ordered.Oracle} (value : Nat) (hp : AtPoll state) :
    Ordered.step (context 1) answers code (compared state value) = .ok (branched state value,[]) := by
  by_cases hv : word value = 0
  all_goals
    simp [Ordered.step,Ordered.scalarSkeleton,Ordered.scalarSlot,Scalar.step,Scalar.integer_delegate_fetch,
      code,Generated.release_acquire_message.program,hp.2.1,hp.2.2,Scalar.require,Scalar.liftInteger,
      Ptx.Event.step,Ptx.localStep,polled,compared,branched,Scalar.finishInteger,assign,advance,hv,
      bind,Except.bind,pure,Except.pure]

theorem polled_pointers {state : Ordered.State} (hp : Pointers state) (value : Nat) : Pointers (polled state value) := by
  constructor <;> simp [polled,Scalar.finishInteger,assign,advance,hp.data,hp.flag,hp.out]

theorem compared_pointers {state : Ordered.State} (hp : Pointers state) (value : Nat) : Pointers (compared state value) := by
  have hl := polled_pointers hp value
  constructor <;> simp [compared,Scalar.finishInteger,assign,advance,hl.data,hl.flag,hl.out]

theorem branched_pointers {state : Ordered.State} (hp : Pointers state) (value : Nat) : Pointers (branched state value) := by
  have hl := compared_pointers hp value
  exact ⟨hl.data,hl.flag,hl.out⟩

theorem poll_chunk {state : Ordered.State} {answers : Ordered.Oracle} {value : Nat}
    (hp : AtPoll state) (ha : answers state.core.queries = .integer value) :
    Ordered.run (context 1) answers code 3 state = .ok (branched state value,[acquireEvent value]) := by
  rw [Ordered.run,poll_step hp ha]
  simp only [Except.bind,Ordered.run,compare_step value hp,branch_step value hp,List.append_nil]

theorem poll_chunk_continues_or_leaves {state : Ordered.State} {value : Nat} (hp : AtPoll state) :
    AtPoll (branched state value) ∨ AtTail (branched state value) := by
  by_cases hv : word value = 0
  · exact Or.inl ⟨branched_pointers hp.1 value,by simp [branched,Scalar.finishInteger,hv],
      by simpa [branched,compared,polled,Scalar.finishInteger,assign,advance] using hp.2.2⟩
  · exact Or.inr ⟨branched_pointers hp.1 value,by simp [branched,Scalar.finishInteger,hv],
      by simpa [branched,compared,polled,Scalar.finishInteger,assign,advance] using hp.2.2⟩

theorem poll_chunk_shape {state : Ordered.State} {answers : Ordered.Oracle} {next events}
    (hp : AtPoll state) (hr : Ordered.run (context 1) answers code 3 state = .ok (next,events)) :
    ∃ value, answers state.core.queries = .integer value ∧ next = branched state value ∧ events = [acquireEvent value] := by
  obtain ⟨_,_,hs⟩ := Ordered.successful_first_step hr
  obtain ⟨value,ha⟩ := poll_reply hp hs
  have he := Prod.mk.inj (Except.ok.inj ((poll_chunk hp ha).symm.trans hr))
  exact ⟨value,ha,he.1.symm,he.2.symm⟩

theorem poll_chunk_closed {state : Ordered.State} {answers : Ordered.Oracle} {next events}
    (hp : AtPoll state) (hr : Ordered.run (context 1) answers code 3 state = .ok (next,events)) : AtPoll next ∨ AtTail next := by
  obtain ⟨value,_,rfl,_⟩ := poll_chunk_shape hp hr
  exact poll_chunk_continues_or_leaves hp

theorem poll_short_running {state : Ordered.State} {answers : Ordered.Oracle} {count last events}
    (hp : AtPoll state) (hc : count < 3) (hr : Ordered.run (context 1) answers code count state = .ok (last,events)) :
    last.core.thread.status = .running := by
  have hcounts : count = 0 ∨ count = 1 ∨ count = 2 := by omega
  rcases hcounts with rfl | rfl | rfl
  · simp only [Ordered.run,Except.ok.injEq,Prod.mk.injEq] at hr
    obtain ⟨rfl,_⟩ := hr
    exact hp.2.2
  · obtain ⟨_,_,hs⟩ := Ordered.successful_first_step hr
    obtain ⟨value,ha⟩ := poll_reply hp hs
    rw [Ordered.run,poll_step hp ha] at hr
    simp only [Except.bind,Ordered.run,List.append_nil,Except.ok.injEq,Prod.mk.injEq] at hr
    obtain ⟨rfl,_⟩ := hr
    simpa only [polled,Scalar.finishInteger,assign,advance] using hp.2.2
  · obtain ⟨_,_,hs⟩ := Ordered.successful_first_step hr
    obtain ⟨value,ha⟩ := poll_reply hp hs
    rw [Ordered.run,poll_step hp ha] at hr
    simp only [Except.bind,Ordered.run,compare_step value hp,List.append_nil,Except.ok.injEq,Prod.mk.injEq] at hr
    obtain ⟨rfl,_⟩ := hr
    simpa only [compared,polled,Scalar.finishInteger,assign,advance] using hp.2.2

def tailLoaded (state : Ordered.State) (value : Nat) : Ordered.State :=
  Scalar.finishInteger state {state.core with
    thread := assign state.core.thread "%value" (word value)
    queries := state.core.queries+1}
def tailStored (state : Ordered.State) (value : Nat) : Ordered.State :=
  let loaded := tailLoaded state value
  Scalar.finishInteger loaded {loaded.core with thread := advance loaded.core.thread}
def tailFinal (state : Ordered.State) (value : Nat) : Ordered.State :=
  let stored := tailStored state value
  Scalar.finishInteger stored {stored.core with thread := {stored.core.thread with status := .done}}
def tailEvents (value : Nat) : List Ordered.Kind := [
  ⟨.read payload (Scalar.u32Bytes (word value)),.weak,none⟩,
  ⟨.write ⟨.global,256⟩ (Scalar.u32Bytes (word value)),.weak,none⟩]

theorem tail_load_step {state : Ordered.State} {answers : Ordered.Oracle} {value : Nat}
    (hp : AtTail state) (ha : answers state.core.queries = .integer value) :
    Ordered.step (context 1) answers code state = .ok (tailLoaded state value,[(tailEvents value)[0]'(by simp [tailEvents])]) := by
  simp [Ordered.step,Ordered.scalarSkeleton,Ordered.scalarSlot,Scalar.step,Scalar.integer_delegate_fetch,
    code,Generated.release_acquire_message.program,hp.2.1,hp.2.2,Scalar.require,Scalar.liftInteger,
    Ptx.Event.step,Scalar.integerOracle,Ptx.evalAddr,Ptx.eval,hp.1.data,ha,tailLoaded,word,
    Scalar.finishInteger,Scalar.liftKind,Ordered.annotate,tailEvents,payload,Location.resolve,
    wrap,Scalar.u32Bytes,bind,Except.bind,pure,Except.pure]

theorem tail_load_real {state : Ordered.State} {answers : Ordered.Oracle} {format value}
    (hp : AtTail state) (ha : answers state.core.queries = .real format value) :
    Ordered.step (context 1) answers code state = .error (.oracleType state.core.queries) := by
  simp [Ordered.step,Ordered.scalarSkeleton,Ordered.scalarSlot,Scalar.step,
    code,Generated.release_acquire_message.program,hp.2.1,hp.2.2,Scalar.require,ha,
    bind,Except.bind,pure,Except.pure,throw,throwThe,MonadExceptOf.throw]

theorem tail_reply {state : Ordered.State} {answers : Ordered.Oracle} {next events}
    (hp : AtTail state) (hs : Ordered.step (context 1) answers code state = .ok (next,events)) :
    ∃ value, answers state.core.queries = .integer value := by
  cases ha : answers state.core.queries with
  | integer value => exact ⟨value,rfl⟩
  | real format value => rw [tail_load_real hp ha] at hs; cases hs

theorem tail_store_step {state : Ordered.State} {answers : Ordered.Oracle} (value : Nat) (hp : AtTail state) :
    Ordered.step (context 1) answers code (tailLoaded state value) = .ok (tailStored state value,[(tailEvents value)[1]'(by simp [tailEvents])]) := by
  simp [Ordered.step,Ordered.scalarSkeleton,Ordered.scalarSlot,Scalar.step,Scalar.integer_delegate_fetch,
    code,Generated.release_acquire_message.program,hp.2.1,hp.2.2,Scalar.require,Scalar.liftInteger,
    Ptx.Event.step,Ptx.evalAddr,Ptx.eval,tailLoaded,tailStored,Scalar.finishInteger,assign,advance,hp.1.out,
    Scalar.liftKind,Ordered.annotate,tailEvents,payload,Location.resolve,word,Scalar.u32Bytes,wrap,
    bind,Except.bind,pure,Except.pure]

theorem tail_return_step {state : Ordered.State} {answers : Ordered.Oracle} (value : Nat) (hp : AtTail state) :
    Ordered.step (context 1) answers code (tailStored state value) = .ok (tailFinal state value,[]) := by
  simp [Ordered.step,Ordered.scalarSkeleton,Ordered.scalarSlot,Scalar.step,Scalar.integer_delegate_fetch,
    code,Generated.release_acquire_message.program,hp.2.1,hp.2.2,Scalar.require,Scalar.liftInteger,
    Ptx.Event.step,Ptx.localStep,tailLoaded,tailStored,tailFinal,Scalar.finishInteger,assign,advance,
    bind,Except.bind,pure,Except.pure]

theorem tail_chunk {state : Ordered.State} {answers : Ordered.Oracle} {value : Nat}
    (hp : AtTail state) (ha : answers state.core.queries = .integer value) :
    Ordered.run (context 1) answers code 3 state = .ok (tailFinal state value,tailEvents value) := by
  rw [Ordered.run,tail_load_step hp ha]
  simp only [Except.bind,Ordered.run,tail_store_step value hp,tail_return_step value hp,List.append_nil]
  rfl

theorem tail_chunk_shape {state : Ordered.State} {answers : Ordered.Oracle} {next events}
    (hp : AtTail state) (hr : Ordered.run (context 1) answers code 3 state = .ok (next,events)) :
    ∃ value, answers state.core.queries = .integer value ∧ next = tailFinal state value ∧ events = tailEvents value := by
  obtain ⟨_,_,hs⟩ := Ordered.successful_first_step hr
  obtain ⟨value,ha⟩ := tail_reply hp hs
  have he := Prod.mk.inj (Except.ok.inj ((tail_chunk hp ha).symm.trans hr))
  exact ⟨value,ha,he.1.symm,he.2.symm⟩

theorem tail_short_running {state : Ordered.State} {answers : Ordered.Oracle} {count last events}
    (hp : AtTail state) (hc : count < 3) (hr : Ordered.run (context 1) answers code count state = .ok (last,events)) :
    last.core.thread.status = .running := by
  have hcounts : count = 0 ∨ count = 1 ∨ count = 2 := by omega
  rcases hcounts with rfl | rfl | rfl
  · simp only [Ordered.run,Except.ok.injEq,Prod.mk.injEq] at hr
    obtain ⟨rfl,_⟩ := hr
    exact hp.2.2
  · obtain ⟨_,_,hs⟩ := Ordered.successful_first_step hr
    obtain ⟨value,ha⟩ := tail_reply hp hs
    rw [Ordered.run,tail_load_step hp ha] at hr
    simp only [Except.bind,Ordered.run,List.append_nil,Except.ok.injEq,Prod.mk.injEq] at hr
    obtain ⟨rfl,_⟩ := hr
    simpa only [tailLoaded,Scalar.finishInteger,assign,advance] using hp.2.2
  · obtain ⟨_,_,hs⟩ := Ordered.successful_first_step hr
    obtain ⟨value,ha⟩ := tail_reply hp hs
    rw [Ordered.run,tail_load_step hp ha] at hr
    simp only [Except.bind,Ordered.run,tail_store_step value hp,List.append_nil,Except.ok.injEq,Prod.mk.injEq] at hr
    obtain ⟨rfl,_⟩ := hr
    simpa only [tailStored,tailLoaded,Scalar.finishInteger,assign,advance] using hp.2.2

theorem tail_chunk_finishes {state : Ordered.State} {answers : Ordered.Oracle} {last events}
    (hp : AtTail state) (hr : Ordered.run (context 1) answers code 3 state = .ok (last,events)) :
    last.core.thread.status = .done := by
  obtain ⟨value,_,rfl,_⟩ := tail_chunk_shape hp hr
  rfl

end
end Ptx.Kernels.ReleaseAcquireMessage
