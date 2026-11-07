import Ptx.Ordered.Loop
import Ptx.Ordered.Execution
import Ptx.Async.Invariant
import Ptx.Async.CompletionClock

/-! A joint source/protocol client, with one real Ordered.step or Async.step per
action. Device completion is gated on ALL recorded source threads being done;
PTX acquire alone never advances a stream or returns a loan. This is an exclusive
model-level baseline. Buffer/region reservations and physical runtime refinement
are separate obligations; protocol scalar values are not PTX byte storage. -/
namespace Ptx.Ordered.Client
open Ptx.ISA
noncomputable section

structure State where
  source : Candidate
  protocol : Async.State
inductive Action
  | source (index : Nat)
  | protocol (action : Async.Action)
inductive Error
  | invalidThread
  | sourceFault (fault : Scalar.Fault)
  | sourceIncomplete
  | protocolFailure (fault : Async.Error)

def finished (source : Candidate) : Bool :=
  source.traces.all (fun trace => trace.final.core.thread.status == .done)

theorem finished_iff {source : Candidate} : finished source = true ↔ Complete source := by
  simp only [finished,List.all_eq_true,beq_iff_eq,Complete]

def advanced (trace : ThreadTrace) (next : Ordered.State) (events : List Kind) : ThreadTrace :=
  {trace with count := trace.count+1,final := next,events := trace.events++events}

def sourceStep (code : List Instr) (launch : Scalar.Launch) (index : Nat) (state : State) : Except Error State :=
  match state.source.traces[index]? with
  | none => .error .invalidThread
  | some trace =>
    match Ordered.step {id := trace.id,params := launch.params,block := launch.geometry.block} trace.oracle code trace.final with
    | .error fault => .error (.sourceFault fault)
    | .ok (next,events) => .ok {state with source := ⟨state.source.traces.set index (advanced trace next events)⟩}

def deviceBlocked (action : Async.Action) (source : Candidate) : Bool :=
  match action with | .device _ => !finished source | _ => false

def step (code : List Instr) (launch : Scalar.Launch) (action : Action) (state : State) : Except Error State :=
  match action with
  | .source index => sourceStep code launch index state
  | .protocol action =>
    if deviceBlocked action state.source then .error .sourceIncomplete
    else match Async.step state.protocol action with
      | .error fault => .error (.protocolFailure fault)
      | .ok next => .ok {state with protocol := next}

def run (code : List Instr) (launch : Scalar.Launch) : List Action → State → Except Error State
  | [],state => .ok state
  | action::rest,state => (step code launch action state).bind (run code launch rest)

theorem advanced_produced {code} {launch : Scalar.Launch} {trace next events}
    (hp : Produced code launch.params launch.geometry.block trace)
    (hs : Ordered.step {id := trace.id,params := launch.params,block := launch.geometry.block} trace.oracle code trace.final = .ok (next,events)) :
    Produced code launch.params launch.geometry.block (advanced trace next events) := by
  unfold Produced advanced
  rw [Ordered.run_add, hp]
  simp only [Except.bind,Ordered.run,hs,List.append_nil]

theorem replaced_ids {traces : List ThreadTrace} {index trace next events}
    (ht : traces[index]? = some trace) :
    ((traces.set index (advanced trace next events)).map ThreadTrace.id) = traces.map ThreadTrace.id := by
  rw [List.map_set]
  obtain ⟨hb,he⟩ := List.getElem?_eq_some_iff.mp ht
  have hi : (traces.map ThreadTrace.id)[index]'(by simpa using hb) = trace.id := by
    simp only [List.getElem_map,he]
  rw [show (advanced trace next events).id = trace.id from rfl,← hi]
  exact List.set_getElem_self _

theorem replaced_well_formed {code launch source index trace next events}
    (hw : WellFormed code launch source) (ht : source.traces[index]? = some trace)
    (hs : Ordered.step {id := trace.id,params := launch.params,block := launch.geometry.block} trace.oracle code trace.final = .ok (next,events)) :
    WellFormed code launch ⟨source.traces.set index (advanced trace next events)⟩ := by
  have hm := List.mem_of_getElem? ht
  have hids := replaced_ids (next := next) (events := events) ht
  refine ⟨hw.1,by simpa only [hids] using hw.2.1,?_,?_⟩
  · intro actual ha
    rcases List.mem_or_eq_of_mem_set ha with hold | rfl
    · exact hw.2.2.1 actual hold
    · exact ⟨(hw.2.2.1 trace hm).1,advanced_produced (hw.2.2.1 trace hm).2 hs⟩
  · intro thread hi
    obtain ⟨old,ho,hid⟩ := hw.2.2.2 thread hi
    have hmem : thread ∈ (source.traces.set index (advanced trace next events)).map ThreadTrace.id := by
      rw [hids]
      exact List.mem_map.mpr ⟨old,ho,hid⟩
    exact List.mem_map.mp hmem

theorem source_step_spec {code launch index state next} (hs : sourceStep code launch index state = .ok next) :
    ∃ trace fresh events, state.source.traces[index]? = some trace ∧
      Ordered.step {id := trace.id,params := launch.params,block := launch.geometry.block} trace.oracle code trace.final = .ok (fresh,events) ∧
      next.source = ⟨state.source.traces.set index (advanced trace fresh events)⟩ ∧ next.protocol = state.protocol := by
  unfold sourceStep at hs
  cases ht : state.source.traces[index]? with
  | none => simp [ht] at hs
  | some trace =>
    cases hr : Ordered.step {id := trace.id,params := launch.params,block := launch.geometry.block} trace.oracle code trace.final with
    | error fault => simp [ht,hr] at hs
    | ok result =>
      obtain ⟨fresh,events⟩ := result
      have he : next = {state with source := ⟨state.source.traces.set index (advanced trace fresh events)⟩} := by
        simpa only [ht,hr,Except.ok.injEq] using hs.symm
      exact ⟨trace,fresh,events,rfl,hr,he ▸ rfl,he ▸ rfl⟩

theorem step_well_formed {code launch action state next}
    (hw : WellFormed code launch state.source) (hs : step code launch action state = .ok next) :
    WellFormed code launch next.source := by
  cases action with
  | source index =>
    obtain ⟨trace,fresh,events,ht,hr,he,_⟩ := source_step_spec hs
    rw [he]
    exact replaced_well_formed hw ht hr
  | protocol action =>
    simp only [step] at hs
    split at hs
    · cases hs
    · cases hr : Async.step state.protocol action with
      | error fault => simp [hr] at hs
      | ok fresh => have he := Except.ok.inj (by simpa only [hr] using hs); rw [← he]; exact hw

theorem source_step_preserves_protocol {code launch index state next}
    (hs : step code launch (.source index) state = .ok next) : next.protocol = state.protocol :=
  (source_step_spec hs).choose_spec.choose_spec.choose_spec.2.2.2

theorem device_requires_source_completion {code launch sid state next}
    (hs : step code launch (.protocol (.device sid)) state = .ok next) : Complete state.source := by
  simp only [step,deviceBlocked] at hs
  cases hf : finished state.source with
  | false => simp [hf] at hs
  | true => exact finished_iff.mp hf

theorem protocol_step_projects {code launch action state next}
    (hs : step code launch (.protocol action) state = .ok next) :
    Async.step state.protocol action = .ok next.protocol ∧ next.source = state.source := by
  simp only [step] at hs
  split at hs
  · cases hs
  · cases hr : Async.step state.protocol action with
    | error fault => simp [hr] at hs
    | ok fresh =>
      have he := Except.ok.inj (by simpa only [hr] using hs)
      rw [← he]
      exact ⟨rfl,rfl⟩

theorem step_protocol_invariant {code launch action state next}
    (hi : Async.Invariant state.protocol) (hs : step code launch action state = .ok next) :
    Async.Invariant next.protocol := by
  cases action with
  | source index => rw [source_step_preserves_protocol hs]; exact hi
  | protocol action => exact Async.step_invariant hi (protocol_step_projects hs).1

theorem run_invariants {code launch actions state next}
    (hw : WellFormed code launch state.source) (hi : Async.Invariant state.protocol)
    (hr : run code launch actions state = .ok next) :
    WellFormed code launch next.source ∧ Async.Invariant next.protocol := by
  induction actions generalizing state with
  | nil => cases hr; exact ⟨hw,hi⟩
  | cons action rest ih =>
    cases hs : step code launch action state with
    | error fault => simp [run,hs,Except.bind] at hr
    | ok mid => exact ih (step_well_formed hw hs) (step_protocol_invariant hi hs) (by simpa [run,hs,Except.bind] using hr)

def resetTrace (trace : ThreadTrace) : ThreadTrace :=
  {trace with count := 0,final := {},events := []}
def reset (source : Candidate) : Candidate := ⟨source.traces.map resetTrace⟩

theorem reset_well_formed {code launch source} (hw : WellFormed code launch source) :
    WellFormed code launch (reset source) := by
  refine ⟨hw.1,?_,?_,?_⟩
  · simpa only [reset,List.map_map,Function.comp_def,resetTrace] using hw.2.1
  · intro trace ht
    obtain ⟨old,ho,rfl⟩ := List.mem_map.mp ht
    exact ⟨(hw.2.2.1 old ho).1,rfl⟩
  · intro thread hi
    obtain ⟨old,ho,hid⟩ := hw.2.2.2 thread hi
    exact ⟨resetTrace old,List.mem_map.mpr ⟨old,ho,rfl⟩,hid⟩

theorem completed_device_covers_launch {code launch sid state next}
    (hw : WellFormed code launch state.source)
    (hs : step code launch (.protocol (.device sid)) state = .ok next) :
    ∀ thread, thread.Valid launch.geometry → ∃ trace ∈ state.source.traces,
      trace.id = thread ∧ trace.final.core.thread.status = .done := by
  intro thread hi
  obtain ⟨trace,ht,hid⟩ := hw.2.2.2 thread hi
  exact ⟨trace,ht,hid,device_requires_source_completion hs trace ht⟩

theorem device_rejects_incomplete {code launch sid state} (hc : ¬Complete state.source) :
    step code launch (.protocol (.device sid)) state = .error .sourceIncomplete := by
  have hf : finished state.source = false := by
    cases hf : finished state.source with
    | false => rfl
    | true => exact False.elim (hc (finished_iff.mp hf))
  simp [step,deviceBlocked,hf]

theorem nondevice_protocol_step {code launch state action} (hn : deviceBlocked action state.source = false) :
    step code launch (.protocol action) state =
      match Async.step state.protocol action with
      | .error fault => .error (.protocolFailure fault)
      | .ok next => .ok {state with protocol := next} := by
  simp only [step,hn,Bool.false_eq_true,ite_false]

theorem reclaim_loan_rejected {code launch state bid buffer}
    (hb : Async.getBuffer state.protocol bid = .ok buffer) (hl : buffer.loans.isEmpty = false) :
    step code launch (.protocol (.reclaim bid)) state = .error (.protocolFailure .outstandingLoan) := by
  rw [nondevice_protocol_step rfl]
  change (match Async.reclaim state.protocol bid with
    | .error fault => (Except.error (.protocolFailure fault) : Except Error State)
    | .ok next => .ok {state with protocol := next}) = _
  rw [Async.reclaim_rejects_loan hb hl]

theorem source_step_keeps_buffer {code launch index state next} {bid : Nat}
    (hs : step code launch (.source index) state = .ok next) :
    next.protocol.buffers[bid]? = state.protocol.buffers[bid]? := by
  rw [source_step_preserves_protocol hs]

theorem source_step_cannot_discharge_loan {code launch index state next bid buffer}
    (hs : step code launch (.source index) state = .ok next)
    (hb : Async.getBuffer state.protocol bid = .ok buffer) (hl : buffer.loans.isEmpty = false) :
    step code launch (.protocol (.reclaim bid)) next = .error (.protocolFailure .outstandingLoan) := by
  apply reclaim_loan_rejected (buffer := buffer) _ hl
  rw [source_step_preserves_protocol hs]
  exact hb

theorem host_acquire_removed_loan_requires_completion {code launch state next event bid before after loan}
    (hs : step code launch (.protocol (.acquire event)) state = .ok next)
    (hb : Async.getBuffer state.protocol bid = .ok before) (ha : Async.getBuffer next.protocol bid = .ok after)
    (hl : loan ∈ before.loans) (hg : loan ∉ after.loans) : Async.complete state.protocol loan.ticket = true :=
  Async.await_removed_loan_complete (protocol_step_projects hs).1 hb ha hl hg

def advancedMany (trace : ThreadTrace) (count : Nat) (next : Ordered.State) (events : List Kind) : ThreadTrace :=
  {trace with count := trace.count+count,final := next,events := trace.events++events}

theorem source_actions_run {code launch index state trace count next events}
    (ht : state.source.traces[index]? = some trace)
    (hr : Ordered.run {id := trace.id,params := launch.params,block := launch.geometry.block} trace.oracle code count trace.final = .ok (next,events)) :
    run code launch (List.replicate count (.source index)) state =
      .ok {state with source := ⟨state.source.traces.set index (advancedMany trace count next events)⟩} := by
  induction count generalizing state trace next events with
  | zero =>
    simp only [Ordered.run,Except.ok.injEq,Prod.mk.injEq] at hr
    obtain ⟨rfl,rfl⟩ := hr
    have hset : state.source.traces.set index trace = state.source.traces := by
      obtain ⟨hb,he⟩ := List.getElem?_eq_some_iff.mp ht
      rw [← he]
      exact List.set_getElem_self hb
    simp only [List.replicate_zero,run,advancedMany,Nat.add_zero,List.append_nil,hset]
  | succ count ih =>
    cases hs : Ordered.step {id := trace.id,params := launch.params,block := launch.geometry.block} trace.oracle code trace.final with
    | error fault => simp [Ordered.run,hs,Except.bind] at hr
    | ok pair =>
      obtain ⟨mid,first⟩ := pair
      cases hrest : Ordered.run {id := trace.id,params := launch.params,block := launch.geometry.block} trace.oracle code count mid with
      | error fault => simp [Ordered.run,hs,hrest,Except.bind] at hr
      | ok pair =>
        obtain ⟨last,rest⟩ := pair
        simp only [Ordered.run,hs,hrest,Except.bind,Except.ok.injEq,Prod.mk.injEq] at hr
        obtain ⟨rfl,rfl⟩ := hr
        let current : State := {state with source := ⟨state.source.traces.set index (advanced trace mid first)⟩}
        have hstep : step code launch (.source index) state = .ok current := by
          simp only [step,sourceStep,ht,hs,current]
        have hlookup : current.source.traces[index]? = some (advanced trace mid first) :=
          List.getElem?_set_self (List.getElem?_eq_some_iff.mp ht).1
        rw [List.replicate_succ,run,hstep]
        simp only [Except.bind]
        rw [ih hlookup (by exact hrest)]
        simp only [current,advancedMany,advanced,List.set_set,List.append_assoc,Nat.add_assoc,Nat.add_comm 1 count]

theorem run_append (code : List Instr) (launch : Scalar.Launch) (first rest : List Action) (state : State) :
    run code launch (first++rest) state = (run code launch first state).bind (run code launch rest) := by
  induction first generalizing state with
  | nil => rfl
  | cons action actions ih =>
    cases hs : step code launch action state <;> simp only [List.cons_append,run,hs,Except.bind,ih]

theorem step_launch_eq {code left right action state}
    (hg : left.geometry = right.geometry) (hp : left.params = right.params) :
    step code left action state = step code right action state := by
  cases action <;> simp only [step,sourceStep,hg,hp]

theorem run_launch_eq {code left right actions state}
    (hg : left.geometry = right.geometry) (hp : left.params = right.params) :
    run code left actions state = run code right actions state := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
    simp only [run,step_launch_eq hg hp]
    cases step code right action state <;> simp only [Except.bind,ih]

end
end Ptx.Ordered.Client
