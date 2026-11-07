import Ptx.Hopper.InFlightAccess
import Ptx.Async.CompletionClock

/-! A coupled access-prefix/loan-protocol transition relation. A prepared plan
assigns protocol tickets to actual TMA or native work. Its device counter may
pass a mapped ticket only after that work's source-matched completion is in
the prefix. Host operations cannot manufacture completion. This is a checked
model adapter, not a proof of CUDA runtime, allocation or byte-value refinement.
Dynamic plan construction and physical buffer/location binding remain separate.
-/
namespace Ptx.Hopper.Progress.Bridge
open Ptx.ISA
noncomputable section

structure State where
  protocol : Ptx.Async.State
  done : Cut

abbrev Plan := Ptx.Async.Ticket → Option Work

def Faithful (resolve : Tma.SharedResolver) (candidate : Unified.Candidate)
    (histories : Location → List Tma.Entry) (cluster : Access.ClusterScope) (plan : Plan) (s : State) : Prop :=
  ∀ ticket work, plan ticket = some work → Ptx.Async.complete s.protocol ticket = true →
    Completed resolve candidate histories cluster s.done work

inductive HostAction
  | record (stream event : Nat)
  | acquire (event : Nat)
  | reclaim (buffer : Nat)
  | write (buffer value : Nat)

def HostAction.action : HostAction → Ptx.Async.Action
  | .record sid event => .record sid event
  | .acquire event => .acquire event
  | .reclaim bid => .reclaim bid
  | .write bid value => .write bid value

theorem host_preserves_streams {s s' : Ptx.Async.State} {action : HostAction}
    (hs : Ptx.Async.step s (HostAction.action action) = .ok s') : s'.streams = s.streams := by
  cases action with
  | record sid event => exact Ptx.Async.record_preserves_completion hs
  | acquire event =>
    change Ptx.Async.await s event = .ok s' at hs
    unfold Ptx.Async.await at hs
    simp only [bind,Except.bind,Pure.pure,Except.pure] at hs
    repeat first | (solve | simp_all) | split at hs
    all_goals cases Except.ok.inj hs; rfl
  | reclaim bid =>
    change Ptx.Async.reclaim s bid = .ok s' at hs
    unfold Ptx.Async.reclaim at hs
    simp only [bind,Except.bind,Pure.pure,Except.pure] at hs
    repeat first | (solve | simp_all) | split at hs
    all_goals cases Except.ok.inj hs; rfl
  | write bid value =>
    change Ptx.Async.hostWrite s bid value = .ok s' at hs
    unfold Ptx.Async.hostWrite at hs
    simp only [bind,Except.bind,Pure.pure,Except.pure] at hs
    repeat first | (solve | simp_all) | split at hs
    all_goals cases Except.ok.inj hs; rfl

inductive Step (block : Dim3) (resolve : Tma.SharedResolver) (candidate : Unified.Candidate)
    (histories : Location → List Tma.Entry) (cluster : Access.ClusterScope) (plan : Plan) : State → State → Prop
  | access {s after} (advance : Advance block candidate histories s.done after) :
      Step block resolve candidate histories cluster plan s {s with done := after}
  | host {s next} (action : HostAction) (run : Ptx.Async.step s.protocol action.action = .ok next) :
      Step block resolve candidate histories cluster plan s {s with protocol := next}
  | device {s next sid st} (stream : Ptx.Async.getStream s.protocol sid = .ok st)
      (run : Ptx.Async.deviceStep s.protocol sid = .ok next)
      (completion : ∀ work, plan ⟨sid,st.completed+1⟩ = some work →
        Completed resolve candidate histories cluster s.done work) :
      Step block resolve candidate histories cluster plan s {s with protocol := next}

theorem step_faithful {block resolve candidate histories cluster plan s s'}
    (hf : Faithful resolve candidate histories cluster plan s)
    (hs : Step block resolve candidate histories cluster plan s s') :
    Faithful resolve candidate histories cluster plan s' := by
  cases hs with
  | access advance =>
    intro ticket work hm hc
    exact completed_monotone (advance_monotone advance) (hf ticket work hm hc)
  | host action run =>
    intro ticket work hm hc
    have hstreams := host_preserves_streams run
    exact hf ticket work hm (by simpa only [Ptx.Async.complete,hstreams] using hc)
  | device stream run completion =>
    intro ticket work hm hc
    rcases Ptx.Async.deviceStep_new_completion run hc with old | ⟨actual,ha,ht⟩
    · exact hf ticket work hm old
    · have heq : actual = _ := Except.ok.inj (ha.symm.trans stream)
      subst actual
      subst ticket
      exact completion work hm

theorem step_reached {block resolve candidate histories cluster plan s s'}
    (hr : Reached block candidate histories s.done)
    (hs : Step block resolve candidate histories cluster plan s s') : Reached block candidate histories s'.done := by
  cases hs with
  | access advance => exact .next hr advance
  | host => exact hr
  | device => exact hr

theorem step_protocol_invariant {block resolve candidate histories cluster plan s s'}
    (hi : Ptx.Async.Invariant s.protocol) (hs : Step block resolve candidate histories cluster plan s s') : Ptx.Async.Invariant s'.protocol := by
  cases hs with
  | access => exact hi
  | host action run => exact Ptx.Async.step_invariant hi run
  | device stream run completion => exact Ptx.Async.deviceStep_invariant hi run

inductive Steps (block : Dim3) (resolve : Tma.SharedResolver) (candidate : Unified.Candidate)
    (histories : Location → List Tma.Entry) (cluster : Access.ClusterScope) (plan : Plan) : State → State → Prop
  | refl (s) : Steps block resolve candidate histories cluster plan s s
  | next {s mid last} : Step block resolve candidate histories cluster plan s mid →
      Steps block resolve candidate histories cluster plan mid last → Steps block resolve candidate histories cluster plan s last

theorem steps_faithful {block resolve candidate histories cluster plan s s'}
    (hf : Faithful resolve candidate histories cluster plan s)
    (hs : Steps block resolve candidate histories cluster plan s s') : Faithful resolve candidate histories cluster plan s' := by
  induction hs with
  | refl => exact hf
  | next first rest ih => exact ih (step_faithful hf first)

theorem steps_reached {block resolve candidate histories cluster plan s s'}
    (hr : Reached block candidate histories s.done)
    (hs : Steps block resolve candidate histories cluster plan s s') : Reached block candidate histories s'.done := by
  induction hs with
  | refl => exact hr
  | next first rest ih => exact ih (step_reached hr first)

theorem steps_protocol_invariant {block resolve candidate histories cluster plan s s'}
    (hi : Ptx.Async.Invariant s.protocol) (hs : Steps block resolve candidate histories cluster plan s s') : Ptx.Async.Invariant s'.protocol := by
  induction hs with
  | refl => exact hi
  | next first rest ih => exact ih (step_protocol_invariant hi first)

theorem prepared_faithful {resolve candidate histories cluster plan} {protocol : Ptx.Async.State}
    (hzero : ∀ (sid : Nat) (st : Ptx.Async.Stream), protocol.streams[sid]? = some st → st.completed = 0)
    (hpositive : ∀ ticket work, plan ticket = some work → 0 < ticket.seq) :
    Faithful resolve candidate histories cluster plan ⟨protocol,fun _ => False⟩ := by
  intro ticket work hm hc
  cases hget : protocol.streams[ticket.stream]? with
  | none => simp [Ptx.Async.complete,hget] at hc
  | some st =>
    have hb : ticket.seq ≤ st.completed := by simpa [Ptx.Async.complete,hget] using hc
    have hz := hzero _ _ hget
    have hp := hpositive ticket work hm
    omega

theorem acquired_use_done {block resolve descriptor candidate histories cluster plan s event next frontier ticket work control node loc mode}
    (hf : Faithful resolve candidate histories cluster plan s)
    (hr : Reached block candidate histories s.done)
    (ha : Ptx.Async.await s.protocol event = .ok next) (he : Ptx.Async.getEvent s.protocol event = .ok frontier)
    (hcover : Ptx.Async.covers frontier ticket = true) (hm : plan ticket = some work)
    (hu : Use resolve descriptor candidate work control node loc mode) : s.done control :=
  reached_completed_use_done hr (hf ticket work hm (Ptx.Async.acquired_covered_complete ha he hcover)) hu

theorem pending_use_blocks_acquire {block resolve descriptor candidate histories cluster plan s event frontier ticket work control node loc mode}
    (hf : Faithful resolve candidate histories cluster plan s)
    (hr : Reached block candidate histories s.done)
    (he : Ptx.Async.getEvent s.protocol event = .ok frontier)
    (hcover : Ptx.Async.covers frontier ticket = true) (hm : plan ticket = some work)
    (hu : Use resolve descriptor candidate work control node loc mode) (hp : ¬s.done control) :
    ∀ next, Ptx.Async.await s.protocol event ≠ .ok next := by
  intro next ha
  exact hp (acquired_use_done hf hr ha he hcover hm hu)

theorem returned_loan_use_done {block resolve descriptor candidate histories cluster plan s event next bid before after loan work control node loc mode}
    (hf : Faithful resolve candidate histories cluster plan s)
    (hr : Reached block candidate histories s.done)
    (ha : Ptx.Async.await s.protocol event = .ok next)
    (hb : Ptx.Async.getBuffer s.protocol bid = .ok before) (hb' : Ptx.Async.getBuffer next bid = .ok after)
    (hl : loan ∈ before.loans) (hgone : loan ∉ after.loans)
    (hm : plan loan.ticket = some work) (hu : Use resolve descriptor candidate work control node loc mode) : s.done control :=
  reached_completed_use_done hr (hf loan.ticket work hm (Ptx.Async.await_removed_loan_complete ha hb hb' hl hgone)) hu

theorem pending_use_keeps_loan {block resolve descriptor candidate histories cluster plan s event next bid before after loan work control node loc mode}
    (hf : Faithful resolve candidate histories cluster plan s)
    (hr : Reached block candidate histories s.done)
    (ha : Ptx.Async.await s.protocol event = .ok next)
    (hb : Ptx.Async.getBuffer s.protocol bid = .ok before) (hb' : Ptx.Async.getBuffer next bid = .ok after)
    (hl : loan ∈ before.loans) (hm : plan loan.ticket = some work)
    (hu : Use resolve descriptor candidate work control node loc mode) (hp : ¬s.done control) : loan ∈ after.loans := by
  by_contra hgone
  exact hp (returned_loan_use_done hf hr ha hb hb' hl hgone hm hu)

end
end Ptx.Hopper.Progress.Bridge
