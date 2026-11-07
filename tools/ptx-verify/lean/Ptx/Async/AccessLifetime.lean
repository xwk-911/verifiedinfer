import Ptx.Async.Drain

/-! Mode-tagged lifetime reservations and total finite clients. A reservation
protects allocation lifetime against host writes/reclamation. Ordered queued
reservations need not be disjoint active byte permissions. Opaque access tasks
leave scalar values unchanged; actual memory effects need a source-level bridge.
-/
namespace Ptx.Async.AccessLifetime

/-- Successful public submission derives the loan; no initial-loan premise. -/
theorem submitted_holds {s sid bid mode next} (hs : submitAccess s sid bid mode = .ok next) :
    ∃ st, getStream s sid = .ok st ∧ Holds next bid ⟨⟨sid,st.issued+1⟩,mode⟩ := by
  unfold submitAccess at hs
  cases hb : borrow s sid bid mode with
  | error e => simp [hb,bind,Except.bind] at hs
  | ok mid =>
    have hq : enqueue mid sid (.access bid mode) = .ok next := by simpa [hb,bind,Except.bind] using hs
    obtain ⟨hstreams,_,st,hst,hh⟩ := borrow_spec hb
    refine ⟨st,getStream_iff.mpr hst,?_⟩
    have hget : getStream mid sid = .ok st := getStream_iff.mpr (by simpa [hstreams] using hst)
    simp [enqueue,hget,bind,Except.bind,pure,Except.pure] at hq
    subst next
    exact hh

theorem submitted_blocks_reclaim {s sid bid mode next}
    (hs : submitAccess s sid bid mode = .ok next) : reclaim next bid = .error .outstandingLoan := by
  obtain ⟨_,_,hh⟩ := submitted_holds hs
  exact reclaim_of_holds hh

theorem submitted_blocks_host_write {s sid bid mode next} (value : Nat)
    (hs : submitAccess s sid bid mode = .ok next) : hostWrite next bid value = .error .outstandingLoan := by
  obtain ⟨_,_,hh⟩ := submitted_holds hs
  exact hostWrite_of_holds hh

/-- Actual public preparation, record, FIFO execution and acquisition succeed
for any finite valid mixture of use/copy/mode-tagged requests. No fairness or
source-kernel completion claim is inferred from this chosen protocol schedule. -/
theorem client_returns (values : List Nat) (requests : List Preparation.Request)
    (hv : ∀ request ∈ requests, request.Valid values.length) :
    ∃ final,
      run (initial 1 values)
        ((requests.map Preparation.Request.action ++ [.record 0 0]) ++
          (List.replicate requests.length (.device 0) ++ [.acquire 0])) = .ok final ∧
      Drain.Returned final ∧ Preparation.Live final ∧ final.buffers.length = values.length ∧
      final.streams = [⟨requests.length,requests.length,[],[]⟩] ∧ Invariant final := by
  obtain ⟨prepared,hp,hr,hl,he⟩ := Preparation.ready_requests (Preparation.ready_initial values) requests
    (by simpa [initial] using hv)
  simp only [List.nil_append] at hr
  let recorded : State := {prepared with events := ⟨0,⟨0,(requests.map Preparation.Request.command).length⟩⟩::prepared.events}
  have hrstep : step prepared (.record 0 0) = .ok recorded :=
    Preparation.ready_record hr (by simp [he,initial])
  have hprefix : run (initial 1 values) (requests.map Preparation.Request.action ++ [.record 0 0]) = .ok recorded := by
    simp only [Client.run_append,hp,Except.bind,run,hrstep]
  have hir : Invariant recorded := steps_invariant (initial_invariant 1 values) (run_sound hprefix)
  have hready : Preparation.Ready recorded (requests.map Preparation.Request.command) := hr
  have hevent : getEvent recorded 0 = .ok ⟨0,(requests.map Preparation.Request.command).length⟩ := by
    simp [getEvent,recorded,bind,Except.bind,pure,Except.pure]
  obtain ⟨final,hf,hreturned,hlive,hlen,hshape⟩ :=
    Drain.drain_and_acquire hready hir (Drain.requests_plain requests) hevent
  have hfinal : run (initial 1 values)
      ((requests.map Preparation.Request.action ++ [.record 0 0]) ++
        (List.replicate requests.length (.device 0) ++ [.acquire 0])) = .ok final := by
    simpa only [Client.run_append,hprefix,Except.bind,List.length_map] using hf
  refine ⟨final,hfinal,hreturned,hlive,?_,by simpa only [List.length_map] using hshape,
    steps_invariant (initial_invariant 1 values) (run_sound hfinal)⟩
  simpa only [recorded,hl,initial,List.length_map] using hlen

end Ptx.Async.AccessLifetime
