import Ptx.Async.Invariant

/-! Two distinct optimization patterns reuse the same reachable-state lifetime
protocol. Data is arbitrary, not a single concrete sample. These contracts are
for abstract copy/use commands; the PTX/Iris joint interpretation remains separate.
-/
namespace Ptx.Async.Contracts

def prefetchPrefix : List Action := [.copy 0 0 1,.record 0 7,.wait 1 7,.use 1 1,.record 1 8]
def prefetchActions : List Action := prefetchPrefix ++ [.device 0,.device 1,.device 1,.acquire 7,.acquire 8]
def prefetchFinal (value : Nat) : State := {
  streams := [⟨1,1,[],[]⟩,⟨2,2,[],[⟨0,1⟩]⟩]
  buffers := [{value := value},{value := value}]
  events := [⟨8,⟨1,2⟩⟩,⟨7,⟨0,1⟩⟩]
}
theorem prefetch_exact (value : Nat) :
    run (initial 2 [value,0]) prefetchActions = .ok (prefetchFinal value) := by rfl
theorem prefetch_invariant (value : Nat) : Invariant (prefetchFinal value) :=
  steps_invariant (initial_invariant _ _) (run_sound (prefetch_exact value))

def prefetchIssued (value : Nat) : State :=
  (run (initial 2 [value,0]) prefetchPrefix).toOption.getD (initial 2 [value,0])
theorem prefetch_issued (value : Nat) :
    run (initial 2 [value,0]) prefetchPrefix = .ok (prefetchIssued value) := by rfl
theorem prefetch_reclaim_rejected (value : Nat) :
    reclaim (prefetchIssued value) 1 = .error .outstandingLoan := by
  apply reachable_pending_reclaim_rejected (run_sound (prefetch_issued value))
    (sid := 1) (st := ⟨2,0,[.wait ⟨0,1⟩,.use 1],[⟨0,1⟩]⟩) (i := 1) (cmd := .use 1) (mode := .read)
  · rfl
  · rfl
  · exact .useRead _

def deferredPrefix : List Action := [.use 0 0,.record 0 9]
def deferredActions : List Action := deferredPrefix ++ [.device 0,.acquire 9,.reclaim 0]
def deferredFinal (value : Nat) : State := {
  streams := [⟨1,1,[],[]⟩]
  buffers := [{value := value,alive := false}]
  events := [⟨9,⟨0,1⟩⟩]
}
theorem deferred_exact (value : Nat) :
    run (initial 1 [value]) deferredActions = .ok (deferredFinal value) := by rfl
theorem deferred_invariant (value : Nat) : Invariant (deferredFinal value) :=
  steps_invariant (initial_invariant _ _) (run_sound (deferred_exact value))

def deferredIssued (value : Nat) : State :=
  (run (initial 1 [value]) deferredPrefix).toOption.getD (initial 1 [value])
theorem deferred_issued (value : Nat) :
    run (initial 1 [value]) deferredPrefix = .ok (deferredIssued value) := by rfl
theorem deferred_reclaim_rejected (value : Nat) :
    reclaim (deferredIssued value) 0 = .error .outstandingLoan := by
  apply reachable_pending_reclaim_rejected (run_sound (deferred_issued value))
    (sid := 0) (st := ⟨1,0,[.use 0],[]⟩) (i := 0) (cmd := .use 0) (mode := .read)
  · rfl
  · rfl
  · exact .useRead _

/-! Regression families for a stale event and concurrent read borrowers. Both
must retain the still-pending loan; old completion evidence cannot free it. -/
theorem stale_event_rejected (value : Nat) :
    run (initial 1 [value]) [.use 0 0,.record 0 9,.device 0,.acquire 9,
      .use 0 0,.acquire 9,.reclaim 0] = .error .outstandingLoan := by rfl
theorem zero_frontier_rejected (value : Nat) :
    run (initial 1 [value]) [.record 0 9,.use 0 0,.acquire 9,.reclaim 0] = .error .outstandingLoan := by rfl
theorem second_reader_rejected (value : Nat) :
    run (initial 2 [value]) [.use 0 0,.use 1 0,.record 0 7,.device 0,.acquire 7,.reclaim 0] =
      .error .outstandingLoan := by rfl

end Ptx.Async.Contracts
