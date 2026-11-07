import Ptx.Async.Preparation
import Ptx.Async.Clients
import Ptx.Kernels.HopperDoubleBufferAsyncBindings

/-! Public aggregate preparation for arbitrary finite tile count and any eight
initial scalar values. Event IDs are indexed, including a distinct final event.
This prepares the logical lifetime client, not actual CUDA launches/allocations.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

def tileRequests (tile : Nat) : List Ptx.Async.Preparation.Request :=
  [.use 0,.copy 2 (aBuffer tile),.use 1,.copy 3 (bBuffer tile),.use (aBuffer tile),.use (bBuffer tile)]
def tileCommands (tile : Nat) : List Ptx.Async.Command := (tileRequests tile).map Ptx.Async.Preparation.Request.command
def asyncCommands (tiles : Nat) : List Ptx.Async.Command := (List.range tiles).flatMap tileCommands
def prefixActions : Nat → List Ptx.Async.Action
  | 0 => [.record 0 0]
  | tiles+1 => prefixActions tiles ++ ((tileRequests tiles).map Ptx.Async.Preparation.Request.action ++ [.record 0 (tiles+1)])
def preparationActions (tiles : Nat) : List Ptx.Async.Action := prefixActions tiles ++ [.record 0 (tiles+1)]
def publicPrepared (values : List Nat) (tiles : Nat) : Ptx.Async.State :=
  (Ptx.Async.run (Ptx.Async.initial 1 values) (preparationActions tiles)).toOption.getD (Ptx.Async.initial 1 values)

theorem tile_requests_valid (tile : Nat) : ∀ request ∈ tileRequests tile, request.Valid 8 := by
  have hs := (stage tile).isLt
  simp [tileRequests,Ptx.Async.Preparation.Request.Valid,aBuffer,bBuffer]
  omega

theorem async_commands_succ (tiles : Nat) : asyncCommands (tiles+1) = asyncCommands tiles ++ tileCommands tiles := by
  simp [asyncCommands,List.range_succ,List.flatMap_append]

theorem async_commands_length (tiles : Nat) : (asyncCommands tiles).length = 6*tiles := by
  induction tiles with
  | zero => rfl
  | succ tiles ih => simp [async_commands_succ,ih,tileCommands,tileRequests]; omega

private theorem indexed_event_fresh {s : Ptx.Async.State} {count : Nat}
    (hi : s.events.map Ptx.Async.Event.id = (List.range count).reverse) :
    s.events.any (fun entry => entry.id == count) = false := by
  apply List.any_eq_false.mpr
  intro entry hm
  have hmem : entry.id ∈ s.events.map Ptx.Async.Event.id := List.mem_map.mpr ⟨entry,hm,rfl⟩
  rw [hi] at hmem
  have hb : entry.id < count := by simpa using hmem
  have hn : entry.id ≠ count := by omega
  simp [hn]

theorem prefix_preparation_exists (values : List Nat) (hv : values.length = 8) (tiles : Nat) :
    ∃ state, Ptx.Async.run (Ptx.Async.initial 1 values) (prefixActions tiles) = .ok state ∧
      Ptx.Async.Preparation.Ready state (asyncCommands tiles) ∧ state.buffers.length = 8 ∧
      state.events.map Ptx.Async.Event.id = (List.range (tiles+1)).reverse := by
  induction tiles with
  | zero =>
    let next := {Ptx.Async.initial 1 values with events := [⟨0,⟨0,0⟩⟩]}
    have hr := Ptx.Async.Preparation.ready_initial values
    have hs := Ptx.Async.Preparation.ready_record (event := 0) hr (by rfl)
    refine ⟨next,by simp only [prefixActions,Ptx.Async.run,hs,Except.bind]; rfl,hr,?_,rfl⟩
    simpa [next,Ptx.Async.initial] using hv
  | succ tiles ih =>
    obtain ⟨state,hs,hr,hlen,hids⟩ := ih
    obtain ⟨mid,hm,hrmid,hmidlen,hmidevents⟩ := Ptx.Async.Preparation.ready_requests hr (tileRequests tiles)
      (by intro request hmem; simpa only [hlen] using tile_requests_valid tiles request hmem)
    have hready : Ptx.Async.Preparation.Ready mid (asyncCommands (tiles+1)) := by
      simpa only [async_commands_succ,tileCommands] using hrmid
    have hmids : mid.events.map Ptx.Async.Event.id = (List.range (tiles+1)).reverse := by rw [hmidevents,hids]
    let next := {mid with events := ⟨tiles+1,⟨0,(asyncCommands (tiles+1)).length⟩⟩::mid.events}
    have hrecord := Ptx.Async.Preparation.ready_record hready (indexed_event_fresh hmids)
    refine ⟨next,?_,hready,hmidlen.trans hlen,?_⟩
    · simp only [prefixActions,Ptx.Async.Client.run_append,hs,Except.bind,hm,Ptx.Async.run,hrecord]
      rfl
    · simp [next,hmids,List.range_succ,List.reverse_append]

theorem preparation_exists (values : List Nat) (hv : values.length = 8) (tiles : Nat) :
    ∃ state, Ptx.Async.run (Ptx.Async.initial 1 values) (preparationActions tiles) = .ok state ∧
      Ptx.Async.Preparation.Ready state (asyncCommands tiles) ∧ state.buffers.length = 8 ∧
      state.events.map Ptx.Async.Event.id = (List.range (tiles+2)).reverse := by
  obtain ⟨state,hs,hr,hlen,hids⟩ := prefix_preparation_exists values hv tiles
  let next := {state with events := ⟨tiles+1,⟨0,(asyncCommands tiles).length⟩⟩::state.events}
  have hrecord := Ptx.Async.Preparation.ready_record hr (indexed_event_fresh hids)
  refine ⟨next,?_,hr,hlen,?_⟩
  · simp only [preparationActions,Ptx.Async.Client.run_append,hs,Except.bind,Ptx.Async.run,hrecord]
    rfl
  · simp [next,hids,List.range_succ,List.reverse_append]

theorem public_preparation_succeeds (values : List Nat) (hv : values.length = 8) (tiles : Nat) :
    Ptx.Async.run (Ptx.Async.initial 1 values) (preparationActions tiles) = .ok (publicPrepared values tiles) := by
  obtain ⟨state,hs,_⟩ := preparation_exists values hv tiles
  simp only [publicPrepared,hs,Except.toOption,Option.getD_some]

theorem public_prepared_properties (values : List Nat) (hv : values.length = 8) (tiles : Nat) :
    Ptx.Async.Preparation.Ready (publicPrepared values tiles) (asyncCommands tiles) ∧
      (publicPrepared values tiles).buffers.length = 8 ∧
      (publicPrepared values tiles).events.map Ptx.Async.Event.id = (List.range (tiles+2)).reverse := by
  obtain ⟨state,hs,hr,hb,he⟩ := preparation_exists values hv tiles
  have hstate := Except.ok.inj (hs.symm.trans (public_preparation_succeeds values hv tiles))
  subst state
  exact ⟨hr,hb,he⟩

theorem public_prepared_invariant (values : List Nat) (hv : values.length = 8) (tiles : Nat) :
    Ptx.Async.Invariant (publicPrepared values tiles) :=
  Ptx.Async.steps_invariant (Ptx.Async.initial_invariant 1 values) (Ptx.Async.run_sound (public_preparation_succeeds values hv tiles))

theorem public_event_ids_unique (values : List Nat) (hv : values.length = 8) (tiles : Nat) :
    ((publicPrepared values tiles).events.map Ptx.Async.Event.id).Nodup := by
  rw [(public_prepared_properties values hv tiles).2.2]
  simpa using (List.nodup_range (n := tiles+2))

theorem public_final_event (values : List Nat) (hv : values.length = 8) (tiles : Nat) :
    Ptx.Async.getEvent (publicPrepared values tiles) (tiles+1) = .ok ⟨0,6*tiles⟩ := by
  obtain ⟨state,hs,hr,_,hids⟩ := prefix_preparation_exists values hv tiles
  let next := {state with events := ⟨tiles+1,⟨0,(asyncCommands tiles).length⟩⟩::state.events}
  have hrecord := Ptx.Async.Preparation.ready_record hr (indexed_event_fresh hids)
  have hrun : Ptx.Async.run (Ptx.Async.initial 1 values) (preparationActions tiles) = .ok next := by
    simp only [preparationActions,Ptx.Async.Client.run_append,hs,Except.bind,Ptx.Async.run,hrecord]
    rfl
  have heq := Except.ok.inj ((public_preparation_succeeds values hv tiles).symm.trans hrun)
  rw [heq]
  simp [Ptx.Async.getEvent,next,async_commands_length,bind,Except.bind,pure,Except.pure]

end
end Ptx.Kernels.HopperDoubleBuffer
