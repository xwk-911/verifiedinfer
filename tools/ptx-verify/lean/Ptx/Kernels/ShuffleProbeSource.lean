import Ptx.Kernels.ShuffleProbeStores

/-! Reconstruct arbitrary completed candidates of the exported probes. Local
oracle replies are not canonicalized. Actual stores retain their own memory
serials after the shuffle event is filtered from the ordinary memory view. -/
namespace Ptx.Kernels.ShuffleProbe
open Ptx.ISA Ptx.Shuffle
noncomputable section

def context (launch : Scalar.Launch) (id : ThreadId) : Scalar.Context :=
  {id := id,params := launch.params,block := launch.geometry.block}

theorem member_source_shape {mode input launch candidate trace} (hp : Params input launch.params)
    (hw : Shuffle.WellFormed (code mode) launch candidate) (hc : Shuffle.Complete candidate)
    (ht : trace ∈ candidate.traces) :
    trace.count = 24 ∧
    trace.final = finalState mode input (context launch trace.id) (trace.oracle.shuffle 0).1 (trace.oracle.shuffle 0).2 ∧
    trace.events = events mode input (context launch trace.id) (trace.oracle.shuffle 0).1 (trace.oracle.shuffle 0).2 :=
  completed_source_shape hp (hw.2.2.1 trace ht).2 (hc trace ht)

theorem actual_event_shape {mode input launch candidate actual kind} (hp : Params input launch.params)
    (hw : Shuffle.WellFormed (code mode) launch candidate) (hc : Shuffle.Complete candidate)
    (he : candidate.eventAt actual = some kind) :
    ∃ trace ∈ candidate.traces, trace.id = actual.thread ∧
      (events mode input (context launch trace.id) (trace.oracle.shuffle 0).1 (trace.oracle.shuffle 0).2)[actual.serial]? = some kind := by
  obtain ⟨trace,ht,hi,hget⟩ := Shuffle.eventAt_trace he
  exact ⟨trace,ht,hi,(member_source_shape hp hw hc ht).2.2 ▸ hget⟩

theorem actual_shuffle_shape {mode input launch candidate actual result} (hp : Params input launch.params)
    (hw : Shuffle.WellFormed (code mode) launch candidate) (hc : Shuffle.Complete candidate)
    (he : candidate.shuffleAt actual = some result) :
    ∃ trace ∈ candidate.traces, trace.id = actual.thread ∧ actual.serial = 0 ∧
      result = record mode input (context launch trace.id) (trace.oracle.shuffle 0).1 (trace.oracle.shuffle 0).2 := by
  obtain ⟨trace,ht,hi,hget⟩ := actual_event_shape hp hw hc (Shuffle.shuffleAt_eventAt he)
  cases hn : actual.serial with
  | zero =>
    simp only [hn,events,List.getElem?_cons_zero,Option.some.injEq] at hget
    exact ⟨trace,ht,hi,rfl,(Shuffle.Kind.shuffle.inj hget).symm⟩
  | succ serial =>
    cases serial with
    | zero => simp [hn,events,outputEvents] at hget
    | succ serial =>
      cases serial with
      | zero => simp [hn,events,outputEvents] at hget
      | succ serial => simp [hn,events,outputEvents] at hget

theorem shuffle_member_lookup {mode input launch candidate trace} (hp : Params input launch.params)
    (hw : Shuffle.WellFormed (code mode) launch candidate) (hc : Shuffle.Complete candidate)
    (ht : trace ∈ candidate.traces) :
    candidate.shuffleAt ⟨trace.id,0⟩ =
      some (record mode input (context launch trace.id) (trace.oracle.shuffle 0).1 (trace.oracle.shuffle 0).2) := by
  unfold Shuffle.Candidate.shuffleAt
  rw [Shuffle.eventAt_of_member hw.2.1 ht rfl,(member_source_shape hp hw hc ht).2.2]
  rfl

theorem output_member_lookups {mode input launch candidate trace} (hp : Params input launch.params)
    (hw : Shuffle.WellFormed (code mode) launch candidate) (hc : Shuffle.Complete candidate)
    (ht : trace ∈ candidate.traces) :
    candidate.view.eventAt ⟨trace.id,0⟩ = some (.write (outputLoc input (context launch trace.id) 0)
      ((encodeU32 (w32 (trace.oracle.shuffle 0).1)).map Symbolic.Byte.bits)) ∧
    candidate.view.eventAt ⟨trace.id,1⟩ = some (.write (outputLoc input (context launch trace.id) 4)
      ((encodeU32 (if (trace.oracle.shuffle 0).2 then 1 else 0)).map Symbolic.Byte.bits)) := by
  constructor <;> rw [Shuffle.view_eventAt_of_member hw.2.1 ht rfl,(member_source_shape hp hw hc ht).2.2] <;> rfl

theorem actual_memory_event_shape {mode input launch candidate actual kind} (hp : Params input launch.params)
    (hw : Shuffle.WellFormed (code mode) launch candidate) (hc : Shuffle.Complete candidate)
    (he : candidate.view.eventAt actual = some kind) :
    ∃ trace ∈ candidate.traces, trace.id = actual.thread ∧
      (actual.serial = 0 ∧ kind = .write (outputLoc input (context launch trace.id) 0)
        ((encodeU32 (w32 (trace.oracle.shuffle 0).1)).map Symbolic.Byte.bits) ∨
       actual.serial = 1 ∧ kind = .write (outputLoc input (context launch trace.id) 4)
        ((encodeU32 (if (trace.oracle.shuffle 0).2 then 1 else 0)).map Symbolic.Byte.bits)) := by
  obtain ⟨mapped,hm,hi,hget⟩ := Ptx.Event.eventAt_trace he
  obtain ⟨trace,ht,rfl⟩ := List.mem_map.mp hm
  have hev := (member_source_shape hp hw hc ht).2.2
  change (ordinaryEvents trace.events)[actual.serial]? = some kind at hget
  rw [hev] at hget
  refine ⟨trace,ht,hi,?_⟩
  cases hn : actual.serial with
  | zero => exact Or.inl ⟨rfl,Option.some.inj (by simpa [hn,events,outputEvents,ordinaryEvents] using hget.symm)⟩
  | succ serial =>
    cases serial with
    | zero => exact Or.inr ⟨rfl,Option.some.inj (by simpa [hn,events,outputEvents,ordinaryEvents] using hget.symm)⟩
    | succ serial => simp [hn,events,outputEvents,ordinaryEvents] at hget

theorem no_ordinary_reads {mode input launch candidate} (hp : Params input launch.params)
    (hw : Shuffle.WellFormed (code mode) launch candidate) (hc : Shuffle.Complete candidate) :
    ∀ actual loc, candidate.view.readByte actual loc = none := by
  intro actual loc
  cases he : candidate.view.eventAt actual with
  | none => simp [Ptx.Event.Candidate.readByte,he]
  | some kind =>
    obtain ⟨_,_,_,⟨_,rfl⟩ | ⟨_,rfl⟩⟩ := actual_memory_event_shape hp hw hc he
    all_goals simp [Ptx.Event.Candidate.readByte,he,Ptx.Event.Kind.readByte]

theorem agreed_value_is_actually_stored {mode input launch candidate trace} (hp : Params input launch.params)
    (hw : Shuffle.WellFormed (code mode) launch candidate) (hc : Shuffle.Complete candidate)
    (hd : Defined launch.geometry.block candidate) (ha : Agreement launch.geometry.block candidate)
    (ht : trace ∈ candidate.traces) :
    ∃ peer ∈ candidate.traces,
      SameWarp launch.geometry.block trace.id peer.id ∧
      lane launch.geometry.block peer.id = (select mode (lane launch.geometry.block trace.id) (w32 input.b) (w32 input.c)).source ∧
      candidate.view.eventAt ⟨trace.id,0⟩ = some (.write (outputLoc input (context launch trace.id) 0)
        ((encodeU32 (inputWord input (context launch peer.id))).map Symbolic.Byte.bits)) ∧
      candidate.view.eventAt ⟨trace.id,1⟩ = some (.write (outputLoc input (context launch trace.id) 4)
        ((encodeU32 (if (select mode (lane launch.geometry.block trace.id) (w32 input.b) (w32 input.c)).predicate then 1 else 0)).map Symbolic.Byte.bits)) := by
  obtain ⟨peerEvent,peerRecord,hlookup,hsource,hvalue,hpredicate⟩ :=
    Shuffle.defined_transfer ha hd (shuffle_member_lookup hp hw hc ht)
  obtain ⟨peer,hm,hi,_,hr⟩ := actual_shuffle_shape hp hw hc hlookup
  rw [hr] at hsource hvalue
  have hv : w32 (trace.oracle.shuffle 0).1 = inputWord input (context launch peer.id) := hvalue
  have hpred : (trace.oracle.shuffle 0).2 =
      (select mode (lane launch.geometry.block trace.id) (w32 input.b) (w32 input.c)).predicate := hpredicate
  obtain ⟨hstore,hflag⟩ := output_member_lookups hp hw hc ht
  refine ⟨peer,hm,?_,?_,?_,?_⟩
  · simpa only [hi] using hsource.1
  · simpa only [hi,record,groupKey] using hsource.2.1
  · simpa only [hv] using hstore
  · simpa only [hpred] using hflag

end
end Ptx.Kernels.ShuffleProbe
