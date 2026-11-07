import Ptx.Generated.BarrierPublish
import Ptx.Event.Observation
import Ptx.Event.Trace

/-! Two-thread publication over the actual generated PTX. The witness family
keeps the input and reader oracle separate so rejection does not presume the
desired answer. These event-model proofs do not establish allocation/ISA UB
freedom, full PTX correspondence or compiler/runtime correctness. -/
namespace Ptx.BarrierPublish
open Ptx.ISA Ptx.Event

abbrev code := Generated.barrier_publish.program
def writer : ThreadId := ⟨.zero, .zero⟩
def reader : ThreadId := ⟨.zero, ⟨1, 0, 0⟩⟩
def w : EventId := ⟨writer, 0⟩
def wa : EventId := ⟨writer, 1⟩
def wr : EventId := ⟨writer, 2⟩
def ra : EventId := ⟨reader, 0⟩
def rr : EventId := ⟨reader, 1⟩
def r : EventId := ⟨reader, 2⟩
def loc (base : Nat) : Location := ⟨.global, wrap 64 base⟩
def bytes (value : Nat) : List Byte := encodeU32 (wrap 32 value)
def params (base value : Nat) : Bindings := [("x", base), ("value", value)]

def producer (base value : Nat) : ThreadTrace := {
  id := writer
  oracle := fun _ => 0
  count := 9
  final := { thread := { pc := 10, regs := [("%p", 1), ("%i", 0), ("%v", wrap 32 value), ("%d", wrap 64 base)], status := .done }, generations := [(0,1)] }
  events := [.write (loc base) (bytes value), .barrierArrival 0 0, .barrierReturn 0 0]
}
def consumer (base value answer : Nat) : ThreadTrace := {
  id := reader
  oracle := fun _ => answer
  count := 10
  final := { thread := { pc := 10, regs := [("%r", wrap 32 answer), ("%p", 0), ("%i", 1), ("%v", wrap 32 value), ("%d", wrap 64 base)], status := .done }, queries := 1, generations := [(0,1)] }
  events := [.barrierArrival 0 0, .barrierReturn 0 0, .read (loc base) (bytes answer)]
}
def graph (base value answer : Nat) : Candidate := ⟨[producer base value, consumer base value answer]⟩
def launch (base value : Nat) (initial : ByteMap) : Launch :=
  ⟨⟨.one, ⟨2, 1, 1⟩⟩, params base value, initial⟩

theorem producer_run (base value : Nat) (oracle : Oracle) :
    Event.run ⟨writer, params base value⟩ oracle code 9 {} =
      .ok ((producer base value).final, (producer base value).events) := by
  simp [code, Generated.barrier_publish.program, params, producer,
    Event.run, Event.step, localStep, eval, evalAddr, assign, advance, put, lookup, wrap,
    Event.generation, writer, Dim3.zero, loc, bytes, Location.resolve,
    bind, Except.bind, pure, Except.pure]
theorem consumer_run (base value : Nat) (oracle : Oracle) :
    Event.run ⟨reader, params base value⟩ oracle code 10 {} =
      .ok ((consumer base value (oracle 0)).final, (consumer base value (oracle 0)).events) := by
  simp [code, Generated.barrier_publish.program, params, consumer,
    Event.run, Event.step, localStep, eval, evalAddr, assign, advance, put, lookup, wrap,
    Event.generation, reader, Dim3.zero, loc, bytes, Location.resolve,
    bind, Except.bind, pure, Except.pure]

theorem producer_produced (base value : Nat) :
    (producer base value).Produced code (params base value) := producer_run base value (fun _ => 0)

theorem consumer_produced (base value answer : Nat) :
    (consumer base value answer).Produced code (params base value) := consumer_run base value (fun _ => answer)

theorem producer_trace_shape {base value : Nat} {t : ThreadTrace}
    (hp : t.Produced code (params base value)) (hid : t.id = writer)
    (hd : t.final.thread.status = .done) :
    t.count = 9 ∧ t.final = (producer base value).final ∧ t.events = (producer base value).events := by
  have hrun : Event.run ⟨writer, params base value⟩ t.oracle code t.count {} = .ok (t.final, t.events) := by
    simpa only [ThreadTrace.Produced, hid] using hp
  exact complete_run_unique hrun hd (producer_run base value t.oracle) rfl

theorem consumer_trace_shape {base value : Nat} {t : ThreadTrace}
    (hp : t.Produced code (params base value)) (hid : t.id = reader)
    (hd : t.final.thread.status = .done) :
    t.count = 10 ∧ t.final = (consumer base value (t.oracle 0)).final ∧
      t.events = (consumer base value (t.oracle 0)).events := by
  have hrun : Event.run ⟨reader, params base value⟩ t.oracle code t.count {} = .ok (t.final, t.events) := by
    simpa only [ThreadTrace.Produced, hid] using hp
  exact complete_run_unique hrun hd (consumer_run base value t.oracle) rfl

theorem valid_id_cases {base value : Nat} {initial : ByteMap} {id : ThreadId}
    (h : id.Valid (launch base value initial).geometry) : id = writer ∨ id = reader := by
  rcases id with ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩
  simp only [ThreadId.Valid, Dim3.Within, launch, Dim3.one] at h
  have hs : cx = 0 ∧ cy = 0 ∧ cz = 0 ∧ ty = 0 ∧ tz = 0 ∧ (tx = 0 ∨ tx = 1) := by omega
  rcases hs with ⟨rfl,rfl,rfl,rfl,rfl,ht⟩
  rcases ht with rfl | rfl
  · exact .inl rfl
  · exact .inr rfl

theorem event_cases {base value answer id kind}
    (he : (graph base value answer).eventAt id = some kind) :
    (id = w ∧ kind = .write (loc base) (bytes value)) ∨
    (id = wa ∧ kind = .barrierArrival 0 0) ∨
    (id = wr ∧ kind = .barrierReturn 0 0) ∨
    (id = ra ∧ kind = .barrierArrival 0 0) ∨
    (id = rr ∧ kind = .barrierReturn 0 0) ∨
    (id = r ∧ kind = .read (loc base) (bytes answer)) := by
  obtain ⟨t, ht, hid, hindex⟩ := eventAt_trace he
  have hn := (List.getElem?_eq_some_iff.mp hindex).1
  simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases id with ⟨thread, serial⟩
  rcases ht with ht | ht
  · subst t
    have hi : thread = writer := hid.symm
    subst thread
    have hs : serial = 0 ∨ serial = 1 ∨ serial = 2 := by simp [producer] at hn; omega
    rcases hs with hs | hs | hs <;> subst serial
    · exact .inl ⟨rfl, by simpa [producer] using hindex.symm⟩
    · exact .inr (.inl ⟨rfl, by simpa [producer] using hindex.symm⟩)
    · exact .inr (.inr (.inl ⟨rfl, by simpa [producer] using hindex.symm⟩))
  · subst t
    have hi : thread = reader := hid.symm
    subst thread
    have hs : serial = 0 ∨ serial = 1 ∨ serial = 2 := by simp [consumer] at hn; omega
    rcases hs with hs | hs | hs <;> subst serial
    · exact .inr (.inr (.inr (.inl ⟨rfl, by simpa [consumer] using hindex.symm⟩)))
    · exact .inr (.inr (.inr (.inr (.inl ⟨rfl, by simpa [consumer] using hindex.symm⟩))))
    · exact .inr (.inr (.inr (.inr (.inr ⟨rfl, by simpa [consumer] using hindex.symm⟩))))

def rank (id : EventId) : Nat := if id.thread = writer then id.serial else id.serial + 1

theorem po_rank {base value answer a b} (h : ProgramOrder (graph base value answer) a b) :
    rank a < rank b := by
  have ht := h.2.2.1
  have hs := h.2.2.2
  unfold rank
  rw [ht]
  split <;> omega

theorem arrival_shape {base value answer id bid generation}
    (h : (graph base value answer).eventAt id = some (.barrierArrival bid generation)) :
    (id = wa ∨ id = ra) ∧ bid = 0 ∧ generation = 0 := by
  rcases event_cases h with h | h | h | h | h | h <;> rcases h with ⟨rfl,hk⟩ <;>
    cases hk
  · exact ⟨.inl rfl, rfl, rfl⟩
  · exact ⟨.inr rfl, rfl, rfl⟩

theorem return_shape {base value answer id bid generation}
    (h : (graph base value answer).eventAt id = some (.barrierReturn bid generation)) :
    (id = wr ∨ id = rr) ∧ bid = 0 ∧ generation = 0 := by
  rcases event_cases h with h | h | h | h | h | h <;> rcases h with ⟨rfl,hk⟩ <;>
    cases hk
  · exact ⟨.inl rfl, rfl, rfl⟩
  · exact ⟨.inr rfl, rfl, rfl⟩

theorem sync_rank {base value answer a b} (h : BarrierSync (graph base value answer) a b) :
    rank a < rank b := by
  obtain ⟨_, bid, generation, ha, hb⟩ := h
  rcases (arrival_shape ha).1 with rfl | rfl <;>
    rcases (return_shape hb).1 with rfl | rfl <;> decide

theorem no_exit_edges {base value answer a b} : ¬ ExitBeforeReturn (graph base value answer) a b := by
  rintro ⟨_, t, ht, _, _, bid, generation, hb, he⟩
  obtain ⟨_, rfl, rfl⟩ := return_shape hb
  have hm : Kind.barrierArrival 0 0 ∈ t.events := by
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp [producer, consumer]
  exact Nat.lt_irrefl 0 (he.2 0 hm)

theorem barriers (base value answer : Nat) : BarrierParticipation (graph base value answer) := by
  intro leave bid generation he
  obtain ⟨hid, rfl, rfl⟩ := return_shape he
  constructor
  · rcases hid with rfl | rfl
    · exact ⟨wa, rfl, by decide, rfl⟩
    · exact ⟨ra, rfl, by decide, rfl⟩
  · intro t ht _
    left
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp [producer, consumer]

theorem read_shape {base value answer read address v}
    (hr : (graph base value answer).readByte read address = some v) :
    read = r ∧ payloadByte (loc base) (bytes answer) address = some v := by
  cases he : (graph base value answer).eventAt read with
  | none => simp [Candidate.readByte, he] at hr
  | some kind =>
    rcases event_cases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals simp [Candidate.readByte, he, Kind.readByte] at hr
    exact ⟨rfl, hr⟩

theorem write_shape {base value answer writer address v}
    (hw : (graph base value answer).writeByte writer address = some v) :
    writer = w ∧ payloadByte (loc base) (bytes value) address = some v := by
  cases he : (graph base value answer).eventAt writer with
  | none => simp [Candidate.writeByte, he] at hw
  | some kind =>
    rcases event_cases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals simp [Candidate.writeByte, he, Kind.writeByte] at hw
    exact ⟨rfl, hw⟩

def rf : ReadsFrom := fun _ _ => .write w

theorem memory_witness (base value : Nat) (initial : ByteMap) :
    GenericMemoryConditions (graph base value value) initial rf (InitialCo (graph base value value)) := by
  apply initial_co_conditions rank
  · exact fun _ _ h => po_rank h
  · exact fun _ _ h => sync_rank h
  · intro a b h; exact (no_exit_edges h).elim
  · exact barriers base value value
  · intro address a b va vb ha hb
    exact (write_shape ha).1.trans (write_shape hb).1.symm
  · intro read address v hr
    obtain ⟨rfl,hpayload⟩ := read_shape hr
    change (graph base value value).writeByte w address = some v
    exact hpayload
  · intro read writer address vr vw hr hw _
    obtain ⟨rfl,_⟩ := read_shape hr
    obtain ⟨rfl,_⟩ := write_shape hw
    decide
  · intro read writer address vr vw hr hw hinit
    cases hinit

theorem wellFormed (base value answer : Nat) (initial : ByteMap) :
    (graph base value answer).WellFormed code (launch base value initial) := by
  refine ⟨by simp [launch, Geometry.Valid, Dim3.Positive, Dim3.one], ?_, ?_, ?_⟩
  · simp [graph, producer, consumer, writer, reader, Dim3.zero]
  · intro t ht
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨by simp [ThreadId.Valid, Dim3.Within, producer, writer, Dim3.zero, launch, Dim3.one],
        producer_produced base value⟩
    · exact ⟨by simp [ThreadId.Valid, Dim3.Within, consumer, reader, Dim3.zero, launch, Dim3.one],
        consumer_produced base value answer⟩
  · intro id hid
    rcases id with ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩
    simp only [ThreadId.Valid, Dim3.Within, launch, Dim3.one] at hid
    have hs : cx = 0 ∧ cy = 0 ∧ cz = 0 ∧ ty = 0 ∧ tz = 0 ∧ (tx = 0 ∨ tx = 1) := by omega
    rcases hs with ⟨rfl,rfl,rfl,rfl,rfl,ht⟩
    rcases ht with rfl | rfl
    · exact ⟨producer base value, by simp [graph], rfl⟩
    · exact ⟨consumer base value answer, by simp [graph], rfl⟩

theorem complete (base value answer : Nat) : (graph base value answer).Complete := by
  intro t ht
  simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> rfl

theorem consistent_execution_exists (base value : Nat) (initial : ByteMap) :
    ∃ c sources order, c.WellFormed code (launch base value initial) ∧ c.Complete ∧
      GenericMemoryConditions c initial sources order :=
  ⟨graph base value value, rf, InitialCo (graph base value value),
    wellFormed base value value initial, complete base value value, memory_witness base value initial⟩

theorem write_before_read (base value answer : Nat) (sources : ReadsFrom) :
    Causality (graph base value answer) sources w r := by
  apply barrier_memory_causal (write := w) (arrive := wa) (leave := rr) (read := r)
  · refine ⟨loc base, .inr ?_, .inl ?_⟩
    · change (payloadByte (loc base) (bytes value) (loc base)).isSome = true
      simp [payloadByte, bytes]
    · change (payloadByte (loc base) (bytes answer) (loc base)).isSome = true
      simp [payloadByte, bytes]
  · exact ⟨rfl, rfl, rfl, by decide⟩
  · exact ⟨rfl, 0, 0, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, by decide⟩

theorem memory_id_cases {base value answer id address}
    (h : (graph base value answer).Accesses id address) : id = w ∨ id = r := by
  rcases h with hr | hw
  · cases he : (graph base value answer).readByte id address with
    | none => simp [he] at hr
    | some v => exact .inr (read_shape he).1
  · cases he : (graph base value answer).writeByte id address with
    | none => simp [he] at hw
    | some v => exact .inl (write_shape he).1

theorem no_races (base value answer : Nat) (sources : ReadsFrom) (a b) :
    ¬ DataRace (graph base value answer) sources a b := by
  intro hrace
  obtain ⟨address,ha,hb⟩ := hrace.overlap
  rcases memory_id_cases ha with rfl | rfl <;> rcases memory_id_cases hb with rfl | rfl
  · exact hrace.notStrong ⟨Or.inl rfl, (loc base, 4), rfl, rfl⟩
  · exact hrace.notForward (write_before_read base value answer sources)
  · exact hrace.notBackward (write_before_read base value answer sources)
  · rcases hrace.conflict with ⟨address,v,hv⟩ | ⟨address,v,hv⟩
    all_goals
      have hn : (graph base value answer).writeByte r address = none := rfl
      rw [hn] at hv
      cases hv

/-- Correctness for the entire reader-oracle family, with ANY reads-from and
coherence witnesses. No particular oracle answer is assumed by the theorem.
BarrierPublishUniversal.lean separately proves provenance completeness and lifts
this characterized family to arbitrary complete candidates. -/
theorem family_output_correct {base value answer initial sources order}
    (hc : GenericMemoryConditions (graph base value answer) initial sources order) :
    wrap 32 answer = wrap 32 value := by
  have heq : bytes answer = bytes value := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < 4
    · have ha : i < (bytes answer).length := by simpa [bytes] using hi
      have hv : i < (bytes value).length := by simpa [bytes] using hi
      have hr : (graph base value answer).readByte r ((loc base).add i) = some ((bytes answer)[i]'ha) := by
        change payloadByte (loc base) (bytes answer) ((loc base).add i) = _
        simpa only [payloadByte_offset] using List.getElem?_eq_getElem ha
      have hw : (graph base value answer).writeByte w ((loc base).add i) = some ((bytes value)[i]'hv) := by
        change payloadByte (loc base) (bytes value) ((loc base).add i) = _
        simpa only [payloadByte_offset] using List.getElem?_eq_getElem hv
      have he := race_free_eligible (no_races base value answer sources) r ((loc base).add i)
      have hval := unique_writer_visible hc he hw hr (write_before_read base value answer sources)
        (fun _ _ h => (write_shape h).1)
      simpa only [List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hv] using congrArg some hval
    · have ha : (bytes answer).length ≤ i := by simp only [bytes, encodeU32_length]; omega
      have hv : (bytes value).length ≤ i := by simp only [bytes, encodeU32_length]; omega
      rw [List.getElem?_eq_none ha, List.getElem?_eq_none hv]
  have hword := congrArg decodeLE heq
  simpa [bytes, decode_encodeU32, wrap] using hword

def wordDomain (base : Nat) : List Location := (List.range 4).map (fun i => (loc base).add i)

theorem wordDomain_global (base : Nat) (address) (h : address ∈ wordDomain base) :
    address.space = .global := by
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
  rfl

theorem observation_witness (base value : Nat) (initial : ByteMap) :
    ObserverConditions (graph base value value) initial rf (InitialCo (graph base value value))
      (singleWriterObservation (graph base value value) initial w (wordDomain base)) :=
  single_writer_observation (complete base value value) (wordDomain_global base)
    (fun _ _ _ h => (write_shape h).1)

theorem observed_execution_exists (base value : Nat) (initial : ByteMap) :
    ∃ c sources order o, c.WellFormed code (launch base value initial) ∧
      GenericMemoryConditions c initial sources order ∧
      ObserverConditions c initial sources order o ∧ o.domain = wordDomain base :=
  ⟨graph base value value, rf, InitialCo (graph base value value),
    singleWriterObservation (graph base value value) initial w (wordDomain base),
    wellFormed base value value initial, memory_witness base value initial, observation_witness base value initial, rfl⟩

theorem observed_byte_correct {base value answer initial sources order o}
    (hc : GenericMemoryConditions (graph base value answer) initial sources order)
    (ho : ObserverConditions (graph base value answer) initial sources order o)
    (hd : o.domain = wordDomain base) (i : Nat) (hi : i < 4) :
    o.output ((loc base).add i) = (bytes value)[i]'(by simpa [bytes] using hi) := by
  have hmem : (loc base).add i ∈ o.domain := by
    rw [hd]
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have he := race_free_observer_eligible (no_races base value answer sources) ((loc base).add i)
  apply observer_unique_writer hc ho hmem he (writer := w)
  · change payloadByte (loc base) (bytes value) ((loc base).add i) = _
    simpa only [payloadByte_offset] using List.getElem?_eq_getElem (show i < (bytes value).length by simpa [bytes] using hi)
  · exact fun _ _ h => (write_shape h).1

def observedU32 (o : Observation) (base : Nat) : Nat :=
  decodeLE [o.output ((loc base).add 0), o.output ((loc base).add 1),
    o.output ((loc base).add 2), o.output ((loc base).add 3)]

theorem observed_word_correct {base value answer initial sources order o}
    (hc : GenericMemoryConditions (graph base value answer) initial sources order)
    (ho : ObserverConditions (graph base value answer) initial sources order o)
    (hd : o.domain = wordDomain base) : observedU32 o base = wrap 32 value := by
  unfold observedU32
  rw [observed_byte_correct hc ho hd 0 (by decide), observed_byte_correct hc ho hd 1 (by decide),
    observed_byte_correct hc ho hd 2 (by decide), observed_byte_correct hc ho hd 3 (by decide)]
  change decodeLE (bytes value) = wrap 32 value
  simp [bytes, decode_encodeU32, wrap]

end Ptx.BarrierPublish
