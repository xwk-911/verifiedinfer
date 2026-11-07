import Ptx.Kernels.SourceChecked
import Ptx.Generated.DivergentBarrier

/-! The archived source completes locally with matching abstract barriers but
is rejected by actual source-PC admission. A two-site/two-generation program is
accepted by dynamic matching, so the static sufficient certificate is not the
definition of legal alignment. -/
namespace Ptx.SourceOriginsTests
open Ptx.ISA Ptx.Event

abbrev badCode := Generated.divergent_barrier.program
abbrev badParams := BarrierPublish.params 0 7
def badWriter : ThreadTrace := {BarrierPublish.producer 0 7 with count := 8}
def badReader : ThreadTrace := {BarrierPublish.consumer 0 7 7 with
  count := 8
  final := { (BarrierPublish.consumer 0 7 7).final with
    thread := {(BarrierPublish.consumer 0 7 7).final.thread with pc := 7}}}
def bad : Candidate := ⟨[badWriter,badReader]⟩

theorem bad_writer_produced : badWriter.Produced badCode badParams := by unfold ThreadTrace.Produced; decide
theorem bad_reader_produced : badReader.Produced badCode badParams := by unfold ThreadTrace.Produced; decide
theorem bad_complete : bad.Complete := by
  intro t ht
  simp only [bad,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl
  · rfl
  · rfl

theorem bad_wellFormed (initial : ByteMap) : bad.WellFormed badCode (BarrierPublish.launch 0 7 initial) := by
  refine ⟨by change (⟨.one,⟨2,1,1⟩⟩ : Geometry).Valid; unfold Geometry.Valid Dim3.Positive; decide,by decide,?_,?_⟩
  · intro t ht
    simp only [bad,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨by change BarrierPublish.writer.Valid ⟨.one,⟨2,1,1⟩⟩; unfold ThreadId.Valid Dim3.Within; decide,bad_writer_produced⟩
    · exact ⟨by change BarrierPublish.reader.Valid ⟨.one,⟨2,1,1⟩⟩; unfold ThreadId.Valid Dim3.Within; decide,bad_reader_produced⟩
  · intro id hv
    rcases BarrierPublish.valid_id_cases hv with rfl | rfl
    · exact ⟨badWriter,by simp [bad],rfl⟩
    · exact ⟨badReader,by simp [bad],rfl⟩

theorem bad_eventAt (id : EventId) : bad.eventAt id =
    if id.thread = BarrierPublish.writer then (BarrierPublish.producer 0 7).events[id.serial]?
    else if id.thread = BarrierPublish.reader then (BarrierPublish.consumer 0 7 7).events[id.serial]? else none := by
  by_cases hw : id.thread = BarrierPublish.writer
  · simp [Candidate.eventAt,bad,badWriter,badReader,BarrierPublish.producer,BarrierPublish.consumer,hw]
  · by_cases hr : id.thread = BarrierPublish.reader
    · simp [Candidate.eventAt,bad,badWriter,badReader,BarrierPublish.producer,BarrierPublish.consumer,hw,hr,List.find?,beq_iff_eq,
        show BarrierPublish.writer ≠ BarrierPublish.reader by decide,
        show BarrierPublish.reader ≠ BarrierPublish.writer by decide]
    · simp [Candidate.eventAt,bad,badWriter,badReader,BarrierPublish.producer,BarrierPublish.consumer,hw,hr,beq_iff_eq,Ne.symm hw,Ne.symm hr]

theorem bad_same_abstract_events : SameEvents bad (BarrierPublish.graph 0 7 7) := by
  funext id
  rw [bad_eventAt,BarrierPublish.graph_eventAt]

theorem bad_sync : BarrierSync bad BarrierPublish.wa BarrierPublish.rr :=
  ⟨rfl,0,0,by decide,by decide⟩
theorem bad_writer_source : bad.sourcePC badCode badParams BarrierPublish.wa = some 9 := by decide
theorem bad_reader_source : bad.sourcePC badCode badParams BarrierPublish.rr = some 5 := by decide

theorem bad_not_source_aligned : ¬ bad.SourceAligned badCode badParams := by
  intro h
  obtain ⟨pc,hw,hr⟩ := h _ _ bad_sync
  rw [bad_writer_source] at hw
  rw [bad_reader_source] at hr
  have h9 := Option.some.inj hw
  have h5 := Option.some.inj hr
  omega

theorem bad_checked_rejected (initial : ByteMap) (rf : ReadsFrom) (co : Coherence) :
    ¬ CheckedConditions badCode (BarrierPublish.launch 0 7 initial) bad rf co := by
  intro h
  exact bad_not_source_aligned h.barrierSources

def repeatedCode : List Instr := [.barrier 0,.mov 32 "%r" (.imm 1),.barrier 0,.ret]
def repeatedEvents : List Kind := [.barrierArrival 0 0,.barrierReturn 0 0,.barrierArrival 0 1,.barrierReturn 0 1]
def repeatedFinal : State := {
  thread := {pc := 3,regs := [("%r",1)],status := .done}
  generations := [(0,2)]
}
def repeatedTrace (id : ThreadId) : ThreadTrace := ⟨id,fun _ => 0,4,repeatedFinal,repeatedEvents⟩
def repeated : Candidate := ⟨[repeatedTrace BarrierPublish.writer,repeatedTrace BarrierPublish.reader]⟩
def repeatedLocated : List (SourceRun.Located Kind) := [
  ⟨.barrierArrival 0 0,0⟩,⟨.barrierReturn 0 0,0⟩,⟨.barrierArrival 0 1,2⟩,⟨.barrierReturn 0 1,2⟩]

theorem repeated_produced (id : ThreadId) : (repeatedTrace id).Produced repeatedCode [] := by rfl
theorem repeated_located (id : ThreadId) :
    runLocated ⟨id,[]⟩ (fun _ => 0) repeatedCode 4 {} = .ok (repeatedFinal,repeatedLocated) := by rfl
theorem repeated_has_multiple_sites : uniqueBarrierSites repeatedCode = false := by decide

theorem repeated_origin {event : EventId} {kind : Kind} {bid generation : Nat}
    (he : repeated.eventAt event = some kind) (hk : BarrierKind bid generation kind) :
    repeated.sourcePC repeatedCode [] event = some (2*generation) := by
  obtain ⟨t,ht,htid,hindex⟩ := eventAt_trace he
  have hn : (repeated.traces.map ThreadTrace.id).Nodup := by decide
  have hem : t.events = repeatedEvents := by
    simp only [repeated,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl <;> rfl
  have hcount : event.serial < 4 := by
    have hh := (List.getElem?_eq_some_iff.mp hindex).1
    simpa only [hem,repeatedEvents,List.length_cons,List.length_nil] using hh
  have hsource : repeated.sourcePC repeatedCode [] event = (repeatedLocated[event.serial]?).map SourceRun.Located.pc := by
    unfold Candidate.sourcePC
    rw [sourceAt_of_trace hn ht htid.symm]
    simp only [repeated,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · dsimp only [repeatedTrace]
      rw [repeated_located]
      rfl
    · dsimp only [repeatedTrace]
      rw [repeated_located]
      rfl
  rw [hsource]
  rw [hem] at hindex
  rcases (show event.serial = 0 ∨ event.serial = 1 ∨ event.serial = 2 ∨ event.serial = 3 by omega) with hs | hs | hs | hs <;>
    simp [hs,repeatedEvents] at hindex <;> subst kind <;> rcases hk with hk | hk <;> cases hk <;> simp [hs,repeatedLocated]

theorem repeated_source_aligned : repeated.SourceAligned repeatedCode [] := by
  rintro a b ⟨_,bid,generation,ha,hb⟩
  exact ⟨2*generation,repeated_origin ha (.inl rfl),repeated_origin hb (.inr rfl)⟩

theorem repeated_wellFormed (initial : ByteMap) :
    repeated.WellFormed repeatedCode ⟨(BarrierPublish.launch 0 0 initial).geometry,[],initial⟩ := by
  refine ⟨by change (⟨.one,⟨2,1,1⟩⟩ : Geometry).Valid; unfold Geometry.Valid Dim3.Positive; decide,by decide,?_,?_⟩
  · intro t ht
    simp only [repeated,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨by change BarrierPublish.writer.Valid ⟨.one,⟨2,1,1⟩⟩; unfold ThreadId.Valid Dim3.Within; decide,repeated_produced _⟩
    · exact ⟨by change BarrierPublish.reader.Valid ⟨.one,⟨2,1,1⟩⟩; unfold ThreadId.Valid Dim3.Within; decide,repeated_produced _⟩
  · intro id hv
    rcases BarrierPublish.valid_id_cases (base := 0) (value := 0) (initial := initial) hv with rfl | rfl
    · exact ⟨repeatedTrace BarrierPublish.writer,by simp [repeated],rfl⟩
    · exact ⟨repeatedTrace BarrierPublish.reader,by simp [repeated],rfl⟩

theorem repeated_complete : repeated.Complete := by
  intro t ht
  simp only [repeated,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl <;> rfl

theorem repeated_trace_events {t : ThreadTrace} (ht : t ∈ repeated.traces) : t.events = repeatedEvents := by
  simp only [repeated,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl <;> rfl

theorem repeated_shape {event : EventId} {kind : Kind} (he : repeated.eventAt event = some kind) :
    (event.serial = 0 ∧ kind = .barrierArrival 0 0) ∨
    (event.serial = 1 ∧ kind = .barrierReturn 0 0) ∨
    (event.serial = 2 ∧ kind = .barrierArrival 0 1) ∨
    (event.serial = 3 ∧ kind = .barrierReturn 0 1) := by
  obtain ⟨t,ht,_,hindex⟩ := eventAt_trace he
  rw [repeated_trace_events ht] at hindex
  have hb := (List.getElem?_eq_some_iff.mp hindex).1
  change event.serial < 4 at hb
  rcases (show event.serial = 0 ∨ event.serial = 1 ∨ event.serial = 2 ∨ event.serial = 3 by omega) with hs | hs | hs | hs <;>
    simp [hs,repeatedEvents] at hindex <;> simp [hs,hindex]

theorem repeated_return {event : EventId} {bid generation : Nat}
    (he : repeated.eventAt event = some (.barrierReturn bid generation)) :
    bid = 0 ∧ generation ≤ 1 ∧ event.serial = 2*generation+1 := by
  rcases repeated_shape he with ⟨_,hk⟩ | ⟨hs,hk⟩ | ⟨_,hk⟩ | ⟨hs,hk⟩ <;> simp_all

theorem repeated_sync_rank {a b : EventId} (hs : BarrierSync repeated a b) : a.serial < b.serial := by
  obtain ⟨_,bid,generation,ha,hb⟩ := hs
  rcases repeated_shape ha with ⟨ha,hka⟩ | ⟨ha,hka⟩ | ⟨ha,hka⟩ | ⟨ha,hka⟩ <;>
    rcases repeated_shape hb with ⟨hb,hkb⟩ | ⟨hb,hkb⟩ | ⟨hb,hkb⟩ | ⟨hb,hkb⟩ <;> simp_all

theorem repeated_arrival_index {generation : Nat} (hg : generation ≤ 1) :
    repeatedEvents[2*generation]? = some (.barrierArrival 0 generation) := by
  rcases (show generation = 0 ∨ generation = 1 by omega) with rfl | rfl <;> rfl

theorem repeated_barriers : BarrierParticipation repeated := by
  intro leave bid generation he
  obtain ⟨rfl,hg,hserial⟩ := repeated_return he
  obtain ⟨t,ht,htid,_⟩ := eventAt_trace he
  constructor
  · refine ⟨⟨leave.thread,2*generation⟩,rfl,by change 2*generation < leave.serial; omega,?_⟩
    rw [eventAt_of_trace (id := ⟨leave.thread,2*generation⟩) (by decide) ht htid.symm,repeated_trace_events ht]
    exact repeated_arrival_index hg
  · intro peer hpeer _
    left
    rw [repeated_trace_events hpeer]
    exact List.mem_of_getElem? (repeated_arrival_index hg)

theorem repeated_no_exit {a b : EventId} : ¬ ExitBeforeReturn repeated a b := by
  rintro ⟨_,t,ht,_,_,bid,generation,he,hx⟩
  obtain ⟨rfl,hg,_⟩ := repeated_return he
  have hlast : Kind.barrierArrival 0 1 ∈ t.events := by rw [repeated_trace_events ht]; simp [repeatedEvents]
  have hh := hx.2 1 hlast
  omega

theorem repeated_no_memory (event : EventId) (loc : Location) :
    repeated.readByte event loc = none ∧ repeated.writeByte event loc = none := by
  cases he : repeated.eventAt event with
  | none => simp [Candidate.readByte,Candidate.writeByte,he]
  | some kind =>
    rcases repeated_shape he with ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
      simp [Candidate.readByte,Candidate.writeByte,he,Kind.readByte,Kind.writeByte]

theorem repeated_memory (initial : ByteMap) : GenericMemoryConditions repeated initial
    (fun _ _ => .initial) (InitialCo repeated) := by
  apply initial_co_conditions (fun event => event.serial)
  · intro a b hp; exact hp.2.2.2
  · intro a b hs; exact repeated_sync_rank hs
  · intro a b he; exact (repeated_no_exit he).elim
  · exact repeated_barriers
  · intro loc a b va vb ha _
    rw [(repeated_no_memory a loc).2] at ha
    cases ha
  · intro read loc value hr
    rw [(repeated_no_memory read loc).1] at hr
    cases hr
  · intro read writer loc vr vw hr _ _
    rw [(repeated_no_memory read loc).1] at hr
    cases hr
  · intro read writer loc vr vw hr _ _
    rw [(repeated_no_memory read loc).1] at hr
    cases hr

theorem repeated_checked (initial : ByteMap) : CheckedConditions repeatedCode
    ⟨(BarrierPublish.launch 0 0 initial).geometry,[],initial⟩ repeated (fun _ _ => .initial) (InitialCo repeated) :=
  ⟨repeated_wellFormed initial,repeated_source_aligned,repeated_memory initial⟩

theorem repeated_observer (initial : ByteMap) (domain : List Location)
    (hglobal : ∀ loc ∈ domain, loc.space = .global) : ObserverConditions repeated initial
    (fun _ _ => .initial) (InitialCo repeated) ⟨domain,initial,fun _ => .initial⟩ := by
  refine ⟨repeated_complete,hglobal,?_,?_⟩
  · intro loc _ _
    rfl
  · intro loc _ _ writer value hw
    rw [(repeated_no_memory writer loc).2] at hw
    cases hw

theorem repeated_accepted (initial : ByteMap) (domain : List Location)
    (hglobal : ∀ loc ∈ domain, loc.space = .global) :
    ∃ c rf co o, CheckedConditions repeatedCode
      ⟨(BarrierPublish.launch 0 0 initial).geometry,[],initial⟩ c rf co ∧
      ObserverConditions c initial rf co o ∧ o.domain = domain ∧ o.output = initial :=
  ⟨repeated,(fun _ _ => .initial),InitialCo repeated,⟨domain,initial,fun _ => .initial⟩,
    repeated_checked initial,repeated_observer initial domain hglobal,rfl,rfl⟩

end Ptx.SourceOriginsTests
