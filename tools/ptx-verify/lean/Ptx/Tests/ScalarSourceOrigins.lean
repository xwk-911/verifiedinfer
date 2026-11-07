import Ptx.Scalar.Checked
import Ptx.Tests.SourceOrigins
import Mathlib.Tactic.NormNum

/-! Actual mixed execution with floating operations, multiple barrier sites and
launch-dependent control. Replacing the real block by the unit block changes
the executed path and invalidates the recorded source execution. -/
namespace Ptx.ScalarSourceOriginsTests
open Ptx.ISA
noncomputable section

def zero : Scalar.FloatOperand := .literal ⟨0,by decide,by decide⟩
def code : List Scalar.Instr := [
  .readSpecial "%sx" (.ntid .x),
  .integer (.setp .eq "%p" (.reg "%sx") (.imm 2)),
  .integer (.branch "%p" true 6),
  .integer (.barrier 0),.integer .ret,.integer .ret,
  .mov .f32 "%f" zero,.integer (.barrier 0),
  .addRn .f32 "%f" (.reg "%f") (.reg "%f"),.integer (.barrier 0),.integer .ret]
def oracle : Scalar.Oracle := fun _ => .integer 0
def block : Dim3 := ⟨2,1,1⟩
def final : Scalar.State := {
  core := {thread := {pc := 10,regs := [("%p",1),("%sx",2)],status := .done},generations := [(0,2)]}
  floats := [("%f",(.f32,0))]
}
def events : List Scalar.Kind := [.barrierArrival 0 0,.barrierReturn 0 0,.barrierArrival 0 1,.barrierReturn 0 1]
def located : List (SourceRun.Located Scalar.Kind) := [
  ⟨.barrierArrival 0 0,7⟩,⟨.barrierReturn 0 0,7⟩,⟨.barrierArrival 0 1,9⟩,⟨.barrierReturn 0 1,9⟩]

theorem located_run (id : ThreadId) : Scalar.runLocated {id := id,block := block} oracle code 8 {} = .ok (final,located) := by
  norm_num [Scalar.runLocated,SourceRun.run,Scalar.step,code,oracle,block,zero,final,located,
    Scalar.eval,Scalar.require,Scalar.liftInteger,Scalar.finishInteger,Scalar.writeFloat,
    Scalar.liftKind,Scalar.integerOracle,Event.step,Event.generation,localStep,Ptx.eval,
    Scalar.integer_delegate_fetch,Scalar.SpecialRegister.value,Scalar.Axis.component,
    assign,advance,put,lookup,declarationLookup,wrap,bind,Except.bind,pure,Except.pure]

theorem actual_run (id : ThreadId) : Scalar.run {id := id,block := block} oracle code 8 {} = .ok (final,events) := by
  simpa only [located,events,List.map_cons,List.map_nil] using Scalar.located_run_erases (located_run id)

theorem unit_block_path_stops (id : ThreadId) :
    Scalar.runLocated {id := id,block := .one} oracle code 8 {} = .error (.integer .blocked) := by
  rfl

theorem multiple_sites : Scalar.uniqueBarrierSites code = false := by decide

theorem typed : Scalar.ProgramTyped [("%sx",.integer .u32),("%p",.integer .pred),("%f",.floating .f32)] [] code := by decide

def trace (id : ThreadId) : Scalar.ThreadTrace := ⟨id,oracle,8,final.core,events⟩
def execution : Scalar.Candidate := ⟨[trace BarrierPublish.writer,trace BarrierPublish.reader]⟩
def launch (initial : Scalar.ByteMap) : Scalar.Launch := ⟨⟨.one,block⟩,[],initial⟩

theorem produced (id : ThreadId) : Scalar.Produced code [] (trace id) block := ⟨final.floats,actual_run id⟩
theorem complete : execution.Complete := by
  intro t ht
  simp only [execution,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl <;> rfl

theorem wellFormed (initial : Scalar.ByteMap) : Scalar.WellFormed code (launch initial) execution := by
  refine ⟨by simp [launch,block,Geometry.Valid,Dim3.Positive,Dim3.one],by decide,?_,?_⟩
  · intro t ht
    simp only [execution,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨by simp [trace,launch,block,ThreadId.Valid,Dim3.Within,BarrierPublish.writer,Dim3.zero,Dim3.one],produced _⟩
    · exact ⟨by simp [trace,launch,block,ThreadId.Valid,Dim3.Within,BarrierPublish.reader,Dim3.zero,Dim3.one],produced _⟩
  · intro id hv
    have hv' : id.Valid (BarrierPublish.launch 0 0 (fun _ => 0)).geometry := hv
    rcases BarrierPublish.valid_id_cases hv' with rfl | rfl
    · exact ⟨trace BarrierPublish.writer,by simp [execution],rfl⟩
    · exact ⟨trace BarrierPublish.reader,by simp [execution],rfl⟩

theorem trace_events {t : Scalar.ThreadTrace} (ht : t ∈ execution.traces) : t.events = events := by
  simp only [execution,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl <;> rfl

theorem source_origin {event : Event.EventId} {kind : Scalar.Kind} {bid generation : Nat}
    (he : execution.eventAt event = some kind) (hk : Event.BarrierKind bid generation kind) :
    Scalar.sourcePC execution code [] block event = some (7+2*generation) := by
  obtain ⟨t,ht,htid,hindex⟩ := Event.eventAt_trace he
  have hn : (execution.traces.map Event.ThreadTrace.id).Nodup := by decide
  have hem := trace_events ht
  have hcount : event.serial < 4 := by
    have hh := (List.getElem?_eq_some_iff.mp hindex).1
    simpa only [hem,events,List.length_cons,List.length_nil] using hh
  have hsource : Scalar.sourcePC execution code [] block event = (located[event.serial]?).map SourceRun.Located.pc := by
    unfold Scalar.sourcePC
    rw [Scalar.sourceAt_of_trace hn ht htid.symm]
    simp only [execution,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl <;> dsimp only [trace] <;> rw [located_run] <;> rfl
  rw [hsource]
  rw [hem] at hindex
  rcases (show event.serial = 0 ∨ event.serial = 1 ∨ event.serial = 2 ∨ event.serial = 3 by omega) with hs | hs | hs | hs <;>
    simp [hs,events] at hindex <;> subst kind <;> rcases hk with hk | hk <;> cases hk <;> simp [hs,located]

theorem aligned (initial : Scalar.ByteMap) : Scalar.SourceAligned code (launch initial) execution := by
  rintro a b ⟨_,bid,generation,ha,hb⟩
  exact ⟨7+2*generation,source_origin ha (.inl rfl),source_origin hb (.inr rfl)⟩

theorem wrong_unit_source : Scalar.sourcePC execution code [] .one ⟨BarrierPublish.writer,0⟩ = none := by
  unfold Scalar.sourcePC
  rw [Scalar.sourceAt_of_trace (t := trace BarrierPublish.writer) (by decide) (by simp [execution]) rfl]
  dsimp only [trace]
  rw [unit_block_path_stops]
  rfl

theorem actual_block_source : Scalar.sourcePC execution code [] block ⟨BarrierPublish.writer,0⟩ = some 7 := by
  unfold Scalar.sourcePC
  rw [Scalar.sourceAt_of_trace (t := trace BarrierPublish.writer) (by decide) (by simp [execution]) rfl]
  dsimp only [trace]
  rw [located_run]
  rfl

theorem event_shape {event : Event.EventId} {kind : Scalar.Kind} (he : execution.eventAt event = some kind) :
    (event.serial = 0 ∧ kind = .barrierArrival 0 0) ∨
    (event.serial = 1 ∧ kind = .barrierReturn 0 0) ∨
    (event.serial = 2 ∧ kind = .barrierArrival 0 1) ∨
    (event.serial = 3 ∧ kind = .barrierReturn 0 1) := by
  obtain ⟨t,ht,_,hindex⟩ := Event.eventAt_trace he
  rw [trace_events ht] at hindex
  have hb := (List.getElem?_eq_some_iff.mp hindex).1
  change event.serial < 4 at hb
  rcases (show event.serial = 0 ∨ event.serial = 1 ∨ event.serial = 2 ∨ event.serial = 3 by omega) with hs | hs | hs | hs <;>
    simp [hs,events] at hindex <;> simp [hs,hindex]

theorem return_shape {event : Event.EventId} {bid generation : Nat}
    (he : execution.eventAt event = some (.barrierReturn bid generation)) :
    bid = 0 ∧ generation ≤ 1 ∧ event.serial = 2*generation+1 := by
  rcases event_shape he with ⟨_,hk⟩ | ⟨hs,hk⟩ | ⟨_,hk⟩ | ⟨hs,hk⟩ <;> simp_all

theorem sync_rank {a b : Event.EventId} (hs : Event.BarrierSync execution a b) : a.serial < b.serial := by
  obtain ⟨_,bid,generation,ha,hb⟩ := hs
  rcases event_shape ha with ⟨ha,hka⟩ | ⟨ha,hka⟩ | ⟨ha,hka⟩ | ⟨ha,hka⟩ <;>
    rcases event_shape hb with ⟨hb,hkb⟩ | ⟨hb,hkb⟩ | ⟨hb,hkb⟩ | ⟨hb,hkb⟩ <;> simp_all

theorem arrival_index {generation : Nat} (hg : generation ≤ 1) :
    events[2*generation]? = some (.barrierArrival 0 generation) := by
  rcases (show generation = 0 ∨ generation = 1 by omega) with rfl | rfl <;> rfl

theorem barriers : Event.BarrierParticipation execution := by
  intro leave bid generation he
  obtain ⟨rfl,hg,hserial⟩ := return_shape he
  obtain ⟨t,ht,htid,_⟩ := Event.eventAt_trace he
  constructor
  · refine ⟨⟨leave.thread,2*generation⟩,rfl,by change 2*generation < leave.serial; omega,?_⟩
    rw [Event.eventAt_of_trace (id := ⟨leave.thread,2*generation⟩) (by decide) ht htid.symm,trace_events ht]
    exact arrival_index hg
  · intro peer hpeer _
    left
    rw [trace_events hpeer]
    exact List.mem_of_getElem? (arrival_index hg)

theorem no_exit {a b : Event.EventId} : ¬ Event.ExitBeforeReturn execution a b := by
  rintro ⟨_,t,ht,_,_,bid,generation,he,hx⟩
  obtain ⟨rfl,hg,_⟩ := return_shape he
  have hlast : Event.Kind.barrierArrival 0 1 ∈ t.events := by rw [trace_events ht]; simp [events]
  have hh := hx.2 1 hlast
  omega

theorem no_memory (event : Event.EventId) (loc : Location) :
    execution.readByte event loc = none ∧ execution.writeByte event loc = none := by
  cases he : execution.eventAt event with
  | none => simp [Event.Candidate.readByte,Event.Candidate.writeByte,he]
  | some kind =>
    rcases event_shape he with ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
      simp [Event.Candidate.readByte,Event.Candidate.writeByte,he,Event.Kind.readByte,Event.Kind.writeByte]

theorem memory (initial : Scalar.ByteMap) : Event.GenericMemoryConditions execution initial
    (fun _ _ => .initial) (Event.InitialCo execution) := by
  apply Event.initial_co_conditions (fun event => event.serial)
  · intro a b hp; exact hp.2.2.2
  · intro a b hs; exact sync_rank hs
  · intro a b he; exact (no_exit he).elim
  · exact barriers
  · intro loc a b va vb ha _
    rw [(no_memory a loc).2] at ha
    cases ha
  · intro read loc value hr
    rw [(no_memory read loc).1] at hr
    cases hr
  · intro read writer loc vr vw hr _ _
    rw [(no_memory read loc).1] at hr
    cases hr
  · intro read writer loc vr vw hr _ _
    rw [(no_memory read loc).1] at hr
    cases hr

theorem checked (initial : Scalar.ByteMap) : Scalar.CheckedConditions code (launch initial) execution
    (fun _ _ => .initial) (Event.InitialCo execution) := ⟨wellFormed initial,aligned initial,memory initial⟩

theorem observer (initial : Scalar.ByteMap) (domain : List Location)
    (hglobal : ∀ loc ∈ domain, loc.space = .global) : Event.ObserverConditions execution initial
    (fun _ _ => .initial) (Event.InitialCo execution) ⟨domain,initial,fun _ => .initial⟩ := by
  refine ⟨complete,hglobal,?_,?_⟩
  · intro loc _ _; rfl
  · intro loc _ _ writer value hw
    rw [(no_memory writer loc).2] at hw
    cases hw

theorem accepted (initial : Scalar.ByteMap) (domain : List Location)
    (hglobal : ∀ loc ∈ domain, loc.space = .global) :
    ∃ c rf co o, Scalar.CheckedConditions code (launch initial) c rf co ∧
      Event.ObserverConditions c initial rf co o ∧ o.domain = domain ∧ o.output = initial :=
  ⟨execution,(fun _ _ => .initial),Event.InitialCo execution,⟨domain,initial,fun _ => .initial⟩,
    checked initial,observer initial domain hglobal,rfl,rfl⟩

def embedTrace (t : Event.ThreadTrace) : Scalar.ThreadTrace :=
  ⟨t.id,Scalar.embedOracle t.oracle,t.count,t.final,t.events.map Scalar.liftKind⟩
def badCode : List Scalar.Instr := SourceOriginsTests.badCode.map Scalar.Instr.integer
def bad : Scalar.Candidate := ⟨[embedTrace SourceOriginsTests.badWriter,embedTrace SourceOriginsTests.badReader]⟩

theorem bad_writer_produced : Scalar.Produced badCode SourceOriginsTests.badParams (embedTrace SourceOriginsTests.badWriter) block := by
  exact ⟨[],by rfl⟩
theorem bad_reader_produced : Scalar.Produced badCode SourceOriginsTests.badParams (embedTrace SourceOriginsTests.badReader) block := by
  exact ⟨[],by rfl⟩
theorem bad_complete : bad.Complete := by
  intro t ht
  simp only [bad,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl <;> rfl
theorem bad_wellFormed (initial : Scalar.ByteMap) :
    Scalar.WellFormed badCode ⟨⟨.one,block⟩,SourceOriginsTests.badParams,initial⟩ bad := by
  refine ⟨by simp [block,Geometry.Valid,Dim3.Positive,Dim3.one],by decide,?_,?_⟩
  · intro t ht
    simp only [bad,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨by change BarrierPublish.writer.Valid ⟨.one,block⟩; simp [block,ThreadId.Valid,Dim3.Within,BarrierPublish.writer,Dim3.zero,Dim3.one],bad_writer_produced⟩
    · exact ⟨by change BarrierPublish.reader.Valid ⟨.one,block⟩; simp [block,ThreadId.Valid,Dim3.Within,BarrierPublish.reader,Dim3.zero,Dim3.one],bad_reader_produced⟩
  · intro id hv
    have hv' : id.Valid (BarrierPublish.launch 0 0 (fun _ => 0)).geometry := hv
    rcases BarrierPublish.valid_id_cases hv' with rfl | rfl
    · exact ⟨embedTrace SourceOriginsTests.badWriter,by simp [bad],rfl⟩
    · exact ⟨embedTrace SourceOriginsTests.badReader,by simp [bad],rfl⟩
theorem bad_sync : Event.BarrierSync bad BarrierPublish.wa BarrierPublish.rr := ⟨rfl,0,0,by rfl,by rfl⟩
theorem bad_writer_source : Scalar.sourcePC bad badCode SourceOriginsTests.badParams block BarrierPublish.wa = some 9 := by rfl
theorem bad_reader_source : Scalar.sourcePC bad badCode SourceOriginsTests.badParams block BarrierPublish.rr = some 5 := by rfl
theorem bad_not_aligned (initial : Scalar.ByteMap) :
    ¬ Scalar.SourceAligned badCode ⟨⟨.one,block⟩,SourceOriginsTests.badParams,initial⟩ bad := by
  intro h
  obtain ⟨pc,hw,hr⟩ := h _ _ bad_sync
  rw [bad_writer_source] at hw
  rw [bad_reader_source] at hr
  have h9 := Option.some.inj hw
  have h5 := Option.some.inj hr
  omega
theorem bad_checked_rejected (initial : Scalar.ByteMap) (rf : Event.ReadsFrom) (co : Event.Coherence) :
    ¬ Scalar.CheckedConditions badCode ⟨⟨.one,block⟩,SourceOriginsTests.badParams,initial⟩ bad rf co := by
  intro h
  exact bad_not_aligned initial h.barrierSources

end
end Ptx.ScalarSourceOriginsTests
