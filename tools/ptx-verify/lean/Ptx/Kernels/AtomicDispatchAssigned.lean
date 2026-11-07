import Ptx.Kernels.AtomicDispatchTickets

/-! A derived assignment of the two actual traces to jobs, rather than an
assignment assumed by the launch precondition. All four events are retained. -/
namespace Ptx.AtomicDispatchEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.AtomicDispatchTrace
noncomputable section

structure Assignment (execution : Scalar.Candidate) where
  first : Scalar.ThreadTrace
  second : Scalar.ThreadTrace
  firstMember : first ∈ execution.traces
  secondMember : second ∈ execution.traces
  covers : ∀ t ∈ execution.traces, t = first ∨ t = second
  firstTicket : ticket first.oracle = 0
  secondTicket : ticket second.oracle = 1

theorem assignment (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate} {rf co}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Pre cfg launch) (hm : GenericMemoryConditions execution launch.initial rf co) : Nonempty (Assignment execution) := by
  obtain ⟨t0,h0,hid0⟩ := hw.2.2.2 (id 0) (by rw [hp.1]; exact id_valid (by decide))
  obtain ⟨t1,h1,hid1⟩ := hw.2.2.2 (id 1) (by rw [hp.1]; exact id_valid (by decide))
  have hcover : ∀ t ∈ execution.traces, t = t0 ∨ t = t1 := by
    intro t ht
    have hv : t.id.Valid geometry := by simpa only [hp.1] using (hw.2.2.1 t ht).1
    obtain ⟨cta,hcta,hid⟩ := valid_id hv
    have hc : cta = 0 ∨ cta = 1 := by omega
    rcases hc with rfl | rfl
    · exact Or.inl (unique_trace_id hw.2.1 ht h0 (hid.trans hid0.symm))
    · exact Or.inr (unique_trace_id hw.2.1 ht h1 (hid.trans hid1.symm))
  rcases tickets cfg hw hd hp.1 hp.2.1 hp.2.2 hm h0 h1 hid0 hid1 with ⟨hz,ho⟩ | ⟨ho,hz⟩
  · exact ⟨⟨t0,t1,h0,h1,hcover,hz,ho⟩⟩
  · exact ⟨⟨t1,t0,h1,h0,fun t ht => (hcover t ht).symm,hz,ho⟩⟩

def firstCounter {execution} (jobs : Assignment execution) : EventId := ⟨jobs.first.id,0⟩
def secondCounter {execution} (jobs : Assignment execution) : EventId := ⟨jobs.second.id,0⟩
def firstJob {execution} (jobs : Assignment execution) : EventId := ⟨jobs.first.id,1⟩
def secondJob {execution} (jobs : Assignment execution) : EventId := ⟨jobs.second.id,1⟩

theorem assigned_ids_ne {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (jobs : Assignment execution) : jobs.first.id ≠ jobs.second.id := by
  intro he
  have ht := unique_trace_id hw.2.1 jobs.firstMember jobs.secondMember he
  have hz := jobs.firstTicket
  rw [ht,jobs.secondTicket] at hz
  omega

theorem assigned_trace_events (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Params cfg.counter cfg.x cfg.y launch.params) (jobs : Assignment execution) :
    jobs.first.events = [.rmw .gpu (counterLoc cfg) (atomicAddBytes (reply jobs.first.oracle) 1),.write (xLoc cfg) (u32Bytes 1)] ∧
    jobs.second.events = [.rmw .gpu (counterLoc cfg) (atomicAddBytes (reply jobs.second.oracle) 1),.write (yLoc cfg) (u32Bytes 2)] := by
  have hz : wrap 32 (reply jobs.first.oracle) = 0 := jobs.firstTicket
  have ho : wrap 32 (reply jobs.second.oracle) = 1 := jobs.secondTicket
  constructor
  · simpa [eventsFor,events,outputEvents,hz,counterLoc,xLoc,u32Bytes] using (trace_shape cfg hw hd hp jobs.firstMember).2.2
  · simpa [eventsFor,events,outputEvents,ho,counterLoc,yLoc,u32Bytes] using (trace_shape cfg hw hd hp jobs.secondMember).2.2

theorem assigned_x_event (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Params cfg.counter cfg.x cfg.y launch.params) (jobs : Assignment execution) :
    execution.eventAt (firstJob jobs) = some (.write (xLoc cfg) (u32Bytes 1)) := by
  rw [eventAt_of_trace hw.2.1 jobs.firstMember rfl,(assigned_trace_events cfg hw hd hp jobs).1]
  rfl

theorem assigned_y_event (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Params cfg.counter cfg.x cfg.y launch.params) (jobs : Assignment execution) :
    execution.eventAt (secondJob jobs) = some (.write (yLoc cfg) (u32Bytes 2)) := by
  rw [eventAt_of_trace hw.2.1 jobs.secondMember rfl,(assigned_trace_events cfg hw hd hp jobs).2]
  rfl

theorem assigned_inventory (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Params cfg.counter cfg.x cfg.y launch.params) (jobs : Assignment execution)
    {e : EventId} (he : execution.Present e) :
    e = firstCounter jobs ∨ e = firstJob jobs ∨ e = secondCounter jobs ∨ e = secondJob jobs := by
  cases hkind : execution.eventAt e with
  | none => simp [Candidate.Present,hkind] at he
  | some kind =>
    obtain ⟨t,ht,htid,hindex⟩ := eventAt_trace hkind
    have hb := (List.getElem?_eq_some_iff.mp hindex).1
    rcases jobs.covers t ht with rfl | rfl
    · rw [(assigned_trace_events cfg hw hd hp jobs).1] at hb
      have hserial : e.serial = 0 ∨ e.serial = 1 := by simp only [List.length_cons,List.length_nil] at hb; omega
      have hthread : e.thread = jobs.first.id := htid.symm
      rcases hserial with hs | hs
      · exact Or.inl (by cases e; simp_all [firstCounter])
      · exact Or.inr (Or.inl (by cases e; simp_all [firstJob]))
    · rw [(assigned_trace_events cfg hw hd hp jobs).2] at hb
      have hserial : e.serial = 0 ∨ e.serial = 1 := by simp only [List.length_cons,List.length_nil] at hb; omega
      have hthread : e.thread = jobs.second.id := htid.symm
      rcases hserial with hs | hs
      · exact Or.inr (Or.inr (Or.inl (by cases e; simp_all [secondCounter])))
      · exact Or.inr (Or.inr (Or.inr (by cases e; simp_all [secondJob])))

theorem assigned_footprints (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Params cfg.counter cfg.x cfg.y launch.params) (jobs : Assignment execution) :
    (execution.eventAt (firstCounter jobs)).bind Kind.footprint = some (counterLoc cfg,4) ∧
    (execution.eventAt (firstJob jobs)).bind Kind.footprint = some (xLoc cfg,4) ∧
    (execution.eventAt (secondCounter jobs)).bind Kind.footprint = some (counterLoc cfg,4) ∧
    (execution.eventAt (secondJob jobs)).bind Kind.footprint = some (yLoc cfg,4) := by
  simp [firstCounter,secondCounter,counter_event cfg hw hd hp jobs.firstMember,counter_event cfg hw hd hp jobs.secondMember,
    assigned_x_event cfg hw hd hp jobs,assigned_y_event cfg hw hd hp jobs,Kind.footprint,atomicAddBytes,u32Bytes]

theorem counter_writer_pair (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params) (jobs : Assignment execution)
    {writer loc value} (hl : InWords cfg.counter 1 loc) (hwrite : execution.writeByte writer loc = some value) :
    writer = firstCounter jobs ∨ writer = secondCounter jobs := by
  obtain ⟨v,hserial,he⟩ := counter_access cfg hw hd hg hp hl (Or.inr (by rw [hwrite]; rfl))
  obtain ⟨t,ht,hid,_⟩ := eventAt_trace he
  rcases jobs.covers t ht with rfl | rfl
  · exact Or.inl (by cases writer; simp_all [firstCounter])
  · exact Or.inr (by cases writer; simp_all [secondCounter])

end
end Ptx.AtomicDispatchEvent
