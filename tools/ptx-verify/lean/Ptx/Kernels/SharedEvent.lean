import Ptx.Kernels.SharedSwap
import Ptx.Kernels.CopyEventOutput

/-! Events of the actual translated SharedSwap program with its ORIGINAL
two-thread configuration, arbitrary data/layout and flexible parameter bindings.
The two load-oracle answers remain independent until memory consistency is used.
-/
namespace Ptx.SharedEvent
open Ptx.ISA Ptx.Event
abbrev code := SharedContract.code
abbrev id := CopyEvent.id
abbrev payload := CopyEvent.payload
abbrev wordByte := CopyEvent.wordByte
def geometry : Geometry := ⟨.one,⟨2,1,1⟩⟩
def srcLoc (c : SharedContract.Config) (tid : Nat) := CopyEvent.srcLoc c.toConfig tid
def dstLoc (c : SharedContract.Config) (tid : Nat) := CopyEvent.dstLoc c.toConfig tid
def sharedLoc (tid : Nat) : Location := ⟨.shared .zero,4*tid⟩

def events (c : SharedContract.Config) (tid first second : Nat) : List Kind := [
  .read (srcLoc c tid) (payload first), .write (sharedLoc tid) (payload first),
  .barrierArrival 0 0, .barrierReturn 0 0,
  .read (sharedLoc (SharedContract.other tid)) (payload second),
  .write (dstLoc c tid) (payload second)]

def finalState (c : SharedContract.Config) (tid first second : Nat) : State := {
  thread := {pc := 16,status := .done,regs := [
    ("%r3",wrap 32 second),("%rd7",4*SharedContract.other tid),
    ("%rd2",4*SharedContract.other tid),("%r2",SharedContract.other tid),
    ("%r1",wrap 32 first),("%rd6",4*tid),("%rd5",0),
    ("%rd4",4*(c.dst+tid)),("%rd3",4*(c.src+tid)),("%r0",tid),
    ("%rd1",4*c.dst),("%rd0",4*c.src)]}
  queries := 2
  generations := [(0,1)]
}

theorem run_thread (c : SharedContract.Config) (tid : Nat) (oracle : Oracle) (parameters : Bindings)
    (ht : tid < 2) (hp : SharedContract.Params c parameters) :
    Event.run ⟨id tid,parameters⟩ oracle code 17 {} =
      .ok (finalState c tid (oracle 0) (oracle 1),events c tid (oracle 0) (oracle 1)) := by
  obtain ⟨hsrc,hdst⟩ := hp
  have hn : tid < c.toConfig.n := by rw [c.n_two]; exact ht
  have hs := CopyContract.src64 c.toConfig
  have hd := CopyContract.dst64 c.toConfig
  have hsa : wrap 64 (4*c.src+4*tid) = 4*(c.src+tid) := by
    simpa only [Nat.mul_add] using CopyContract.srcAddr64 c.toConfig hn
  have hda : wrap 64 (4*c.dst+4*tid) = 4*(c.dst+tid) := by
    simpa only [Nat.mul_add] using CopyContract.dstAddr64 c.toConfig hn
  have htid : tid = 0 ∨ tid = 1 := by omega
  rcases htid with rfl | rfl
  all_goals
    simp only [wrap] at hs hd hsa hda
    simp [code,SharedContract.code,Generated.shared_swap.program,finalState,events,
      srcLoc,dstLoc,CopyEvent.srcLoc,CopyEvent.dstLoc,sharedLoc,id,CopyEvent.id,
      SharedContract.other,payload,CopyEvent.payload,Event.run,Event.step,Event.generation,
      localStep,eval,evalAddr,assign,advance,put,lookup,Location.resolve,Dim3.zero,
      hs,hd,hsa,hda,hsrc,hdst,bind,Except.bind,pure,Except.pure,wrap]
  all_goals
    constructor <;> (have hsc := c.src64; have hdc := c.dst64; have hnc := c.n_two; omega)

theorem trace_shape (c : SharedContract.Config) {tid : Nat} {t : ThreadTrace} {parameters}
    (ht : tid < 2) (hp : SharedContract.Params c parameters) (hid : t.id = id tid)
    (hr : t.Produced code parameters) (hd : t.final.thread.status = .done) :
    t.count = 17 ∧ t.final = finalState c tid (t.oracle 0) (t.oracle 1) ∧
      t.events = events c tid (t.oracle 0) (t.oracle 1) := by
  have he : Event.run ⟨id tid,parameters⟩ t.oracle code t.count {} = .ok (t.final,t.events) := by
    simpa only [ThreadTrace.Produced,hid] using hr
  exact complete_run_unique he hd (run_thread c tid t.oracle parameters ht hp) rfl

theorem valid_id {thread : ThreadId} (h : thread.Valid geometry) :
    ∃ tid, tid < 2 ∧ thread = id tid := by
  rcases thread with ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩
  simp only [ThreadId.Valid,Dim3.Within,geometry,Dim3.one] at h
  have hs : cx = 0 ∧ cy = 0 ∧ cz = 0 ∧ ty = 0 ∧ tz = 0 ∧ tx < 2 := by omega
  rcases hs with ⟨rfl,rfl,rfl,rfl,rfl,ht⟩
  exact ⟨tx,ht,rfl⟩

theorem events_present (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    (tid : Nat) (ht : tid < 2) :
    ∃ first second, ∀ serial, execution.eventAt ⟨id tid,serial⟩ = (events c tid first second)[serial]? := by
  have hv : (id tid).Valid l.geometry := by
    rw [hg]
    simp [ThreadId.Valid,Dim3.Within,geometry,id,CopyEvent.id,Dim3.zero,Dim3.one,ht]
  obtain ⟨t,hm,hid⟩ := hw.2.2.2 (id tid) hv
  have hs := trace_shape c ht hp hid (hw.2.2.1 t hm).2 (hd t hm)
  exact ⟨t.oracle 0,t.oracle 1,fun serial => by
    rw [eventAt_of_trace hw.2.1 hm hid.symm,hs.2.2]⟩

theorem event_shape (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    {event : EventId} {kind : Kind} (he : execution.eventAt event = some kind) :
    ∃ tid first second, tid < 2 ∧ event.thread = id tid ∧
      (events c tid first second)[event.serial]? = some kind := by
  obtain ⟨t,hm,htid,hindex⟩ := eventAt_trace he
  have hv : t.id.Valid geometry := by simpa only [hg] using (hw.2.2.1 t hm).1
  obtain ⟨tid,ht,hid⟩ := valid_id hv
  have hs := trace_shape c ht hp hid (hw.2.2.1 t hm).2 (hd t hm)
  exact ⟨tid,t.oracle 0,t.oracle 1,ht,htid.symm.trans hid,by simpa only [hs.2.2] using hindex⟩

theorem read_shape (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    {event : EventId} {loc : Location} {value : Byte} (hr : execution.readByte event loc = some value) :
    ∃ tid answer, tid < 2 ∧
      ((event = ⟨id tid,0⟩ ∧ payloadByte (srcLoc c tid) (payload answer) loc = some value) ∨
       (event = ⟨id tid,4⟩ ∧ payloadByte (sharedLoc (SharedContract.other tid)) (payload answer) loc = some value)) := by
  cases he : execution.eventAt event with
  | none => simp [Candidate.readByte,he] at hr
  | some kind =>
    obtain ⟨tid,first,second,ht,hid,hindex⟩ := event_shape c hw hd hg hp he
    have hb := (List.getElem?_eq_some_iff.mp hindex).1
    have hs : event.serial = 0 ∨ event.serial = 1 ∨ event.serial = 2 ∨ event.serial = 3 ∨
        event.serial = 4 ∨ event.serial = 5 := by simp [events] at hb; omega
    rcases event with ⟨thread,serial⟩
    simp only at hid hs hindex
    subst thread
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [events,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq] at hindex <;>
      subst kind <;> simp [Candidate.readByte,he,Kind.readByte] at hr
    · exact ⟨tid,first,ht,Or.inl ⟨rfl,hr⟩⟩
    · exact ⟨tid,second,ht,Or.inr ⟨rfl,hr⟩⟩

theorem write_shape (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    {event : EventId} {loc : Location} {value : Byte} (hr : execution.writeByte event loc = some value) :
    ∃ tid answer, tid < 2 ∧
      ((event = ⟨id tid,1⟩ ∧ payloadByte (sharedLoc tid) (payload answer) loc = some value) ∨
       (event = ⟨id tid,5⟩ ∧ payloadByte (dstLoc c tid) (payload answer) loc = some value)) := by
  cases he : execution.eventAt event with
  | none => simp [Candidate.writeByte,he] at hr
  | some kind =>
    obtain ⟨tid,first,second,ht,hid,hindex⟩ := event_shape c hw hd hg hp he
    have hb := (List.getElem?_eq_some_iff.mp hindex).1
    have hs : event.serial = 0 ∨ event.serial = 1 ∨ event.serial = 2 ∨ event.serial = 3 ∨
        event.serial = 4 ∨ event.serial = 5 := by simp [events] at hb; omega
    rcases event with ⟨thread,serial⟩
    simp only at hid hs hindex
    subst thread
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [events,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq] at hindex <;>
      subst kind <;> simp [Candidate.writeByte,he,Kind.writeByte] at hr
    · exact ⟨tid,first,ht,Or.inl ⟨rfl,hr⟩⟩
    · exact ⟨tid,second,ht,Or.inr ⟨rfl,hr⟩⟩

end Ptx.SharedEvent
