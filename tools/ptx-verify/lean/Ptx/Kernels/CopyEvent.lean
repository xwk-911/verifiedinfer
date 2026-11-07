import Ptx.Kernels.Copy
import Ptx.Event.Trace
import Ptx.Event.Consistency

/-! Trace reconstruction for the actual Copy AST with the original configuration
family: arbitrary array length, launch count, layout and data. This is the thread
part of the operational/event bridge, not yet an output-refinement theorem. -/
namespace Ptx.CopyEvent
open Ptx.ISA Ptx.Event
abbrev code := CopyContract.code

def id (tid : Nat) : ThreadId := ⟨.zero, ⟨tid, 0, 0⟩⟩
def context (tid : Nat) (parameters : Bindings) : Context := ⟨id tid, parameters⟩
def payload (answer : Nat) := encodeU32 (wrap 32 answer)
def events (c : CopyContract.Config) (tid answer : Nat) : List Kind := [
  .read ⟨.global, 4*(c.src+tid)⟩ (payload answer),
  .write ⟨.global, 4*(c.dst+tid)⟩ (payload answer)]

def activeFinal (c : CopyContract.Config) (tid answer : Nat) : State := {
  thread := { pc := 11, status := .done, regs := [("%r2", wrap 32 answer),
    ("%rd4", 4*(c.dst+tid)), ("%rd3", 4*(c.src+tid)), ("%rd2", 4*tid),
    ("%p", 0), ("%r1", tid), ("%r0", c.n), ("%rd1", 4*c.dst), ("%rd0", 4*c.src)] }
  queries := 1
}
def maskedFinal (c : CopyContract.Config) (tid : Nat) : State := {
  thread := { pc := 11, status := .done, regs := [("%p", 1), ("%r1", tid),
    ("%r0", c.n), ("%rd1", 4*c.dst), ("%rd0", 4*c.src)] }
}

theorem run_active (c : CopyContract.Config) (tid : Nat) (oracle : Oracle) (parameters : Bindings)
    (ht : tid < c.count) (hp : CopyContract.Params c parameters) (ha : tid < c.n) :
    Event.run (context tid parameters) oracle code 12 {} =
      .ok (activeFinal c tid (oracle 0), events c tid (oracle 0)) := by
  obtain ⟨hsrc, hdst, hn⟩ := hp
  have ht32 := CopyContract.tid32 c ht
  have hn32 := CopyContract.n32 c
  have hs64 := CopyContract.src64 c
  have hd64 := CopyContract.dst64 c
  have ho64 := CopyContract.offset64 c ht
  have hsaddr := CopyContract.srcAddr64 c ha
  have hdaddr := CopyContract.dstAddr64 c ha
  have hwide : wrap 64 (tid*4) = 4*tid := by rw [Nat.mul_comm tid 4]; exact ho64
  have hsumSrc : wrap 64 (4*c.src + 4*tid) = 4*(c.src+tid) := by
    simpa only [Nat.mul_add] using hsaddr
  have hsumDst : wrap 64 (4*c.dst + 4*tid) = 4*(c.dst+tid) := by
    simpa only [Nat.mul_add] using hdaddr
  simp only [wrap] at ht32 hn32 hs64 hd64 ho64 hsaddr hdaddr hwide hsumSrc hsumDst
  simp [code, CopyContract.code, Generated.copy.program, context, id, Dim3.zero,
    activeFinal, events, payload, Event.run, Event.step, localStep, eval, evalAddr,
    assign, advance, put, lookup, Location.resolve, hsrc, hdst, hn, ht32, hn32,
    hs64, hd64, ho64, hsaddr, hdaddr, hwide, hsumSrc, hsumDst, Nat.not_le.mpr ha,
    bind, Except.bind, pure, Except.pure, wrap]

theorem run_masked (c : CopyContract.Config) (tid : Nat) (oracle : Oracle) (parameters : Bindings)
    (ht : tid < c.count) (hp : CopyContract.Params c parameters) (ha : c.n ≤ tid) :
    Event.run (context tid parameters) oracle code 7 {} = .ok (maskedFinal c tid, []) := by
  obtain ⟨hsrc, hdst, hn⟩ := hp
  have ht32 := CopyContract.tid32 c ht
  have hn32 := CopyContract.n32 c
  have hs64 := CopyContract.src64 c
  have hd64 := CopyContract.dst64 c
  simp only [wrap] at ht32 hn32 hs64 hd64
  simp [code, CopyContract.code, Generated.copy.program, context, id, Dim3.zero,
    maskedFinal, Event.run, Event.step, localStep, eval, assign, advance, put, lookup,
    hsrc, hdst, hn, ht32, hn32, hs64, hd64, ha, bind, Except.bind, pure, Except.pure, wrap]

theorem active_trace_shape (c : CopyContract.Config) {tid : Nat} {t : ThreadTrace} {parameters}
    (ht : tid < c.count) (hp : CopyContract.Params c parameters) (ha : tid < c.n)
    (hid : t.id = id tid) (hr : t.Produced code parameters) (hd : t.final.thread.status = .done) :
    t.count = 12 ∧ t.final = activeFinal c tid (t.oracle 0) ∧ t.events = events c tid (t.oracle 0) := by
  have he : Event.run (context tid parameters) t.oracle code t.count {} = .ok (t.final, t.events) := by
    simpa only [ThreadTrace.Produced, hid, context] using hr
  exact complete_run_unique he hd (run_active c tid t.oracle parameters ht hp ha) rfl

theorem masked_trace_shape (c : CopyContract.Config) {tid : Nat} {t : ThreadTrace} {parameters}
    (ht : tid < c.count) (hp : CopyContract.Params c parameters) (ha : c.n ≤ tid)
    (hid : t.id = id tid) (hr : t.Produced code parameters) (hd : t.final.thread.status = .done) :
    t.count = 7 ∧ t.final = maskedFinal c tid ∧ t.events = [] := by
  have he : Event.run (context tid parameters) t.oracle code t.count {} = .ok (t.final, t.events) := by
    simpa only [ThreadTrace.Produced, hid, context] using hr
  exact complete_run_unique he hd (run_masked c tid t.oracle parameters ht hp ha) rfl

def geometry (c : CopyContract.Config) : Geometry := ⟨.one, ⟨c.count, 1, 1⟩⟩

theorem valid_id (c : CopyContract.Config) {thread : ThreadId} (h : thread.Valid (geometry c)) :
    ∃ tid, tid < c.count ∧ thread = id tid := by
  rcases thread with ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩
  simp only [ThreadId.Valid, Dim3.Within, geometry, Dim3.one] at h
  have hs : cx = 0 ∧ cy = 0 ∧ cz = 0 ∧ ty = 0 ∧ tz = 0 ∧ tx < c.count := by omega
  rcases hs with ⟨rfl,rfl,rfl,rfl,rfl,ht⟩
  exact ⟨tx,ht,rfl⟩

theorem event_shape (c : CopyContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry c) (hp : CopyContract.Params c l.params)
    {event : EventId} {kind : Kind} (he : execution.eventAt event = some kind) :
    ∃ tid answer, tid < c.n ∧
      ((event = ⟨id tid,0⟩ ∧ kind = .read ⟨.global,4*(c.src+tid)⟩ (payload answer)) ∨
       (event = ⟨id tid,1⟩ ∧ kind = .write ⟨.global,4*(c.dst+tid)⟩ (payload answer))) := by
  obtain ⟨t,ht,htid,hindex⟩ := eventAt_trace he
  have hvalid : t.id.Valid (geometry c) := by simpa only [hg] using (hw.2.2.1 t ht).1
  obtain ⟨tid,htcount,hid⟩ := valid_id c hvalid
  by_cases ha : tid < c.n
  · have hs := active_trace_shape c htcount hp ha hid (hw.2.2.1 t ht).2 (hd t ht)
    rw [hs.2.2] at hindex
    have hbound := (List.getElem?_eq_some_iff.mp hindex).1
    rcases event with ⟨thread,serial⟩
    have hthread : thread = id tid := htid.symm.trans hid
    subst thread
    have hserial : serial = 0 ∨ serial = 1 := by simp [events] at hbound; omega
    refine ⟨tid,t.oracle 0,ha,?_⟩
    rcases hserial with rfl | rfl
    · exact .inl ⟨rfl, by simpa [events] using hindex.symm⟩
    · exact .inr ⟨rfl, by simpa [events] using hindex.symm⟩
  · have hs := masked_trace_shape c htcount hp (Nat.le_of_not_lt ha) hid (hw.2.2.1 t ht).2 (hd t ht)
    rw [hs.2.2] at hindex
    simp at hindex

theorem read_shape (c : CopyContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry c) (hp : CopyContract.Params c l.params)
    {event : EventId} {address : Location} {value : Byte}
    (hr : execution.readByte event address = some value) :
    ∃ tid answer, tid < c.n ∧ event = ⟨id tid,0⟩ ∧
      payloadByte ⟨.global,4*(c.src+tid)⟩ (payload answer) address = some value := by
  cases he : execution.eventAt event with
  | none => simp [Candidate.readByte,he] at hr
  | some kind =>
    obtain ⟨tid,answer,ht,hcase⟩ := event_shape c hw hd hg hp he
    rcases hcase with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨tid,answer,ht,rfl,by simpa [Candidate.readByte,he,Kind.readByte] using hr⟩
    · simp [Candidate.readByte,he,Kind.readByte] at hr

theorem write_shape (c : CopyContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry c) (hp : CopyContract.Params c l.params)
    {event : EventId} {address : Location} {value : Byte}
    (hr : execution.writeByte event address = some value) :
    ∃ tid answer, tid < c.n ∧ event = ⟨id tid,1⟩ ∧
      payloadByte ⟨.global,4*(c.dst+tid)⟩ (payload answer) address = some value := by
  cases he : execution.eventAt event with
  | none => simp [Candidate.writeByte,he] at hr
  | some kind =>
    obtain ⟨tid,answer,ht,hcase⟩ := event_shape c hw hd hg hp he
    rcases hcase with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simp [Candidate.writeByte,he,Kind.writeByte] at hr
    · exact ⟨tid,answer,ht,rfl,by simpa [Candidate.writeByte,he,Kind.writeByte] using hr⟩

theorem no_rmw (c : CopyContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry c) (hp : CopyContract.Params c l.params) (event : EventId) :
    ¬ execution.IsRMW event := by
  rintro ⟨scope,base,bytes,he⟩
  obtain ⟨_,_,_,hs⟩ := event_shape c hw hd hg hp he
  rcases hs with ⟨_,hk⟩ | ⟨_,hk⟩ <;> cases hk

theorem no_races (c : CopyContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry c) (hp : CopyContract.Params c l.params)
    (sources : ReadsFrom) (a b : EventId) : ¬ DataRace execution sources a b := by
  intro hrace
  obtain ⟨address,ha,hb⟩ := hrace.overlap
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · obtain ⟨va,hva⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨vb,hvb⟩ := Option.isSome_iff_exists.mp hb
    rcases hrace.conflict with ⟨other,v,hv⟩ | ⟨other,v,hv⟩
    · exact read_write_exclusive (no_rmw c hw hd hg hp a) hva hv
    · exact read_write_exclusive (no_rmw c hw hd hg hp b) hvb hv
  · obtain ⟨va,hva⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨vb,hvb⟩ := Option.isSome_iff_exists.mp hb
    obtain ⟨i,_,hi,_,hread⟩ := read_shape c hw hd hg hp hva
    obtain ⟨j,_,hj,_,hwrite⟩ := write_shape c hw hd hg hp hvb
    have hreadBounds := payloadByte_bounds hread
    have hwriteBounds := payloadByte_bounds hwrite
    simp only [payload,encodeU32_length] at hreadBounds hwriteBounds
    have hdisjoint := c.disjoint
    omega
  · obtain ⟨va,hva⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨vb,hvb⟩ := Option.isSome_iff_exists.mp hb
    obtain ⟨i,_,hi,_,hwrite⟩ := write_shape c hw hd hg hp hva
    obtain ⟨j,_,hj,_,hread⟩ := read_shape c hw hd hg hp hvb
    have hreadBounds := payloadByte_bounds hread
    have hwriteBounds := payloadByte_bounds hwrite
    simp only [payload,encodeU32_length] at hreadBounds hwriteBounds
    have hdisjoint := c.disjoint
    omega
  · obtain ⟨va,hva⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨vb,hvb⟩ := Option.isSome_iff_exists.mp hb
    obtain ⟨i,ansA,hi,haId,hwriteA⟩ := write_shape c hw hd hg hp hva
    obtain ⟨j,ansB,hj,hbId,hwriteB⟩ := write_shape c hw hd hg hp hvb
    have hboundsA := payloadByte_bounds hwriteA
    have hboundsB := payloadByte_bounds hwriteB
    simp only [payload,encodeU32_length] at hboundsA hboundsB
    have heq : i = j := by omega
    subst j
    have hab : a = b := haId.trans hbId.symm
    cases hab
    apply hrace.notStrong
    refine ⟨Or.inl rfl, (⟨.global,4*(c.dst+i)⟩,4), ?_, ?_⟩
    all_goals
      cases he : execution.eventAt a with
      | none => simp [Candidate.writeByte,he] at hva
      | some kind =>
        obtain ⟨tid,answer,ht,hcase⟩ := event_shape c hw hd hg hp he
        rcases hcase with ⟨hid,hkind⟩ | ⟨hid,hkind⟩
        · simp [Candidate.writeByte,he,hkind,Kind.writeByte] at hva
        · have htid : tid = i := by
            have hh := (congrArg EventId.thread (hid.symm.trans haId))
            exact congrArg (fun thread => thread.tid.x) hh
          subst tid
          simp [hkind,Kind.footprint,payload]

end Ptx.CopyEvent
