import Ptx.Kernels.AtomicDispatchConfig

/-! Every event of every complete provenance-checked candidate comes from the
actual source branch. Oracles, counts and trace ordering remain unrestricted. -/
namespace Ptx.AtomicDispatchEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.AtomicDispatchTrace
noncomputable section

theorem trace_shape (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Params cfg.counter cfg.x cfg.y launch.params) (ht : t ∈ execution.traces) :
    t.oracle 0 = .integer (reply t.oracle) ∧ t.count = sourceCount (reply t.oracle) ∧ t.events = eventsFor cfg t.oracle := by
  obtain ⟨floats,hr⟩ := (hw.2.2.1 t ht).2
  obtain ⟨value,ho,hcount,_,hevents⟩ := completed_source_shape
    {id := t.id,params := launch.params,block := launch.geometry.block} t.oracle cfg.counter cfg.x cfg.y hp
    (by have := cfg.counterEnd; omega) (by have := cfg.xEnd; omega) (by have := cfg.yEnd; omega) hr (hd t ht)
  have he := reply_typed ho
  exact ⟨by simpa [he] using ho,by simpa [he] using hcount,by simpa [eventsFor,he] using hevents⟩

theorem counter_event (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Params cfg.counter cfg.x cfg.y launch.params) (ht : t ∈ execution.traces) :
    execution.eventAt ⟨t.id,0⟩ = some (.rmw .gpu (counterLoc cfg) (atomicAddBytes (reply t.oracle) 1)) := by
  rw [eventAt_of_trace hw.2.1 ht rfl,(trace_shape cfg hw hd hp ht).2.2]
  rfl

theorem counter_read_byte (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Params cfg.counter cfg.x cfg.y launch.params) (ht : t ∈ execution.traces)
    {offset : Nat} (ho : offset < 4) :
    execution.readByte ⟨t.id,0⟩ ((counterLoc cfg).add offset) = some (u32Byte (ticket t.oracle) offset) := by
  simpa only [Candidate.readByte,counter_event cfg hw hd hp ht,Option.bind_some,Kind.readByte,
    atomicAddBytes,ticket,u32Bytes] using u32_payload_byte (counterLoc cfg) (ticket t.oracle) offset ho

theorem counter_write_byte (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Params cfg.counter cfg.x cfg.y launch.params) (ht : t ∈ execution.traces)
    {offset : Nat} (ho : offset < 4) :
    execution.writeByte ⟨t.id,0⟩ ((counterLoc cfg).add offset) = some (u32Byte (wrap 32 (ticket t.oracle+1)) offset) := by
  simpa only [Candidate.writeByte,counter_event cfg hw hd hp ht,Option.bind_some,Kind.writeByte,
    atomicAddBytes,ticket,u32Bytes] using u32_payload_byte (counterLoc cfg) (wrap 32 (ticket t.oracle+1)) offset ho

theorem event_shape (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params)
    {e : EventId} {kind : Scalar.Kind} (he : execution.eventAt e = some kind) :
    ∃ value, e.thread.Valid geometry ∧
      ((e.serial = 0 ∧ kind = .rmw .gpu (counterLoc cfg) (atomicAddBytes value 1)) ∨
       (e.serial = 1 ∧ wrap 32 value = 0 ∧ kind = .write (xLoc cfg) (u32Bytes 1)) ∨
       (e.serial = 1 ∧ wrap 32 value = 1 ∧ kind = .write (yLoc cfg) (u32Bytes 2))) := by
  obtain ⟨t,ht,htid,hindex⟩ := eventAt_trace he
  have hv : t.id.Valid geometry := by simpa only [hg] using (hw.2.2.1 t ht).1
  have hs := (trace_shape cfg hw hd hp ht).2.2
  rcases e with ⟨thread,serial⟩
  simp only at htid
  subst thread
  refine ⟨reply t.oracle,hv,?_⟩
  rw [hs] at hindex
  unfold eventsFor events at hindex
  cases serial with
  | zero => exact Or.inl ⟨rfl,(Option.some.inj hindex).symm⟩
  | succ serial =>
    simp only [List.singleton_append,List.getElem?_cons_succ] at hindex
    unfold outputEvents at hindex
    split at hindex
    · rename_i hz
      have hb := (List.getElem?_eq_some_iff.mp hindex).1
      have hs : serial = 0 := by simp only [List.length_singleton] at hb; omega
      subst serial
      exact Or.inr (Or.inl ⟨rfl,hz,(Option.some.inj hindex).symm⟩)
    · split at hindex
      · rename_i hone
        have hb := (List.getElem?_eq_some_iff.mp hindex).1
        have hs : serial = 0 := by simp only [List.length_singleton] at hb; omega
        subst serial
        exact Or.inr (Or.inr ⟨rfl,hone,(Option.some.inj hindex).symm⟩)
      · simp at hindex

theorem read_shape (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params)
    {e : EventId} {loc : Location} {value : Symbolic.Byte} (hr : execution.readByte e loc = some value) :
    ∃ reply, e.serial = 0 ∧ payloadByte (counterLoc cfg) (u32Bytes (wrap 32 reply)) loc = some value := by
  cases he : execution.eventAt e with
  | none => simp [Candidate.readByte,he] at hr
  | some kind =>
    obtain ⟨reply,_,hs⟩ := event_shape cfg hw hd hg hp he
    rcases hs with ⟨hserial,rfl⟩ | ⟨_,_,rfl⟩ | ⟨_,_,rfl⟩
    · exact ⟨reply,hserial,by simpa only [Candidate.readByte,he,Option.bind_some,Kind.readByte,atomicAddBytes,u32Bytes] using hr⟩
    · simp [Candidate.readByte,he,Kind.readByte] at hr
    · simp [Candidate.readByte,he,Kind.readByte] at hr

end
end Ptx.AtomicDispatchEvent
