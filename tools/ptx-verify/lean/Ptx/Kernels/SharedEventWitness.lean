import Ptx.Kernels.SharedEventOutput

/-! Constructive memory/observation witnesses, independent of universal output
correctness. Shared initial bytes are arbitrary; they are overwritten before use.
-/
namespace Ptx.SharedEvent
open Ptx.ISA Ptx.Event

theorem arrival_shape (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    {event : EventId} {bid generation : Nat}
    (he : execution.eventAt event = some (.barrierArrival bid generation)) :
    ∃ tid, tid < 2 ∧ event = ⟨id tid,2⟩ ∧ bid = 0 ∧ generation = 0 := by
  obtain ⟨tid,first,second,ht,hid,hindex⟩ := event_shape c hw hd hg hp he
  have hb := (List.getElem?_eq_some_iff.mp hindex).1
  have hs : event.serial = 0 ∨ event.serial = 1 ∨ event.serial = 2 ∨ event.serial = 3 ∨
      event.serial = 4 ∨ event.serial = 5 := by simp [events] at hb; omega
  rcases event with ⟨thread,serial⟩
  simp only at hid hs hindex
  subst thread
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [events] at hindex
  exact ⟨tid,ht,rfl,hindex.1.symm,hindex.2.symm⟩

theorem return_shape (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    {event : EventId} {bid generation : Nat}
    (he : execution.eventAt event = some (.barrierReturn bid generation)) :
    ∃ tid, tid < 2 ∧ event = ⟨id tid,3⟩ ∧ bid = 0 ∧ generation = 0 := by
  obtain ⟨tid,first,second,ht,hid,hindex⟩ := event_shape c hw hd hg hp he
  have hb := (List.getElem?_eq_some_iff.mp hindex).1
  have hs : event.serial = 0 ∨ event.serial = 1 ∨ event.serial = 2 ∨ event.serial = 3 ∨
      event.serial = 4 ∨ event.serial = 5 := by simp [events] at hb; omega
  rcases event with ⟨thread,serial⟩
  simp only at hid hs hindex
  subst thread
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [events] at hindex
  exact ⟨tid,ht,rfl,hindex.1.symm,hindex.2.symm⟩

theorem trace_arrives (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    {t : ThreadTrace} (ht : t ∈ execution.traces) : Kind.barrierArrival 0 0 ∈ t.events := by
  have hv : t.id.Valid geometry := by simpa only [hg] using (hw.2.2.1 t ht).1
  obtain ⟨tid,htid,hid⟩ := valid_id hv
  have hs := trace_shape c htid hp hid (hw.2.2.1 t ht).2 (hd t ht)
  rw [hs.2.2]
  simp [events]

theorem no_exit_edges (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    (a b : EventId) : ¬ ExitBeforeReturn execution a b := by
  rintro ⟨_,t,ht,_,_,bid,generation,hb,he⟩
  obtain ⟨_,_,_,rfl,rfl⟩ := return_shape c hw hd hg hp hb
  exact Nat.lt_irrefl 0 (he.2 0 (trace_arrives c hw hd hg hp ht))

theorem barriers (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params) : BarrierParticipation execution := by
  intro leave bid generation he
  obtain ⟨tid,ht,rfl,rfl,rfl⟩ := return_shape c hw hd hg hp he
  refine ⟨⟨⟨id tid,2⟩,rfl,by change (2 : Nat) < 3; decide,(barrier_events c hw hd hg hp ht).1⟩,?_⟩
  intro t hm _
  exact Or.inl (trace_arrives c hw hd hg hp hm)

theorem sync_rank (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    {a b : EventId} (hs : BarrierSync execution a b) : a.serial < b.serial := by
  obtain ⟨_,bid,generation,ha,hb⟩ := hs
  obtain ⟨_,_,rfl,_,_⟩ := arrival_shape c hw hd hg hp ha
  obtain ⟨_,_,rfl,_,_⟩ := return_shape c hw hd hg hp hb
  change (2 : Nat) < 3
  decide

def canonicalTrace (c : SharedContract.Config) (tid : Nat) : ThreadTrace := {
  id := id tid
  oracle := fun q => if q = 0 then c.input tid else c.input (SharedContract.other tid)
  count := 17
  final := finalState c tid (c.input tid) (c.input (SharedContract.other tid))
  events := events c tid (c.input tid) (c.input (SharedContract.other tid))
}
def canonical (c : SharedContract.Config) : Candidate := ⟨(List.range 2).map (canonicalTrace c)⟩

theorem canonical_produced (c : SharedContract.Config) (tid : Nat) (parameters : Bindings)
    (ht : tid < 2) (hp : SharedContract.Params c parameters) : (canonicalTrace c tid).Produced code parameters := by
  simpa only [ThreadTrace.Produced,canonicalTrace,ite_true,ite_false,reduceCtorEq]
    using run_thread c tid (canonicalTrace c tid).oracle parameters ht hp

theorem canonical_ids (c : SharedContract.Config) : ((canonical c).traces.map ThreadTrace.id).Nodup := by
  change [id 0,id 1].Nodup
  decide

theorem canonical_member (c : SharedContract.Config) {tid : Nat} (ht : tid < 2) :
    canonicalTrace c tid ∈ (canonical c).traces := List.mem_map.mpr ⟨tid,List.mem_range.mpr ht,rfl⟩

theorem canonical_wellFormed (c : SharedContract.Config) {l : Launch}
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params) : (canonical c).WellFormed code l := by
  refine ⟨?_,canonical_ids c,?_,?_⟩
  · rw [hg]; simp [geometry,Geometry.Valid,Dim3.Positive,Dim3.one]
  · intro t ht
    obtain ⟨tid,hin,rfl⟩ := List.mem_map.mp ht
    have hb := List.mem_range.mp hin
    refine ⟨?_,canonical_produced c tid l.params hb hp⟩
    rw [hg]
    simp [canonicalTrace,ThreadId.Valid,Dim3.Within,geometry,id,CopyEvent.id,Dim3.zero,Dim3.one,hb]
  · intro thread ht
    have hv : thread.Valid geometry := by simpa only [hg] using ht
    obtain ⟨tid,hb,rfl⟩ := valid_id hv
    exact ⟨canonicalTrace c tid,canonical_member c hb,rfl⟩

theorem canonical_complete (c : SharedContract.Config) : (canonical c).Complete := by
  intro t ht
  obtain ⟨tid,_,rfl⟩ := List.mem_map.mp ht
  rfl

theorem canonical_eventAt (c : SharedContract.Config) {tid serial : Nat} (ht : tid < 2) :
    (canonical c).eventAt ⟨id tid,serial⟩ = (events c tid (c.input tid) (c.input (SharedContract.other tid)))[serial]? :=
  eventAt_of_trace (canonical_ids c) (canonical_member c ht) rfl

def rf : ReadsFrom := fun read _ =>
  if read.serial = 4 then .write ⟨id (SharedContract.other read.thread.tid.x),1⟩ else .initial

theorem canonical_read_value (c : SharedContract.Config) {l : Launch}
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params) (hi : Cells.Represents c.before l.initial)
    {read : EventId} {loc : Location} {value : Byte} (hr : (canonical c).readByte read loc = some value) :
    sourceByte (canonical c) l.initial loc (rf read loc) = some value := by
  have hw := canonical_wellFormed c hg hp
  obtain ⟨tid,answer,ht,hs⟩ := read_shape c hw (canonical_complete c) hg hp hr
  rcases hs with ⟨rfl,hpayload⟩ | ⟨rfl,hpayload⟩
  · have he := canonical_eventAt c (serial := 0) ht
    simp only [events,List.getElem?_cons_zero] at he
    have hb : payloadByte (srcLoc c tid) (payload (c.input tid)) loc = some value := by
      simpa only [Candidate.readByte,he,Option.bind_some,Kind.readByte] using hr
    have hbounds := payloadByte_bounds hb
    simp only [srcLoc,CopyEvent.srcLoc,payload,CopyEvent.payload,encodeU32_length] at hbounds
    let offset := loc.address-4*(c.src+tid)
    have hoffset : offset < 4 := by dsimp [offset]; omega
    have haddress : 4*(c.src+tid)+offset = loc.address := by dsimp [offset]; omega
    have heq : loc = (srcLoc c tid).add offset := by
      rcases loc with ⟨space,address⟩
      have hs : space = .global := hbounds.1.symm
      subst space
      change Location.mk .global address = Location.mk .global (4*(c.src+tid)+offset)
      congr 1
      exact haddress.symm
    have hv := Cells.wordByte_payload (srcLoc c tid) (wrap 32 (c.input tid)) offset hoffset
    rw [heq] at hb
    have hbValue : value = wordByte (c.input tid) offset := Option.some.inj (hb.symm.trans hv)
    have htn : tid < c.toConfig.n := by rw [c.n_two]; exact ht
    have hini := CopyEvent.initialized_of_representation c.toConfig hi tid htn offset hoffset
    simpa only [rf,reduceCtorEq,ite_false,sourceByte,heq,srcLoc] using congrArg some (hini.trans hbValue.symm)
  · have he := canonical_eventAt c (serial := 4) ht
    simp only [events,List.getElem?_cons_succ,List.getElem?_cons_zero] at he
    have hew := canonical_eventAt c (serial := 1) (SharedContract.other_lt ht)
    simp only [events,List.getElem?_cons_succ,List.getElem?_cons_zero] at hew
    change (canonical c).writeByte ⟨id (SharedContract.other tid),1⟩ loc = some value
    simpa only [sourceByte,Candidate.writeByte,hew,Candidate.readByte,he,Option.bind_some,Kind.writeByte,Kind.readByte]
      using hr

theorem canonical_memory (c : SharedContract.Config) {l : Launch}
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params) (hi : Cells.Represents c.before l.initial) :
    GenericMemoryConditions (canonical c) l.initial rf (InitialCo (canonical c)) := by
  have hw := canonical_wellFormed c hg hp
  have hd := canonical_complete c
  apply initial_co_conditions (fun event => event.serial)
  · intro a b h; exact h.2.2.2
  · intro a b h; exact sync_rank c hw hd hg hp h
  · intro a b h; exact (no_exit_edges c hw hd hg hp a b h).elim
  · exact barriers c hw hd hg hp
  · intro loc a b va vb ha hb; exact writer_unique c hw hd hg hp ha hb
  · intro read loc value hr; exact canonical_read_value c hg hp hi hr
  · intro read writer loc vr vw hr hwrite hs
    obtain ⟨tid,_,ht,hcase⟩ := read_shape c hw hd hg hp hr
    rcases hcase with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · simp [rf] at hs
    · simp only [rf,ite_true] at hs
      cases hs
      change (1 : Nat) < 4
      decide
  · intro read writer loc vr vw hr hwrite hs
    obtain ⟨tid,_,ht,hcase⟩ := read_shape c hw hd hg hp hr
    rcases hcase with ⟨hid,hpayload⟩ | ⟨hid,hpayload⟩
    · obtain ⟨other,_,hi,hwcase⟩ := write_shape c hw hd hg hp hwrite
      rcases hwcase with ⟨_,hwbyte⟩ | ⟨_,hwbyte⟩
      all_goals
        have hbr := payloadByte_bounds hpayload
        have hbw := payloadByte_bounds hwbyte
        simp only [srcLoc,dstLoc,CopyEvent.srcLoc,CopyEvent.dstLoc,sharedLoc,payload,
          CopyEvent.payload,encodeU32_length] at hbr hbw
      · cases hbr.1.trans hbw.1.symm
      · have hdisjoint := c.disjoint
        have hn := c.n_two
        omega
    · rw [hid] at hs
      simp [rf] at hs

def select (c : SharedContract.Config) (loc : Location) : Option EventId :=
  if CopyEvent.Destination c.toConfig loc then some ⟨id (loc.address/4-c.dst),5⟩ else none

def canonicalObservation (c : SharedContract.Config) (initial : ByteMap) : Observation :=
  selectedObservation (canonical c) initial (select c) (domain c)

theorem canonical_observation (c : SharedContract.Config) {l : Launch}
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params) :
    ObserverConditions (canonical c) l.initial rf (InitialCo (canonical c)) (canonicalObservation c l.initial) := by
  apply selected_observation_on_domain (canonical_complete c) (CopyEvent.domain_global c.toConfig)
  intro loc hmem writer value hwrite
  have hw := canonical_wellFormed c hg hp
  have hglobal := CopyEvent.domain_global c.toConfig loc hmem
  obtain ⟨tid,_,ht,hs⟩ := write_shape c hw (canonical_complete c) hg hp hwrite
  rcases hs with ⟨_,hpayload⟩ | ⟨hid,hpayload⟩
  all_goals
    have hb := payloadByte_bounds hpayload
    simp only [dstLoc,CopyEvent.dstLoc,sharedLoc,payload,CopyEvent.payload,encodeU32_length] at hb
  · rw [hglobal] at hb
    cases hb.1
  · have hdestination : CopyEvent.Destination c.toConfig loc := ⟨hglobal,by omega,by have := c.n_two; omega⟩
    have htid : loc.address/4-c.dst = tid := by omega
    simp only [select,ite_eq_left hdestination,htid,hid]

theorem nonvacuous (c : SharedContract.Config) : Event.Nonvacuous code (Pre c) (fun _ => domain c) := by
  intro l hp
  exact ⟨canonical c,rf,InitialCo (canonical c),canonicalObservation c l.initial,
    canonical_wellFormed c hp.1 hp.2.1,canonical_memory c hp.1 hp.2.1 hp.2.2,
    canonical_observation c hp.1 hp.2.1,rfl⟩

end Ptx.SharedEvent
