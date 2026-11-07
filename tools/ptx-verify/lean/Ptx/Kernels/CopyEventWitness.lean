import Ptx.Kernels.CopyEventOutput

/-! Constructive Copy execution/observation witnesses for the original general
configuration and any represented initial byte map. Positive physical launch
geometry is explicit; the old zero-thread CPU/no-launch case is not erased.
-/
namespace Ptx.CopyEvent
open Ptx.ISA Ptx.Event

def canonicalTrace (c : CopyContract.Config) (tid : Nat) : ThreadTrace := {
  id := id tid
  oracle := fun _ => c.input tid
  count := if tid < c.n then 12 else 7
  final := if tid < c.n then activeFinal c tid (c.input tid) else maskedFinal c tid
  events := if tid < c.n then events c tid (c.input tid) else []
}
def canonical (c : CopyContract.Config) : Candidate := ⟨(List.range c.count).map (canonicalTrace c)⟩

theorem canonical_produced (c : CopyContract.Config) (tid : Nat) (parameters : Bindings)
    (ht : tid < c.count) (hp : CopyContract.Params c parameters) :
    (canonicalTrace c tid).Produced code parameters := by
  by_cases ha : tid < c.n
  · exact (by simpa only [ThreadTrace.Produced,canonicalTrace,ite_eq_left ha,context] using
      run_active c tid (fun _ => c.input tid) parameters ht hp ha)
  · exact (by simpa only [ThreadTrace.Produced,canonicalTrace,ite_eq_right ha,context] using
      run_masked c tid (fun _ => c.input tid) parameters ht hp (Nat.le_of_not_lt ha))

theorem canonical_ids (c : CopyContract.Config) :
    ((canonical c).traces.map ThreadTrace.id).Nodup := by
  have hinj : Function.Injective id := by intro a b h; exact congrArg (fun thread => thread.tid.x) h
  have hmap : ((List.range c.count).map id).Nodup :=
    List.Pairwise.map id (fun _ _ hn heq => hn (hinj heq)) List.nodup_range
  simpa only [canonical,List.map_map,Function.comp_def,canonicalTrace] using hmap

theorem canonical_member (c : CopyContract.Config) {tid : Nat} (ht : tid < c.count) :
    canonicalTrace c tid ∈ (canonical c).traces :=
  List.mem_map.mpr ⟨tid,List.mem_range.mpr ht,rfl⟩

theorem canonical_wellFormed (c : CopyContract.Config) {l : Launch} (hpositive : 0 < c.count)
    (hg : l.geometry = geometry c) (hp : CopyContract.Params c l.params) :
    (canonical c).WellFormed code l := by
  refine ⟨?_,canonical_ids c,?_,?_⟩
  · rw [hg]
    simp [Geometry.Valid,Dim3.Positive,geometry,Dim3.one,hpositive]
  · intro t ht
    obtain ⟨tid,hin,rfl⟩ := List.mem_map.mp ht
    have hcount := List.mem_range.mp hin
    refine ⟨?_,canonical_produced c tid l.params hcount hp⟩
    rw [hg]
    simp [canonicalTrace,ThreadId.Valid,Dim3.Within,geometry,id,Dim3.zero,Dim3.one,hcount]
  · intro thread ht
    have ht' : thread.Valid (geometry c) := by simpa only [hg] using ht
    obtain ⟨tid,hcount,rfl⟩ := valid_id c ht'
    exact ⟨canonicalTrace c tid,canonical_member c hcount,rfl⟩

theorem canonical_complete (c : CopyContract.Config) : (canonical c).Complete := by
  intro t ht
  obtain ⟨tid,_,rfl⟩ := List.mem_map.mp ht
  by_cases ha : tid < c.n <;> simp [canonicalTrace,ha,activeFinal,maskedFinal]

theorem canonical_eventAt (c : CopyContract.Config) {tid serial : Nat} (ht : tid < c.count) :
    (canonical c).eventAt ⟨id tid,serial⟩ = (canonicalTrace c tid).events[serial]? :=
  eventAt_of_trace (canonical_ids c) (canonical_member c ht) rfl

theorem canonical_read_value (c : CopyContract.Config) {l : Launch} (hpositive : 0 < c.count)
    (hg : l.geometry = geometry c) (hp : CopyContract.Params c l.params) (hi : Initialized c l.initial)
    {read : EventId} {address : Location} {value : Byte}
    (hr : (canonical c).readByte read address = some value) : value = l.initial address := by
  have hw := canonical_wellFormed c hpositive hg hp
  obtain ⟨tid,_,ht,hid,_⟩ := read_shape c hw (canonical_complete c) hg hp hr
  have hcount : tid < c.count := by have := c.coverage; omega
  rw [hid] at hr
  have he := canonical_eventAt c (serial := 0) hcount
  simp only [canonicalTrace,ite_eq_left ht,events,List.getElem?_cons_zero] at he
  have hb : payloadByte (srcLoc c tid) (payload (c.input tid)) address = some value := by
    simpa only [Candidate.readByte,he,Option.bind_some,Kind.readByte,srcLoc] using hr
  have hbounds := payloadByte_bounds hb
  simp only [payload,encodeU32_length,srcLoc] at hbounds
  let offset := address.address - 4*(c.src+tid)
  have hoffset : offset < 4 := by dsimp [offset]; omega
  have haddress : 4*(c.src+tid)+offset = address.address := by dsimp [offset]; omega
  have hloc : address = (srcLoc c tid).add offset := by
    rcases address with ⟨space,address⟩
    have hs : space = .global := hbounds.1.symm
    subst space
    change Location.mk .global address = Location.mk .global (4*(c.src+tid)+offset)
    congr 1
    exact haddress.symm
  have hbyte := Cells.wordByte_payload (srcLoc c tid) (wrap 32 (c.input tid)) offset hoffset
  rw [hloc] at hb
  have hv : value = wordByte (c.input tid) offset := Option.some.inj (hb.symm.trans hbyte)
  exact hv.trans ((hi tid ht offset hoffset).symm.trans (congrArg l.initial hloc.symm))

theorem canonical_unique_writes (c : CopyContract.Config) {l : Launch} (hpositive : 0 < c.count)
    (hg : l.geometry = geometry c) (hp : CopyContract.Params c l.params)
    (address : Location) (a b : EventId) (va vb : Byte)
    (ha : (canonical c).writeByte a address = some va)
    (hb : (canonical c).writeByte b address = some vb) : a = b := by
  have hw := canonical_wellFormed c hpositive hg hp
  obtain ⟨i,_,hi,haId,hpa⟩ := write_shape c hw (canonical_complete c) hg hp ha
  obtain ⟨j,_,hj,hbId,hpb⟩ := write_shape c hw (canonical_complete c) hg hp hb
  have hba := payloadByte_bounds hpa
  have hbb := payloadByte_bounds hpb
  simp only [payload,encodeU32_length] at hba hbb
  have hij : i = j := by omega
  subst j
  exact haId.trans hbId.symm

theorem canonical_no_returns (c : CopyContract.Config) {l : Launch} (hpositive : 0 < c.count)
    (hg : l.geometry = geometry c) (hp : CopyContract.Params c l.params) (leave : EventId) (bid generation : Nat) :
    (canonical c).eventAt leave ≠ some (.barrierReturn bid generation) := by
  intro he
  obtain ⟨_,_,_,hcase⟩ := event_shape c (canonical_wellFormed c hpositive hg hp) (canonical_complete c) hg hp he
  rcases hcase with ⟨_,hk⟩ | ⟨_,hk⟩ <;> cases hk

theorem canonical_memory (c : CopyContract.Config) {l : Launch} (hpositive : 0 < c.count)
    (hg : l.geometry = geometry c) (hp : CopyContract.Params c l.params) (hi : Initialized c l.initial) :
    GenericMemoryConditions (canonical c) l.initial (fun _ _ => .initial) (InitialCo (canonical c)) := by
  have hw := canonical_wellFormed c hpositive hg hp
  have hd := canonical_complete c
  apply initial_co_conditions (fun event => event.serial)
  · intro a b h; exact h.2.2.2
  · rintro a b ⟨_,bid,generation,_,hr⟩
    exact (canonical_no_returns c hpositive hg hp b bid generation hr).elim
  · rintro a b ⟨_,_,_,_,_,bid,generation,hr,_⟩
    exact (canonical_no_returns c hpositive hg hp b bid generation hr).elim
  · intro leave bid generation hr
    exact (canonical_no_returns c hpositive hg hp leave bid generation hr).elim
  · exact canonical_unique_writes c hpositive hg hp
  · intro read address value hr
    have heq := canonical_read_value c hpositive hg hp hi hr
    simpa only [sourceByte] using congrArg some heq.symm
  · intro read writer address vr vw hr hw hs
    cases hs
  · intro read writer address vr vw hr hwrite _
    obtain ⟨tid,_,ht,_,hread⟩ := read_shape c hw hd hg hp hr
    obtain ⟨other,_,hi,_,hpwrite⟩ := write_shape c hw hd hg hp hwrite
    have hbr := payloadByte_bounds hread
    have hbw := payloadByte_bounds hpwrite
    simp only [payload,encodeU32_length] at hbr hbw
    have hdisjoint := c.disjoint
    omega

def select (c : CopyContract.Config) (loc : Location) : Option EventId :=
  if Destination c loc then some ⟨id (loc.address/4-c.dst),1⟩ else none

theorem select_covers (c : CopyContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry c) (hp : CopyContract.Params c l.params)
    (loc : Location) (writer : EventId) (value : Byte) (hwrite : execution.writeByte writer loc = some value) :
    select c loc = some writer := by
  obtain ⟨tid,answer,ht,hid,hpayload⟩ := write_shape c hw hd hg hp hwrite
  have hb := payloadByte_bounds hpayload
  simp only [payload,encodeU32_length] at hb
  have hdestination : Destination c loc := ⟨hb.1.symm,by omega,by omega⟩
  have htid : loc.address/4-c.dst = tid := by omega
  simp only [select,ite_eq_left hdestination,htid,hid]

def canonicalObservation (c : CopyContract.Config) (initial : ByteMap) : Observation :=
  selectedObservation (canonical c) initial (select c) (domain c)

theorem canonical_observation (c : CopyContract.Config) {l : Launch} (hpositive : 0 < c.count)
    (hg : l.geometry = geometry c) (hp : CopyContract.Params c l.params) :
    ObserverConditions (canonical c) l.initial (fun _ _ => .initial) (InitialCo (canonical c))
      (canonicalObservation c l.initial) :=
  selected_observation (canonical_complete c) (domain_global c)
    (select_covers c (canonical_wellFormed c hpositive hg hp) (canonical_complete c) hg hp)

theorem nonvacuous (c : CopyContract.Config) : Event.Nonvacuous code (Pre c) (fun _ => domain c) := by
  intro l hp
  exact ⟨canonical c,fun _ _ => .initial,InitialCo (canonical c),canonicalObservation c l.initial,
    canonical_wellFormed c hp.1 hp.2.1 hp.2.2.1,
    canonical_memory c hp.1 hp.2.1 hp.2.2.1 (initialized_of_representation c hp.2.2.2),
    canonical_observation c hp.1 hp.2.1 hp.2.2.1,rfl⟩

end Ptx.CopyEvent
