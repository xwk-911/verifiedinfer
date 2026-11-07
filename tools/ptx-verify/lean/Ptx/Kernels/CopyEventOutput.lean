import Ptx.Kernels.CopyEvent
import Ptx.Event.Region
import Ptx.Event.Contracts

/-! Universal Copy byte-output and frame proofs, using the original Config and
Params. Cell/byte representation supplies exactly the original initialized
source values. Constructive execution witnesses and operational execution
inclusion are separate obligations, not assumed by these output theorems.
-/
namespace Ptx.CopyEvent
open Ptx.ISA Ptx.Event

def srcLoc (c : CopyContract.Config) (tid : Nat) : Location := ⟨.global,4*(c.src+tid)⟩
def dstLoc (c : CopyContract.Config) (tid : Nat) : Location := ⟨.global,4*(c.dst+tid)⟩
def wordByte (answer offset : Nat) := Cells.wordByte (wrap 32 answer) offset

def Initialized (c : CopyContract.Config) (initial : ByteMap) : Prop :=
  ∀ tid, tid < c.n → ∀ offset, offset < 4 →
    initial ((srcLoc c tid).add offset) = wordByte (c.input tid) offset

theorem initialized_of_representation (c : CopyContract.Config) {initial : ByteMap}
    (hr : Cells.Represents c.before initial) : Initialized c initial := by
  intro tid ht offset ho
  exact hr (c.src+tid) (CopyContract.word (c.input tid)) (c.initialized tid ht) offset ho

theorem source_unwritten (c : CopyContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry c) (hp : CopyContract.Params c l.params)
    (tid offset : Nat) (ht : tid < c.n) (ho : offset < 4) (writer : EventId) :
    execution.writeByte writer ((srcLoc c tid).add offset) = none := by
  cases he : execution.writeByte writer ((srcLoc c tid).add offset) with
  | none => rfl
  | some value =>
    obtain ⟨other,answer,hi,_,hpayload⟩ := write_shape c hw hd hg hp he
    have hb := payloadByte_bounds hpayload
    simp only [payload,encodeU32_length,srcLoc,Location.add] at hb
    have hdisjoint := c.disjoint
    omega

theorem active_events_present (c : CopyContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry c) (hp : CopyContract.Params c l.params)
    (tid : Nat) (ht : tid < c.n) :
    ∃ answer, execution.eventAt ⟨id tid,0⟩ = some (.read (srcLoc c tid) (payload answer)) ∧
      execution.eventAt ⟨id tid,1⟩ = some (.write (dstLoc c tid) (payload answer)) := by
  have hcount : tid < c.count := by have := c.coverage; omega
  have hvalid : (id tid).Valid l.geometry := by
    rw [hg]
    simp [ThreadId.Valid,Dim3.Within,geometry,id,Dim3.zero,Dim3.one,hcount]
  obtain ⟨t,htmem,htid⟩ := hw.2.2.2 (id tid) hvalid
  have hs := active_trace_shape c hcount hp ht htid (hw.2.2.1 t htmem).2 (hd t htmem)
  refine ⟨t.oracle 0,?_,?_⟩
  all_goals
    rw [eventAt_of_trace hw.2.1 htmem htid.symm,hs.2.2]
    rfl

theorem read_byte_matches_initial (c : CopyContract.Config) {l : Launch} {execution : Candidate}
    {sources : ReadsFrom} {order : Coherence}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry c) (hp : CopyContract.Params c l.params)
    (hc : GenericMemoryConditions execution l.initial sources order)
    {tid answer : Nat} (ht : tid < c.n)
    (hr : execution.eventAt ⟨id tid,0⟩ = some (.read (srcLoc c tid) (payload answer)))
    (offset : Nat) (ho : offset < 4) :
    wordByte answer offset = l.initial ((srcLoc c tid).add offset) := by
  have hread : execution.readByte ⟨id tid,0⟩ ((srcLoc c tid).add offset) = some (wordByte answer offset) := by
    simp only [Candidate.readByte,hr,Option.bind_some,Kind.readByte]
    exact Cells.wordByte_payload _ _ _ ho
  have he := race_free_eligible (no_races c hw hd hg hp sources) ⟨id tid,0⟩ ((srcLoc c tid).add offset)
  exact unwritten_read_initial hc.agreement he hread (source_unwritten c hw hd hg hp tid offset ht ho)

theorem destination_writer_unique (c : CopyContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry c) (hp : CopyContract.Params c l.params)
    (tid offset : Nat) (_ht : tid < c.n) (ho : offset < 4)
    {writer : EventId} {value : Byte}
    (hwrite : execution.writeByte writer ((dstLoc c tid).add offset) = some value) :
    writer = ⟨id tid,1⟩ := by
  obtain ⟨other,answer,hi,hid,hpayload⟩ := write_shape c hw hd hg hp hwrite
  have hb := payloadByte_bounds hpayload
  simp only [payload,encodeU32_length,dstLoc,Location.add] at hb
  have heq : other = tid := by omega
  subst other
  exact hid

theorem output_byte (c : CopyContract.Config) {l : Launch} {execution : Candidate}
    {sources : ReadsFrom} {order : Coherence} {o : Observation}
    (hw : execution.WellFormed code l) (hg : l.geometry = geometry c)
    (hp : CopyContract.Params c l.params) (hi : Initialized c l.initial)
    (hc : GenericMemoryConditions execution l.initial sources order)
    (ho : ObserverConditions execution l.initial sources order o)
    (tid offset : Nat) (ht : tid < c.n) (hoffset : offset < 4)
    (hmem : (dstLoc c tid).add offset ∈ o.domain) :
    o.output ((dstLoc c tid).add offset) = wordByte (c.input tid) offset := by
  obtain ⟨answer,hr,hwrite⟩ := active_events_present c hw ho.complete hg hp tid ht
  have hwbyte : execution.writeByte ⟨id tid,1⟩ ((dstLoc c tid).add offset) = some (wordByte answer offset) := by
    simp only [Candidate.writeByte,hwrite,Option.bind_some,Kind.writeByte]
    exact Cells.wordByte_payload _ _ _ hoffset
  have he := race_free_observer_eligible (no_races c hw ho.complete hg hp sources) ((dstLoc c tid).add offset)
  have houtput := observer_unique_writer hc ho hmem he hwbyte
    (fun _ _ h => destination_writer_unique c hw ho.complete hg hp tid offset ht hoffset h)
  exact houtput.trans ((read_byte_matches_initial c hw ho.complete hg hp hc ht hr offset hoffset).trans
    (hi tid ht offset hoffset))

def Destination (c : CopyContract.Config) (loc : Location) : Prop :=
  loc.space = .global ∧ 4*c.dst ≤ loc.address ∧ loc.address < 4*(c.dst+c.n)

instance (c : CopyContract.Config) (loc : Location) : Decidable (Destination c loc) :=
  inferInstanceAs (Decidable (loc.space = .global ∧ 4*c.dst ≤ loc.address ∧ loc.address < 4*(c.dst+c.n)))

theorem outside_unwritten (c : CopyContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry c) (hp : CopyContract.Params c l.params)
    {loc : Location} (houtside : ¬ Destination c loc) (writer : EventId) : execution.writeByte writer loc = none := by
  cases he : execution.writeByte writer loc with
  | none => rfl
  | some value =>
    obtain ⟨tid,answer,ht,_,hpayload⟩ := write_shape c hw hd hg hp he
    have hb := payloadByte_bounds hpayload
    simp only [payload,encodeU32_length] at hb
    exfalso
    apply houtside
    exact ⟨hb.1.symm, by omega, by omega⟩

theorem output_frame (c : CopyContract.Config) {l : Launch} {execution : Candidate}
    {sources : ReadsFrom} {order : Coherence} {o : Observation}
    (hw : execution.WellFormed code l) (hg : l.geometry = geometry c)
    (hp : CopyContract.Params c l.params)
    (ho : ObserverConditions execution l.initial sources order o)
    {loc : Location} (hmem : loc ∈ o.domain) (houtside : ¬ Destination c loc) :
    o.output loc = l.initial loc :=
  observer_unwritten ho hmem (race_free_observer_eligible (no_races c hw ho.complete hg hp sources) loc)
    (outside_unwritten c hw ho.complete hg hp houtside)

def domain (c : CopyContract.Config) : List Location :=
  (List.range (4*c.before.length)).map (fun address => ⟨.global,address⟩)

theorem domain_global (c : CopyContract.Config) (address : Location) (h : address ∈ domain c) :
    address.space = .global := by
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp h
  rfl

theorem cell_in_domain (c : CopyContract.Config) {cell offset : Nat}
    (hc : cell < c.before.length) (ho : offset < 4) : Cells.location cell offset ∈ domain c := by
  exact List.mem_map.mpr ⟨4*cell+offset, List.mem_range.mpr (by omega), rfl⟩

theorem destination_in_domain (c : CopyContract.Config) {tid offset : Nat}
    (ht : tid < c.n) (ho : offset < 4) : (dstLoc c tid).add offset ∈ domain c := by
  apply cell_in_domain c (cell := c.dst+tid) (offset := offset) (ho := ho)
  have := c.dstBound
  omega

def BytePost (c : CopyContract.Config) (initial output : ByteMap) : Prop :=
  (∀ tid, tid < c.n → ∀ offset, offset < 4 →
    output ((dstLoc c tid).add offset) = wordByte (c.input tid) offset) ∧
  (∀ loc ∈ domain c, ¬ Destination c loc → output loc = initial loc)

def Pre (c : CopyContract.Config) (l : Launch) : Prop :=
  0 < c.count ∧ l.geometry = geometry c ∧ CopyContract.Params c l.params ∧ Cells.Represents c.before l.initial

theorem byte_post (c : CopyContract.Config) {l : Launch} {execution : Candidate}
    {sources : ReadsFrom} {order : Coherence} {o : Observation}
    (hw : execution.WellFormed code l) (hg : l.geometry = geometry c)
    (hp : CopyContract.Params c l.params) (hi : Cells.Represents c.before l.initial)
    (hc : GenericMemoryConditions execution l.initial sources order)
    (ho : ObserverConditions execution l.initial sources order o) (hd : o.domain = domain c) :
    BytePost c l.initial o.output := by
  constructor
  · intro tid ht offset hoffset
    exact output_byte c hw hg hp (initialized_of_representation c hi) hc ho tid offset ht hoffset
      (hd.symm ▸ destination_in_domain c ht hoffset)
  · intro loc hmem houtside
    exact output_frame c hw hg hp ho (hd.symm ▸ hmem) houtside

theorem correct (c : CopyContract.Config) :
    Event.Triple code (Pre c) (fun _ => domain c) (fun l output => BytePost c l.initial output) := by
  intro l execution sources order o hp hw hc ho hd
  exact byte_post c hw hp.2.1 hp.2.2.1 hp.2.2.2 hc ho hd

/-- Agreement with the cell postcondition of ANY completed operational execution.
This is not an assertion that an operational completed execution already exists. -/
theorem represents_cell_post (c : CopyContract.Config) {initial output : ByteMap} {m : Machine}
    (hi : Cells.Represents c.before initial) (hb : BytePost c initial output)
    (hm : CopyContract.Post c m) : Cells.Represents m.globalMem output :=
  Cells.region_represents (dst := c.dst) (count := c.n) (values := fun i => CopyContract.word (c.input i))
    hi ⟨hb.1,hb.2⟩ ⟨hm.1,hm.2.2.1,hm.2.2.2⟩

theorem completed_representation_agreement (c : CopyContract.Config) {l : Launch} {execution : Candidate}
    {sources : ReadsFrom} {order : Coherence} {o : Observation} {m m' : Machine}
    (hw : execution.WellFormed code l) (hg : l.geometry = geometry c)
    (hp : CopyContract.Params c l.params) (hi : Cells.Represents c.before l.initial)
    (hc : GenericMemoryConditions execution l.initial sources order)
    (ho : ObserverConditions execution l.initial sources order o) (hd : o.domain = domain c)
    (hpre : CopyContract.Pre c m) (hs : Steps code m m')
    (hdone : m'.threads.all (fun t => t.status == .done) = true) :
    Cells.Represents m'.globalMem o.output :=
  represents_cell_post c hi (byte_post c hw hg hp hi hc ho hd) (CopyContract.correct c m m' hpre hs hdone)

/-- Exact allocated-byte agreement also covers uninitialized frame cells. Their
bytes keep the SAME initial fallback; the cell representation alone would leave
these bytes unconstrained. Existence of a completed operational run is separate. -/
theorem post_encoding_agreement (c : CopyContract.Config) {initial output : ByteMap} {m : Machine}
    (hi : Cells.Represents c.before initial) (hb : BytePost c initial output)
    (hm : CopyContract.Post c m) (cell offset : Nat)
    (hcell : cell < c.before.length) (hoffset : offset < 4) :
    output (Cells.location cell offset) = Cells.encode m.globalMem initial (Cells.location cell offset) :=
  Cells.region_encoding_agreement (dst := c.dst) (count := c.n) (values := fun i => CopyContract.word (c.input i))
    hi ⟨hb.1,hb.2⟩ ⟨hm.1,hm.2.2.1,hm.2.2.2⟩ hcell hoffset

theorem completed_output_agreement (c : CopyContract.Config) {l : Launch} {execution : Candidate}
    {sources : ReadsFrom} {order : Coherence} {o : Observation} {m m' : Machine}
    (hw : execution.WellFormed code l) (hg : l.geometry = geometry c)
    (hp : CopyContract.Params c l.params) (hi : Cells.Represents c.before l.initial)
    (hc : GenericMemoryConditions execution l.initial sources order)
    (ho : ObserverConditions execution l.initial sources order o) (hd : o.domain = domain c)
    (hpre : CopyContract.Pre c m) (hs : Steps code m m')
    (hdone : m'.threads.all (fun t => t.status == .done) = true)
    (cell offset : Nat) (hcell : cell < c.before.length) (hoffset : offset < 4) :
    o.output (Cells.location cell offset) = Cells.encode m'.globalMem l.initial (Cells.location cell offset) :=
  post_encoding_agreement c hi (byte_post c hw hg hp hi hc ho hd)
    (CopyContract.correct c m m' hpre hs hdone) cell offset hcell hoffset

end Ptx.CopyEvent
