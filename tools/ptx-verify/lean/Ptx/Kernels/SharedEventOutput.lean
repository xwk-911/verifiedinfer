import Ptx.Kernels.SharedEventMemory

/-! Universal byte-output/frame contract, over arbitrary provenance-checked
complete candidates and memory/observer witnesses. Shared load answers are
derived through the actual barrier, not supplied in the precondition.
-/
namespace Ptx.SharedEvent
open Ptx.ISA Ptx.Event

theorem source_byte_correct (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    {sources : ReadsFrom} {order : Coherence}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    (hi : Cells.Represents c.before l.initial)
    (hc : GenericMemoryConditions execution l.initial sources order)
    {tid answer : Nat} (ht : tid < 2)
    (hr : execution.eventAt ⟨id tid,0⟩ = some (.read (srcLoc c tid) (payload answer)))
    (offset : Nat) (ho : offset < 4) : wordByte answer offset = wordByte (c.input tid) offset := by
  have hb : execution.readByte ⟨id tid,0⟩ ((srcLoc c tid).add offset) = some (wordByte answer offset) := by
    simp only [Candidate.readByte,hr,Option.bind_some,Kind.readByte]
    exact Cells.wordByte_payload _ _ _ ho
  have he := race_free_eligible (no_races c hw hd hg hp sources) ⟨id tid,0⟩ ((srcLoc c tid).add offset)
  have hv := unwritten_read_initial hc.agreement he hb (source_unwritten c hw hd hg hp tid offset ht ho)
  have htn : tid < c.toConfig.n := by rw [c.n_two]; exact ht
  exact hv.trans (CopyEvent.initialized_of_representation c.toConfig hi tid htn offset ho)

theorem shared_byte_correct (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    {sources : ReadsFrom} {order : Coherence}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    (hi : Cells.Represents c.before l.initial)
    (hc : GenericMemoryConditions execution l.initial sources order)
    {tid answer : Nat} (ht : tid < 2)
    (hr : execution.eventAt ⟨id tid,4⟩ = some (.read (sharedLoc (SharedContract.other tid)) (payload answer)))
    (offset : Nat) (ho : offset < 4) :
    wordByte answer offset = wordByte (c.input (SharedContract.other tid)) offset := by
  have hother := SharedContract.other_lt ht
  obtain ⟨first,second,hevents⟩ := events_present c hw hd hg hp (SharedContract.other tid) hother
  have hwEvent : execution.eventAt ⟨id (SharedContract.other tid),1⟩ =
      some (.write (sharedLoc (SharedContract.other tid)) (payload first)) := by simp [hevents,events]
  have hrEvent : execution.eventAt ⟨id (SharedContract.other tid),0⟩ =
      some (.read (srcLoc c (SharedContract.other tid)) (payload first)) := by simp [hevents,events]
  let loc := (sharedLoc (SharedContract.other tid)).add offset
  have hbRead : execution.readByte ⟨id tid,4⟩ loc = some (wordByte answer offset) := by
    simp only [Candidate.readByte,hr,Option.bind_some,Kind.readByte,loc]
    exact Cells.wordByte_payload _ _ _ ho
  have hbWrite : execution.writeByte ⟨id (SharedContract.other tid),1⟩ loc = some (wordByte first offset) := by
    simp only [Candidate.writeByte,hwEvent,Option.bind_some,Kind.writeByte,loc]
    exact Cells.wordByte_payload _ _ _ ho
  have heligible := race_free_eligible (no_races c hw hd hg hp sources) ⟨id tid,4⟩ loc
  have hcause := write_read_order (sources := sources) c hw hd hg hp hbWrite hbRead
  have hv := unique_writer_visible hc heligible hbWrite hbRead hcause
    (fun _ _ h => writer_unique c hw hd hg hp h hbWrite)
  exact hv.trans (source_byte_correct c hw hd hg hp hi hc hother hrEvent offset ho)

abbrev domain (c : SharedContract.Config) := CopyEvent.domain c.toConfig

theorem destination_in_domain (c : SharedContract.Config) {tid offset : Nat} (ht : tid < 2) (ho : offset < 4) :
    (dstLoc c tid).add offset ∈ domain c :=
  CopyEvent.destination_in_domain c.toConfig (by rw [c.n_two]; exact ht) ho

theorem output_byte (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    {sources : ReadsFrom} {order : Coherence} {o : Observation}
    (hw : execution.WellFormed code l) (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    (hi : Cells.Represents c.before l.initial) (hc : GenericMemoryConditions execution l.initial sources order)
    (ho : ObserverConditions execution l.initial sources order o) (hd : o.domain = domain c)
    (tid offset : Nat) (ht : tid < 2) (hoffset : offset < 4) :
    o.output ((dstLoc c tid).add offset) = wordByte (c.input (SharedContract.other tid)) offset := by
  obtain ⟨first,second,hevents⟩ := events_present c hw ho.complete hg hp tid ht
  have hwrite : execution.eventAt ⟨id tid,5⟩ = some (.write (dstLoc c tid) (payload second)) := by simp [hevents,events]
  have hread : execution.eventAt ⟨id tid,4⟩ =
      some (.read (sharedLoc (SharedContract.other tid)) (payload second)) := by simp [hevents,events]
  have hb : execution.writeByte ⟨id tid,5⟩ ((dstLoc c tid).add offset) = some (wordByte second offset) := by
    simp only [Candidate.writeByte,hwrite,Option.bind_some,Kind.writeByte]
    exact Cells.wordByte_payload _ _ _ hoffset
  have he := race_free_observer_eligible (no_races c hw ho.complete hg hp sources) ((dstLoc c tid).add offset)
  have hv := observer_unique_writer hc ho (hd.symm ▸ destination_in_domain c ht hoffset) he hb
    (fun _ _ h => writer_unique c hw ho.complete hg hp h hb)
  exact hv.trans (shared_byte_correct c hw ho.complete hg hp hi hc ht hread offset hoffset)

theorem outside_unwritten (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    {loc : Location} (hglobal : loc.space = .global) (hout : ¬ CopyEvent.Destination c.toConfig loc) (writer : EventId) :
    execution.writeByte writer loc = none := by
  cases he : execution.writeByte writer loc with
  | none => rfl
  | some value =>
    obtain ⟨tid,_,ht,hs⟩ := write_shape c hw hd hg hp he
    rcases hs with ⟨_,hpayload⟩ | ⟨_,hpayload⟩
    all_goals
      have hb := payloadByte_bounds hpayload
      simp only [dstLoc,CopyEvent.dstLoc,sharedLoc,payload,CopyEvent.payload,encodeU32_length] at hb
    · rw [hglobal] at hb
      cases hb.1
    · exfalso
      apply hout
      exact ⟨hglobal,by omega,by have := c.n_two; omega⟩

def BytePost (c : SharedContract.Config) (initial output : ByteMap) : Prop :=
  (∀ tid, tid < 2 → ∀ offset, offset < 4 →
    output ((dstLoc c tid).add offset) = wordByte (c.input (SharedContract.other tid)) offset) ∧
  (∀ loc ∈ domain c, ¬ CopyEvent.Destination c.toConfig loc → output loc = initial loc)

def Pre (c : SharedContract.Config) (l : Launch) : Prop :=
  l.geometry = geometry ∧ SharedContract.Params c l.params ∧ Cells.Represents c.before l.initial

theorem correct (c : SharedContract.Config) :
    Event.Triple code (Pre c) (fun _ => domain c) (fun l output => BytePost c l.initial output) := by
  intro l execution sources order o hp hw hc ho hd
  constructor
  · exact fun tid ht offset hoffset => output_byte c hw hp.1 hp.2.1 hp.2.2 hc ho hd tid offset ht hoffset
  · intro loc hmem hout
    exact observer_unwritten ho (hd.symm ▸ hmem)
      (race_free_observer_eligible (no_races c hw ho.complete hp.1 hp.2.1 sources) loc)
      (outside_unwritten c hw ho.complete hp.1 hp.2.1 (CopyEvent.domain_global c.toConfig loc hmem) hout)

end Ptx.SharedEvent
