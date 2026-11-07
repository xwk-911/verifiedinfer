import Ptx.Kernels.SharedEvent

namespace Ptx.SharedEvent
open Ptx.ISA Ptx.Event

theorem present (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    {tid serial : Nat} (ht : tid < 2) (hs : serial < 6) : execution.Present ⟨id tid,serial⟩ := by
  obtain ⟨first,second,he⟩ := events_present c hw hd hg hp tid ht
  have hb : serial < (events c tid first second).length := by simp [events]; exact hs
  simp only [Candidate.Present,he,List.getElem?_eq_getElem hb]
  rfl

theorem program_order (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    {tid a b : Nat} (ht : tid < 2) (hab : a < b) (hb : b < 6) :
    ProgramOrder execution ⟨id tid,a⟩ ⟨id tid,b⟩ :=
  ⟨present c hw hd hg hp ht (by omega),present c hw hd hg hp ht hb,rfl,hab⟩

theorem barrier_events (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    {tid : Nat} (ht : tid < 2) :
    execution.eventAt ⟨id tid,2⟩ = some (.barrierArrival 0 0) ∧
    execution.eventAt ⟨id tid,3⟩ = some (.barrierReturn 0 0) := by
  obtain ⟨first,second,he⟩ := events_present c hw hd hg hp tid ht
  simp only [he,events,List.getElem?_cons_succ,List.getElem?_cons_zero,and_self]

theorem shared_causal (c : SharedContract.Config) {l : Launch} {execution : Candidate} {sources : ReadsFrom}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    {writer reader : Nat} (hwid : writer < 2) (hrid : reader < 2)
    (ho : execution.Overlap ⟨id writer,1⟩ ⟨id reader,4⟩) :
    Causality execution sources ⟨id writer,1⟩ ⟨id reader,4⟩ :=
  barrier_memory_causal (arrive := ⟨id writer,2⟩) (leave := ⟨id reader,3⟩)
    ho (program_order c hw hd hg hp hwid (by decide) (by decide))
    ⟨rfl,0,0,(barrier_events c hw hd hg hp hwid).1,(barrier_events c hw hd hg hp hrid).2⟩
    (program_order c hw hd hg hp hrid (by decide) (by decide))

theorem write_read_order (c : SharedContract.Config) {l : Launch} {execution : Candidate} {sources : ReadsFrom}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    {writer reader : EventId} {loc : Location} {vw vr : Byte}
    (hwrite : execution.writeByte writer loc = some vw) (hread : execution.readByte reader loc = some vr) :
    Causality execution sources writer reader := by
  obtain ⟨i,_,hi,hsw⟩ := write_shape c hw hd hg hp hwrite
  obtain ⟨j,_,hj,hsr⟩ := read_shape c hw hd hg hp hread
  rcases hsw with ⟨rfl,hwbyte⟩ | ⟨rfl,hwbyte⟩ <;>
    rcases hsr with ⟨rfl,hrbyte⟩ | ⟨rfl,hrbyte⟩
  all_goals
    have hbw := payloadByte_bounds hwbyte
    have hbr := payloadByte_bounds hrbyte
    simp only [srcLoc,dstLoc,CopyEvent.srcLoc,CopyEvent.dstLoc,sharedLoc,payload,
      CopyEvent.payload,encodeU32_length] at hbw hbr
  · cases hbw.1.trans hbr.1.symm
  · exact shared_causal c hw hd hg hp hi hj ⟨loc,Or.inr (by simp [hwrite]),Or.inl (by simp [hread])⟩
  · have hdisjoint := c.disjoint
    have hn := c.n_two
    omega
  · cases hbw.1.trans hbr.1.symm

theorem writer_unique (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    {a b : EventId} {loc : Location} {va vb : Byte}
    (ha : execution.writeByte a loc = some va) (hb : execution.writeByte b loc = some vb) : a = b := by
  obtain ⟨i,_,hi,ha⟩ := write_shape c hw hd hg hp ha
  obtain ⟨j,_,hj,hb⟩ := write_shape c hw hd hg hp hb
  rcases ha with ⟨rfl,hpa⟩ | ⟨rfl,hpa⟩ <;> rcases hb with ⟨rfl,hpb⟩ | ⟨rfl,hpb⟩
  all_goals
    have hba := payloadByte_bounds hpa
    have hbb := payloadByte_bounds hpb
    simp only [dstLoc,CopyEvent.dstLoc,sharedLoc,payload,CopyEvent.payload,encodeU32_length] at hba hbb
  · have he : i = j := by omega
    subst j
    rfl
  · cases hba.1.trans hbb.1.symm
  · cases hba.1.trans hbb.1.symm
  · have he : i = j := by omega
    subst j
    rfl

theorem write_self_strong {execution : Candidate} {event : EventId} (hw : execution.Writes event) :
    MorallyStrong execution event event := by
  obtain ⟨loc,value,hv⟩ := hw
  exact Event.write_self_strong hv

theorem no_rmw (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params) (event : EventId) :
    ¬ execution.IsRMW event := by
  rintro ⟨scope,base,bytes,he⟩
  obtain ⟨_,_,_,_,_,hindex⟩ := event_shape c hw hd hg hp he
  have hm := List.mem_of_getElem? hindex
  simp [events] at hm

theorem no_races (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    (sources : ReadsFrom) (a b : EventId) : ¬ DataRace execution sources a b := by
  intro hrace
  obtain ⟨loc,ha,hb⟩ := hrace.overlap
  rcases ha with ha | ha <;> rcases hb with hb | hb
  all_goals
    obtain ⟨va,hva⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨vb,hvb⟩ := Option.isSome_iff_exists.mp hb
  · rcases hrace.conflict with ⟨_,_,hwrite⟩ | ⟨_,_,hwrite⟩
    · exact read_write_exclusive (no_rmw c hw hd hg hp a) hva hwrite
    · exact read_write_exclusive (no_rmw c hw hd hg hp b) hvb hwrite
  · exact hrace.notBackward (write_read_order c hw hd hg hp hvb hva)
  · exact hrace.notForward (write_read_order c hw hd hg hp hva hvb)
  · have he := writer_unique c hw hd hg hp hva hvb
    subst b
    exact hrace.notStrong (write_self_strong ⟨loc,va,hva⟩)

theorem source_unwritten (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    (hw : execution.WellFormed code l) (hd : execution.Complete)
    (hg : l.geometry = geometry) (hp : SharedContract.Params c l.params)
    (tid offset : Nat) (ht : tid < 2) (ho : offset < 4) (writer : EventId) :
    execution.writeByte writer ((srcLoc c tid).add offset) = none := by
  cases he : execution.writeByte writer ((srcLoc c tid).add offset) with
  | none => rfl
  | some value =>
    obtain ⟨other,_,hi,hs⟩ := write_shape c hw hd hg hp he
    rcases hs with ⟨_,hpayload⟩ | ⟨_,hpayload⟩
    all_goals
      have hb := payloadByte_bounds hpayload
      simp only [srcLoc,dstLoc,CopyEvent.srcLoc,CopyEvent.dstLoc,sharedLoc,payload,
        CopyEvent.payload,encodeU32_length,Location.add] at hb
    · cases hb.1
    · have hdisjoint := c.disjoint
      have hn := c.n_two
      omega

end Ptx.SharedEvent
