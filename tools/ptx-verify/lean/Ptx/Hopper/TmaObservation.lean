import Ptx.Hopper.TmaControl

/-! Actual completion observations, indexed by resource-history prefixes.
Phase numbers restart at initialization; a separate lifetime stamp prevents
an old notification from being associated with a reinitialized object. Only
the immediately completed phase is used by this rule. This sufficient rule
does not claim completeness for all PTX parity-wait usages. -/
namespace Ptx.Hopper.Tma
open Ptx.ISA
noncomputable section

structure PhaseStamp where
  lifetime : Nat
  phase : Nat
  deriving Repr, DecidableEq

def lifetimeBefore (entries : List Entry) (index : Nat) : Nat :=
  ((entries.take index).filter (fun e => match e.operation with | .init _ => true | _ => false)).length

def stampBefore (entries : List Entry) (index : Nat) : Option PhaseStamp :=
  match Mbarrier.run none ((entries.map Entry.operation).take index) with
  | some (some state) => some ⟨lifetimeBefore entries index,state.phase⟩
  | _ => none

def noticeCopy (entry : Entry) : Option CopyId :=
  match entry.origin,entry.operation with | .notification id,.completeTx _ => some id | _,_ => none
def waitEvent (entry : Entry) : Option Ptx.Event.EventId :=
  match entry.origin,entry.operation with | .source event,.tryWaitParity _ true => some event | _,_ => none

/-- Computed from actual entry kinds and actual protocol prefixes. Merely
being earlier in a history, returning false, or sharing a parity is insufficient. -/
def observation (entries : List Entry) (noticeIndex waitIndex : Nat) : Option (CopyId × Ptx.Event.EventId) := do
  let notice ← entries[noticeIndex]?
  let waiting ← entries[waitIndex]?
  let id ← noticeCopy notice
  let event ← waitEvent waiting
  let before ← stampBefore entries noticeIndex
  let after ← stampBefore entries waitIndex
  if noticeIndex < waitIndex ∧ before.lifetime = after.lifetime ∧ before.phase+1 = after.phase then
    some (id,event)
  else none

theorem stamp_before_sound {entries index stamp} (h : stampBefore entries index = some stamp) :
    ∃ state, Mbarrier.run none ((entries.map Entry.operation).take index) = some (some state) ∧
      stamp.lifetime = lifetimeBefore entries index ∧ stamp.phase = state.phase := by
  unfold stampBefore at h
  cases hr : Mbarrier.run none ((entries.map Entry.operation).take index) with
  | none => simp [hr] at h
  | some state =>
    cases state with
    | none => simp [hr] at h
    | some state =>
      simp only [hr,Option.some.injEq] at h
      cases h
      exact ⟨state,rfl,rfl,rfl⟩

theorem notice_copy_sound {entry id} (h : noticeCopy entry = some id) :
    ∃ count, entry = ⟨.notification id,.completeTx count⟩ := by
  rcases entry with ⟨origin,op⟩
  cases origin <;> cases op <;> simp_all [noticeCopy]

theorem wait_event_sound {entry event} (h : waitEvent entry = some event) :
    ∃ parity, entry = ⟨.source event,.tryWaitParity parity true⟩ := by
  rcases entry with ⟨origin,op⟩
  cases origin <;> cases op <;> simp_all [waitEvent]
  split at h <;> simp_all

theorem observation_shape {entries noticeIndex waitIndex id event}
    (h : observation entries noticeIndex waitIndex = some (id,event)) :
    ∃ count parity before after,
      entries[noticeIndex]? = some ⟨.notification id,.completeTx count⟩ ∧
      entries[waitIndex]? = some ⟨.source event,.tryWaitParity parity true⟩ ∧
      stampBefore entries noticeIndex = some before ∧ stampBefore entries waitIndex = some after ∧
      noticeIndex < waitIndex ∧ before.lifetime = after.lifetime ∧ before.phase+1 = after.phase := by
  simp only [observation,bind,Option.bind_eq_some_iff] at h
  obtain ⟨notice,hn,waiting,hw,actual,hi,wait,he,before,hb,after,ha,hh⟩ := h
  split at hh
  · rename_i hc
    have hpair := Option.some.inj hh
    cases hpair
    obtain ⟨count,rfl⟩ := notice_copy_sound hi
    obtain ⟨parity,rfl⟩ := wait_event_sound he
    exact ⟨count,parity,before,after,hn,hw,hb,ha,hc⟩
  · cases hh

theorem observation_actual_phase {resolve c loc entries noticeIndex waitIndex id event}
    (hv : HistoryValid resolve c loc entries)
    (ho : observation entries noticeIndex waitIndex = some (id,event)) :
    ∃ copy parity before after,
      copyAt c id = some copy ∧ loc = resolve id.issue.thread copy.barrier ∧
      c.barrierAt event = some ⟨loc,.tryWaitParity parity true⟩ ∧
      Mbarrier.run none ((entries.map Entry.operation).take noticeIndex) = some (some before) ∧
      Mbarrier.run none ((entries.map Entry.operation).take waitIndex) = some (some after) ∧
      lifetimeBefore entries noticeIndex = lifetimeBefore entries waitIndex ∧
      before.phase+1 = after.phase ∧ 0 < after.phase ∧ parity%2 ≠ after.phase%2 := by
  obtain ⟨count,parity,ns,ws,hn,hw,hns,hws,_,he,hphase⟩ := observation_shape ho
  obtain ⟨copy,hcopy,hl,_⟩ := notification_history_has_actual_copy hv (List.mem_of_getElem? hn)
  obtain ⟨before,hbefore,hen,hpn⟩ := stamp_before_sound hns
  obtain ⟨after,hafter,hew,hpw⟩ := stamp_before_sound hws
  obtain ⟨waitState,hevent,_,hwait,hpositive,hparity⟩ := history_successful_wait_phase hv hw
  have hs : after = waitState := Option.some.inj (Option.some.inj (hafter.symm.trans hwait))
  subst waitState
  exact ⟨copy,parity,before,after,hcopy,hl,hevent,hbefore,hafter,
    hen ▸ hew ▸ he,hpn ▸ hpw ▸ hphase,hpositive,hparity⟩

theorem observation_requires_notification_before_wait {entries noticeIndex waitIndex id event}
    (ho : observation entries noticeIndex waitIndex = some (id,event)) : noticeIndex < waitIndex := by
  obtain ⟨_,_,_,_,_,_,_,_,hh⟩ := observation_shape ho
  exact hh.1

theorem observation_no_false_wait {entries noticeIndex waitIndex event parity}
    (hw : entries[waitIndex]? = some ⟨.source event,.tryWaitParity parity false⟩) :
    observation entries noticeIndex waitIndex = none := by
  simp [observation,hw,waitEvent]

theorem observation_no_reinitialized_object {entries noticeIndex waitIndex}
    (he : lifetimeBefore entries noticeIndex ≠ lifetimeBefore entries waitIndex) :
    observation entries noticeIndex waitIndex = none := by
  cases ho : observation entries noticeIndex waitIndex with
  | none => rfl
  | some pair =>
    rcases pair with ⟨id,event⟩
    obtain ⟨_,_,before,after,_,_,hn,hw,_,heq,_⟩ := observation_shape ho
    obtain ⟨_,_,hn,_⟩ := stamp_before_sound hn
    obtain ⟨_,_,hw,_⟩ := stamp_before_sound hw
    exact (he (hn ▸ hw ▸ heq)).elim

theorem origin_index {entries : List Entry} {index entry}
    (hu : (entries.map Entry.origin).Nodup) (he : entries[index]? = some entry) :
    (entries.map Entry.origin).idxOf entry.origin = index := by
  have hm : (entries.map Entry.origin)[index]? = some entry.origin := by simp [List.getElem?_map,he]
  obtain ⟨hb,hv⟩ := List.getElem?_eq_some_iff.mp hm
  simpa only [hv] using hu.idxOf_getElem index hb

theorem observation_before_of_unique {entries noticeIndex waitIndex id event}
    (hu : (entries.map Entry.origin).Nodup)
    (ho : observation entries noticeIndex waitIndex = some (id,event)) :
    Before entries (.notification id) (.source event) := by
  obtain ⟨count,parity,_,_,hn,hw,_,_,hbefore,_⟩ := observation_shape ho
  refine ⟨List.mem_map.mpr ⟨_,List.mem_of_getElem? hn,rfl⟩,
    List.mem_map.mpr ⟨_,List.mem_of_getElem? hw,rfl⟩,?_⟩
  rw [origin_index hu hn,origin_index hu hw]
  exact hbefore

theorem observation_before {resolve c loc entries noticeIndex waitIndex id event}
    (hv : HistoryValid resolve c loc entries)
    (ho : observation entries noticeIndex waitIndex = some (id,event)) :
    Before entries (.notification id) (.source event) :=
  observation_before_of_unique hv.unique ho

end
end Ptx.Hopper.Tma
