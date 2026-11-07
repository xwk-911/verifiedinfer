import Ptx.Hopper.MbarrierRetries
import Ptx.Hopper.ProxyPublication

/-! Preserve actual retained resource entries, protocol prefixes, lifetime and
completion observations while erasing failed waits from an admitted history.
Entry origins are never renamed. The erased list is not claimed exhaustive
for the original candidate and is not automatically a HistoryValid witness.
-/
namespace Ptx.Hopper.Tma.RetryErasure
open Ptx.ISA
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def keep (entry : Entry) : Bool := Mbarrier.Retries.keep entry.operation
def erase (entries : List Entry) : List Entry := entries.filter keep
def rank (entries : List Entry) (index : Nat) : Nat := (erase (entries.take index)).length
def isInit (entry : Entry) : Bool := match entry.operation with | .init _ => true | _ => false

theorem erased_operations (entries : List Entry) :
    (erase entries).map Entry.operation = Mbarrier.Retries.erase (entries.map Entry.operation) := by
  rw [Mbarrier.Retries.erase,List.filter_map]
  rfl

theorem erased_take (entries : List Entry) (index : Nat) :
    (erase entries).take (rank entries index) = erase (entries.take index) := by
  have hs : erase entries = erase (entries.take index)++erase (entries.drop index) := by
    simp only [erase,← List.filter_append,List.take_append_drop]
  rw [hs]
  simp [rank,List.take_append]

theorem erased_entry_at {entries : List Entry} {index entry}
    (he : entries[index]? = some entry) (hk : keep entry = true) :
    (erase entries)[rank entries index]? = some entry := by
  induction entries generalizing index with
  | nil => cases he
  | cons first rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at he
      subst entry
      simp [erase,rank,hk]
    | succ index =>
      have hh : rest[index]? = some entry := he
      have hi := ih hh
      cases hf : keep first <;> simpa [erase,rank,hf,Nat.add_comm] using hi

theorem rank_strict_of_kept {entries : List Entry} {i j entry} (hi : entries[i]? = some entry)
    (hk : keep entry = true) (hij : i < j) : rank entries i < rank entries j := by
  have ht : (entries.take j)[i]? = some entry := (List.getElem?_take_of_lt hij).trans hi
  have hh := erased_entry_at ht hk
  have hb := (List.getElem?_eq_some_iff.mp hh).1
  simpa only [rank,List.take_take,Nat.min_eq_left (Nat.le_of_lt hij)] using hb

theorem initializations_erased (entries : List Entry) : (erase entries).filter isInit = entries.filter isInit := by
  change (entries.filter keep).filter isInit = entries.filter isInit
  rw [List.filter_filter]
  apply congrArg (fun p : Entry → Bool => entries.filter p)
  funext entry
  cases entry with
  | mk origin op => cases op <;> simp [isInit,keep,Mbarrier.Retries.keep]

theorem lifetime_erased (entries : List Entry) (index : Nat) :
    lifetimeBefore (erase entries) (rank entries index) = lifetimeBefore entries index := by
  simp only [lifetimeBefore,erased_take]
  exact congrArg List.length (initializations_erased (entries.take index))

theorem prefix_run_erased {entries : List Entry} (hp : Mbarrier.Admitted (entries.map Entry.operation)) (index : Nat) :
    Mbarrier.run none (((erase entries).take (rank entries index)).map Entry.operation) =
      Mbarrier.run none ((entries.take index).map Entry.operation) := by
  obtain ⟨last,hr⟩ := hp
  obtain ⟨mid,hm⟩ := Mbarrier.Retries.run_prefix_of_success hr index
  rw [← List.map_take] at hm
  rw [erased_take,erased_operations,Mbarrier.Retries.run_erase_of_success hm,hm]

theorem stamp_erased {entries : List Entry} (hp : Mbarrier.Admitted (entries.map Entry.operation)) (index : Nat) :
    stampBefore (erase entries) (rank entries index) = stampBefore entries index := by
  simp only [stampBefore,← List.map_take,prefix_run_erased hp,lifetime_erased]

theorem observation_erased_eq {entries : List Entry} {noticeIndex waitIndex copy event count parity}
    (hp : Mbarrier.Admitted (entries.map Entry.operation))
    (hn : entries[noticeIndex]? = some ⟨.notification copy,.completeTx count⟩)
    (hw : entries[waitIndex]? = some ⟨.source event,.tryWaitParity parity true⟩) (hi : noticeIndex < waitIndex) :
    observation (erase entries) (rank entries noticeIndex) (rank entries waitIndex) = observation entries noticeIndex waitIndex := by
  have hnk : keep (⟨.notification copy,.completeTx count⟩ : Entry) = true := rfl
  have hwk : keep (⟨.source event,.tryWaitParity parity true⟩ : Entry) = true := rfl
  have hne := erased_entry_at hn hnk
  have hwe := erased_entry_at hw hwk
  have hr := rank_strict_of_kept hn hnk hi
  cases hs : stampBefore entries noticeIndex <;> cases ht : stampBefore entries waitIndex <;>
    simp [observation,hn,hw,hne,hwe,noticeCopy,waitEvent,stamp_erased hp,hs,ht,hi,hr]

theorem observation_from_erased {entries : List Entry} {noticeIndex waitIndex copy event count parity}
    (hp : Mbarrier.Admitted (entries.map Entry.operation))
    (hn : entries[noticeIndex]? = some ⟨.notification copy,.completeTx count⟩)
    (hw : entries[waitIndex]? = some ⟨.source event,.tryWaitParity parity true⟩) (hi : noticeIndex < waitIndex)
    (he : observation (erase entries) (rank entries noticeIndex) (rank entries waitIndex) = some (copy,event)) :
    observation entries noticeIndex waitIndex = some (copy,event) := by
  rw [← observation_erased_eq hp hn hw hi]
  exact he

theorem completion_observed_from_erased {resolve candidate histories cluster loc copy event noticeIndex waitIndex count parity}
    (hv : HistoryValid resolve candidate loc (histories loc))
    (hn : (histories loc)[noticeIndex]? = some ⟨.notification copy,.completeTx count⟩)
    (hw : (histories loc)[waitIndex]? = some ⟨.source event,.tryWaitParity parity true⟩) (hi : noticeIndex < waitIndex)
    (he : observation (erase (histories loc)) (rank (histories loc) noticeIndex) (rank (histories loc) waitIndex) = some (copy,event))
    (hc : cluster copy.issue.thread event.thread) (hl : loc.space = .shared event.thread.cta) :
    Access.CompletionObserved resolve candidate histories cluster copy event :=
  ⟨hc,loc,noticeIndex,waitIndex,hl,hv,observation_from_erased hv.protocol hn hw hi he⟩

end
end Ptx.Hopper.Tma.RetryErasure
