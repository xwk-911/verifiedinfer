import Ptx.Hopper.TmaPrefixAccounting
import Ptx.Hopper.MbarrierTransactionCounts
import Mathlib.Data.List.Nodup

/-! Count bounds from injective, prefix-present parents. Matching is a proof
obligation over actual entries: the rule does not invent an arrival for a
notification, merge duplicate events, or assume nonnegative transaction credit. -/
namespace Ptx.Hopper.Tma
open Ptx.ISA
noncomputable section

def isArrivalEntry (entry : Entry) : Bool :=
  match entry.operation with | .arriveExpectTx _ => true | _ => false
def isCompletionEntry (bytes : Nat) (entry : Entry) : Bool :=
  match entry.operation with | .completeTx n => n == bytes | _ => false

theorem completion_entry_operation {bytes entry} (h : isCompletionEntry bytes entry = true) : entry.operation = .completeTx bytes := by
  cases he : entry.operation <;> simp_all [isCompletionEntry]

theorem prefix_entry_of_origin {resolve candidate loc entries origin op}
    (hh : HistoryValid resolve candidate loc entries)
    (ha : resourceAt resolve candidate origin = some ⟨loc,op⟩) (cut : Nat)
    (hp : origin ∈ (entries.take cut).map Entry.origin) : Entry.mk origin op ∈ entries.take cut := by
  obtain ⟨entry,he,horigin⟩ := List.mem_map.mp hp
  have hs := history_sound hh (List.mem_of_mem_take he)
  rw [horigin,ha] at hs
  have hop := congrArg BarrierEvent.operation (Option.some.inj hs)
  rcases entry with ⟨actual,operation⟩
  dsimp only at horigin hop
  subst actual
  subst operation
  exact he

theorem before_left_in_right_prefix {entries : List Entry} {left right : Origin} (hb : Before entries left right) :
    left ∈ (entries.take ((entries.map Entry.origin).idxOf right)).map Entry.origin := by
  rw [List.map_take]
  exact (List.mem_take_iff_idxOf_lt hb.1).2 hb.2.2

theorem origin_not_in_own_prefix {entries : List Entry} {origin : Origin} (hm : origin ∈ entries.map Entry.origin) :
    origin ∉ (entries.take ((entries.map Entry.origin).idxOf origin)).map Entry.origin := by
  rw [List.map_take]
  intro h
  have hi := (List.mem_take_iff_idxOf_lt hm).1 h
  omega

theorem observation_no_phase_match {entries noticeIndex waitIndex before after}
    (hn : stampBefore entries noticeIndex = some before) (hw : stampBefore entries waitIndex = some after)
    (hp : before.phase+1 ≠ after.phase) : observation entries noticeIndex waitIndex = none := by
  cases ho : observation entries noticeIndex waitIndex with
  | none => rfl
  | some pair =>
    obtain ⟨_,_,actualBefore,actualAfter,_,_,hbefore,hafter,_,_,hphase⟩ := observation_shape ho
    have hb : actualBefore = before := Option.some.inj (hbefore.symm.trans hn)
    have ha : actualAfter = after := Option.some.inj (hafter.symm.trans hw)
    subst actualBefore
    subst actualAfter
    exact (hp hphase).elim

theorem arrival_entries_count (entries : List Entry) :
    (entries.filter isArrivalEntry).length = Mbarrier.arrivalCount (entries.map Entry.operation) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    cases entry with
    | mk origin op => cases op <;> simp [List.filter_cons,isArrivalEntry,Mbarrier.arrivalCount,Mbarrier.arrivalUnit] at ih ⊢ <;> omega

theorem completion_entries_count (bytes : Nat) (entries : List Entry) :
    (entries.filter (isCompletionEntry bytes)).length = Mbarrier.completionCount bytes (entries.map Entry.operation) := by
  simp only [Mbarrier.completionCount,List.filter_map,List.length_map]
  rfl

theorem filter_count_le_of_injective_parent {α : Type} {entries : List α} {child parent : α → Bool} {f : α → α}
    (hu : entries.Nodup)
    (hf : ∀ x ∈ entries.filter child, ∀ y ∈ entries.filter child, f x = f y → x = y)
    (hm : ∀ x ∈ entries.filter child, f x ∈ entries.filter parent) :
    (entries.filter child).length ≤ (entries.filter parent).length := by
  have hn := List.Nodup.map_on hf (hu.filter child)
  have hs : (entries.filter child).map f ⊆ entries.filter parent := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    exact hm y hy
  simpa only [List.length_map] using hn.length_le_of_subset hs

theorem filter_count_lt_of_missing_parent {α : Type} {entries : List α} {child parent : α → Bool} {f : α → α}
    (hu : entries.Nodup)
    (hf : ∀ x ∈ entries.filter child, ∀ y ∈ entries.filter child, f x = f y → x = y)
    (hm : ∀ x ∈ entries.filter child, f x ∈ entries.filter parent)
    (missing : α) (hp : missing ∈ entries.filter parent) (hn : missing ∉ (entries.filter child).map f) :
    (entries.filter child).length < (entries.filter parent).length := by
  have hmap := List.Nodup.map_on hf (hu.filter child)
  have hcons : (missing :: (entries.filter child).map f).Nodup := List.nodup_cons.mpr ⟨hn,hmap⟩
  have hs : missing :: (entries.filter child).map f ⊆ entries.filter parent := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hp
    · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
      exact hm y hy
  have h := hcons.length_le_of_subset hs
  simp only [List.length_cons,List.length_map] at h
  omega

theorem completion_count_le_arrivals {entries : List Entry} (bytes : Nat) (parent : Entry → Entry)
    (hu : entries.Nodup)
    (hf : ∀ x ∈ entries.filter (isCompletionEntry bytes), ∀ y ∈ entries.filter (isCompletionEntry bytes), parent x = parent y → x = y)
    (hm : ∀ x ∈ entries.filter (isCompletionEntry bytes), parent x ∈ entries.filter isArrivalEntry) :
    Mbarrier.completionCount bytes (entries.map Entry.operation) ≤ Mbarrier.arrivalCount (entries.map Entry.operation) := by
  rw [← completion_entries_count,← arrival_entries_count]
  exact filter_count_le_of_injective_parent hu hf hm

def noticeParent (offset budget : Nat) (entry : Entry) : Entry :=
  match entry.origin with
  | .notification copy => ⟨.source ⟨copy.issue.thread,copy.issue.serial-offset⟩,.arriveExpectTx budget⟩
  | _ => entry

end
end Ptx.Hopper.Tma
