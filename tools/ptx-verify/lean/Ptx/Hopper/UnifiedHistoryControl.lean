import Ptx.Hopper.UnifiedControl
import Mathlib.Data.List.Basic

/-! Arbitrary checked resource histories inherit already-proved control paths.
Exhaustiveness supplies actual origins; a reverse/equal history position would
close a unified control cycle. No canonical history order is assumed. -/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

theorem tma_issue_notification_path {block candidate histories id op}
    (he : Tma.copyAt candidate.view id = some op) (hb : 0 < op.descriptor.bytes) :
    Ptx.Event.Path (ControlEdge block candidate histories) (.base (.source id.issue)) (.base (.notify id)) := by
  have hw : Tma.WritePresent candidate.view id 0 := by rw [Tma.WritePresent,he]; exact hb
  have hi : Tma.InternalEdge candidate.view (.source id.issue) (.descriptor id) := .issue (by rw [he]; rfl)
  exact .trans (.single (base_control_edge (.inr (.inr (.inl hi)))))
    (.trans (.single (base_control_edge (.inr (.inr (.inl (.descriptorWrite hw))))))
      (.single (base_control_edge (.inr (.inr (.inl (.complete hw)))))))

theorem history_control_edge {block candidate histories loc left right lop rop}
    (hh : Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hl : Tma.resourceAt Tma.localShared candidate.view left = some ⟨loc,lop⟩)
    (hr : Tma.resourceAt Tma.localShared candidate.view right = some ⟨loc,rop⟩)
    (hb : Tma.Before (histories loc) left right) :
    ControlEdge block candidate histories (.base left.node) (.base right.node) := by
  have hleft := Tma.history_complete hh hl
  have hright := Tma.history_complete hh hr
  exact base_control_edge (.inr (.inr (.inr ⟨loc,⟨left,lop⟩,hleft,⟨right,rop⟩,hright,hb,rfl,rfl⟩)))

theorem history_before_of_control_path {block candidate histories loc left right lop rop}
    (hh : Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : ControlAcyclic block candidate histories)
    (hl : Tma.resourceAt Tma.localShared candidate.view left = some ⟨loc,lop⟩)
    (hr : Tma.resourceAt Tma.localShared candidate.view right = some ⟨loc,rop⟩)
    (hp : Ptx.Event.Path (ControlEdge block candidate histories) (.base left.node) (.base right.node)) :
    Tma.Before (histories loc) left right := by
  have hleft := Tma.history_complete hh hl
  have hright := Tma.history_complete hh hr
  have hmleft : left ∈ (histories loc).map Tma.Entry.origin := List.mem_map.mpr ⟨_,hleft,rfl⟩
  have hmright : right ∈ (histories loc).map Tma.Entry.origin := List.mem_map.mpr ⟨_,hright,rfl⟩
  refine ⟨hmleft,hmright,?_⟩
  by_contra hn
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_gt hn) with hreverse | hequal
  · have hb : Tma.Before (histories loc) right left := ⟨hmright,hmleft,hreverse⟩
    exact hc _ (.trans hp (.single (history_control_edge hh hr hl hb)))
  · have he : left = right := (List.idxOf_inj hmleft).mp hequal.symm
    subst right
    exact hc _ hp

theorem history_reverse_rejected_of_control_path {block candidate histories loc left right lop rop}
    (hh : Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : ControlAcyclic block candidate histories)
    (hl : Tma.resourceAt Tma.localShared candidate.view left = some ⟨loc,lop⟩)
    (hr : Tma.resourceAt Tma.localShared candidate.view right = some ⟨loc,rop⟩)
    (hp : Ptx.Event.Path (ControlEdge block candidate histories) (.base left.node) (.base right.node)) :
    ¬Tma.Before (histories loc) right left := by
  intro hb
  exact hc _ (.trans hp (.single (history_control_edge hh hr hl hb)))

end
end Ptx.Hopper.Unified

namespace Ptx.Hopper.Tma
noncomputable section

theorem before_prefix_closed {entries : List Entry} {left right : Origin} (hb : Before entries left right) (cut : Nat)
    (hr : right ∈ (entries.take cut).map Entry.origin) : left ∈ (entries.take cut).map Entry.origin := by
  rw [List.map_take] at hr ⊢
  exact (List.mem_take_iff_idxOf_lt hb.1).2 (hb.2.2.trans ((List.mem_take_iff_idxOf_lt hb.2.1).1 hr))

theorem later_not_in_prefix {entries : List Entry} {left right : Origin} (hb : Before entries left right) (cut : Nat)
    (hcut : cut ≤ (entries.map Entry.origin).idxOf left+1) : right ∉ (entries.take cut).map Entry.origin := by
  rw [List.map_take]
  intro hr
  have hi := (List.mem_take_iff_idxOf_lt hb.2.1).1 hr
  have hs := hb.2.2
  omega

end
end Ptx.Hopper.Tma
