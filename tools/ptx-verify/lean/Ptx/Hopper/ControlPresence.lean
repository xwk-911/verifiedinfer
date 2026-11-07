import Ptx.Hopper.ControlInventory

/-! Source/resource matching makes both ends of each control edge actual.
Arbitrary unvalidated resource histories do not satisfy this theorem. -/
namespace Ptx.Hopper.Progress
open Ptx.ISA
noncomputable section

theorem resource_origin_present {resolve candidate loc entries entry}
    (hh : Tma.HistoryValid resolve candidate loc entries) (he : entry ∈ entries) : Tma.Present candidate entry.origin.node := by
  have hs := Tma.history_sound hh he
  cases ho : entry.origin with
  | source event =>
    change candidate.Present event
    have hb : candidate.barrierAt event = some ⟨loc,entry.operation⟩ := by simpa [Tma.resourceAt,ho] using hs
    cases ha : candidate.eventAt event with
    | none => simp [Hopper.Candidate.barrierAt,ha] at hb
    | some op => simp [Hopper.Candidate.Present,ha]
  | notification id =>
    change (Tma.copyAt candidate id).isSome = true
    have hn : Tma.notification resolve candidate id = some ⟨loc,entry.operation⟩ := by simpa [Tma.resourceAt,ho] using hs
    obtain ⟨op,hcopy,_,_⟩ := Tma.notification_has_actual_copy hn
    simp [hcopy]

theorem tma_edge_present {resolve candidate histories left right}
    (hh : ∀ loc, Tma.HistoryValid resolve candidate loc (histories loc))
    (he : Tma.ControlEdge candidate histories left right) : Tma.Present candidate left ∧ Tma.Present candidate right := by
  rcases he with hp | hc | hi | ⟨loc,a,ha,b,hb,_,rfl,rfl⟩
  · cases left <;> cases right <;> try exact False.elim hp
    exact ⟨hp.1,hp.2.1⟩
  · cases left <;> cases right <;> try exact False.elim hc
    exact Hopper.cta_control_present hc
  · cases hi with
    | issue hi =>
      obtain ⟨op,hcopy⟩ := Option.isSome_iff_exists.mp hi
      exact ⟨by simp [Tma.Present,Hopper.Candidate.Present,Tma.copyAt_iff.mp hcopy],by simp [Tma.Present,hcopy]⟩
    | descriptorRead hr =>
      obtain ⟨op,hcopy,_⟩ := Tma.read_has_copy hr
      exact ⟨by simp [Tma.Present,hcopy],hr⟩
    | descriptorWrite hw =>
      obtain ⟨op,hcopy,_⟩ := Tma.write_has_copy hw
      exact ⟨by simp [Tma.Present,hcopy],hw⟩
    | data hr =>
      obtain ⟨op,hcopy,hbound⟩ := Tma.read_has_copy hr
      exact ⟨hr,by simp [Tma.Present,Tma.WritePresent,hcopy,hbound]⟩
    | complete hw =>
      obtain ⟨op,hcopy,_⟩ := Tma.write_has_copy hw
      exact ⟨hw,by simp [Tma.Present,hcopy]⟩
  · exact ⟨resource_origin_present (hh loc) ha,resource_origin_present (hh loc) hb⟩

theorem control_edge_present {block resolve candidate histories left right}
    (hh : ∀ loc, Tma.HistoryValid resolve candidate.view loc (histories loc))
    (he : Unified.ControlEdge block candidate histories left right) : Present candidate left ∧ Present candidate right := by
  rcases he with hb | ha | hr | hi | hf
  · cases left <;> cases right <;> try exact False.elim hb
    exact tma_edge_present hh hb
  · cases left <;> cases right <;> simp only [Unified.NativeArrival] at ha
    all_goals split at ha <;> try contradiction
    all_goals simp_all only [Unified.ControlNode.base.injEq,Unified.ControlNode.arrival.injEq]
    exact ⟨ha.1.1,ha.2⟩
  · cases left <;> cases right <;> simp only [Unified.NativeRendezvous] at hr
    all_goals split at hr <;> try contradiction
    all_goals simp_all only [Unified.ControlNode.base.injEq,Unified.ControlNode.arrival.injEq]
    obtain ⟨_,signature,hl,hr⟩ := hr
    exact ⟨by simp [Present,hl],(Unified.view_present_iff candidate _).mpr (Unified.native_signature_present hr)⟩
  · cases left <;> cases right <;> simp only [Unified.NativeIssue] at hi
    all_goals split at hi <;> try contradiction
    all_goals simp_all only [Unified.ControlNode.base.injEq,Unified.ControlNode.operand.injEq]
    obtain ⟨rfl,hrep⟩ := hi
    obtain ⟨⟨mark,call⟩,hrep⟩ := Option.isSome_iff_exists.mp hrep
    exact ⟨(Unified.view_present_iff candidate _).mpr (by simp [Unified.Candidate.Present,(Unified.representative_at hrep).1]),by simp [Present,hrep]⟩
  · cases left <;> cases right <;> simp only [Unified.NativeFinish] at hf
    all_goals split at hf <;> try contradiction
    all_goals simp_all only [Unified.ControlNode.base.injEq,Unified.ControlNode.operand.injEq]
    obtain ⟨collective,lane,mark,groups,keep,before,after,query,hwait,_⟩ := hf
    exact ⟨by simp [Present,Unified.collective_representative collective],
      (Unified.view_present_iff candidate _).mpr (by simp [Unified.Candidate.Present,hwait])⟩

end
end Ptx.Hopper.Progress
