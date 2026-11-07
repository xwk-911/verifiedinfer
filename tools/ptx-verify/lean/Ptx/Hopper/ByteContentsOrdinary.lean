import Ptx.Hopper.ByteContentsControl

/-! At an actual non-return ordinary event with empty resource histories, every
unified control predecessor is an actual same-thread program-order event.
Native/TMA controls cannot invent a dependency into this ordinary event.
-/
namespace Ptx.Hopper.ByteContents
open Ptx.ISA Ptx.Hopper.Progress
noncomputable section

theorem ordinary_source_predecessors {block candidate id kind before}
    (he : candidate.eventAt id = some (.base (.ampere (.ordinary kind))))
    (hn : ∀ bid generation, kind ≠ .barrierReturn bid generation)
    (hc : Unified.ControlEdge block candidate (fun _ => []) before (.base (.source id))) :
    ∃ earlier, before = .base (.source earlier) ∧ Hopper.ProgramOrder candidate.view earlier id := by
  have hv : candidate.view.eventAt id = some (.ampere (.ordinary kind)) := by
    rw [Unified.view_eventAt,he]
    rfl
  rcases hc with hb | ha | hr | hi | hf
  · cases before with
    | base earlier =>
      rcases hb with hp | hc | hi | hr
      · cases earlier with
        | source left => exact ⟨left,rfl,hp⟩
        | descriptor _ | read _ _ | write _ _ | notify _ => cases hp
      · cases earlier with
        | source left =>
          cases kind <;> simp [Tma.CTAControl,Hopper.CTAControl,Hopper.Candidate.ctaTag,hv] at hc
          exact (hn _ _ rfl).elim
        | descriptor _ | read _ _ | write _ _ | notify _ => cases hc
      · cases hi
      · obtain ⟨loc,left,hl,_⟩ := hr; cases hl
    | arrival _ | operand _ _ => cases hb
  · cases before <;> simp [Unified.NativeArrival] at ha
  · cases before <;> simp [Unified.NativeRendezvous,Unified.NativeSync,Unified.Candidate.nativeSignatureAt,he,Wgmma.eventSignature,Wgmma.collective] at hr
  · cases before <;> simp [Unified.NativeIssue] at hi
  · cases before with
    | base _ | arrival _ => cases hf
    | operand issue operand =>
      obtain ⟨mark,groups,keep,old,after,query,hw,_⟩ := Unified.completed_has_actual_wait hf
      rw [he] at hw
      cases hw

end
end Ptx.Hopper.ByteContents
