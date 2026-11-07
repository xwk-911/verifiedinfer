import Ptx.Kernels.AmpereTiledGraph

/-! Actual waited publication and post-read protection across arbitrary K
phases and different issuers/consumers. Copy accesses remain independent nodes
outside issuer PO. No read values, rf/co or race-freedom premise is assumed. -/
namespace Ptx.AmpereTiledPhaseOrder
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledGraph
noncomputable section

theorem po_of_present {candidate : Candidate} {a b : Ptx.Event.EventId}
    (ha : candidate.Present (.thread a)) (hb : candidate.Present (.thread b))
    (ht : a.thread = b.thread) (hs : a.serial < b.serial) : ProgramOrder candidate (.thread a) (.thread b) :=
  ⟨ha,hb,ht,hs⟩
theorem present_of_event {candidate : Candidate} {event kind}
    (he : candidate.eventAt event = some kind) : candidate.Present (.thread event) := by
  change (candidate.eventAt event).isSome = true
  rw [he]
  rfl
theorem po_of_events {candidate : Candidate} {a b : Ptx.Event.EventId} {ka kb}
    (ha : candidate.eventAt a = some ka) (hb : candidate.eventAt b = some kb)
    (ht : a.thread = b.thread) (hs : a.serial < b.serial) : ProgramOrder candidate (.thread a) (.thread b) :=
  po_of_present (present_of_event ha) (present_of_event hb) ht hs

theorem copy_wait {cfg launch candidate} (h : SourceInfo cfg launch candidate) {id : ThreadId}
    (hv : id.Valid launch.geometry) {phase : Nat} (hp : phase < cfg.k/16) (part : Fin 3) :
    WaitCovers candidate ⟨id,3*phase+part.val⟩ ⟨id,17*phase+4⟩ := by
  obtain ⟨op,hcopy,hgroup,_⟩ := copy_exists h hv hp part
  exact ⟨rfl,op,phase+1,0,hcopy,wait_event h hv hp,by omega⟩

theorem copy_before_read {cfg launch candidate} (h : SourceInfo cfg launch candidate) {writer reader : ThreadId}
    (hw : writer.Valid launch.geometry) (hr : reader.Valid launch.geometry) (hcta : writer.cta = reader.cta)
    {phase : Nat} (hp : phase < cfg.k/16) (part : Fin 3) (reg : Fin 6) :
    BaseOrder candidate (.copyWrite ⟨writer,3*phase+part.val⟩) (.thread ⟨reader,17*phase+7+reg.val⟩) := by
  have hwait := wait_event h hw hp
  have harrive := arrival_event h hw hp 0
  have hreturn := return_event h hr hp 0
  apply publish_after_wait_and_barrier (copy_wait h hw hp part)
    (po_of_events hwait harrive rfl (by simp))
    (show BarrierSync candidate (.thread ⟨writer,17*phase+5⟩) (.thread ⟨reader,17*phase+6⟩) from
      ⟨hcta,0,2*phase,harrive,hreturn⟩)
  exact po_of_present (present_of_event hreturn) (read_present h hr hp reg) rfl (by simp; omega)

theorem read_before_later_copy {cfg launch candidate} (h : SourceInfo cfg launch candidate) {reader writer : ThreadId}
    (hr : reader.Valid launch.geometry) (hw : writer.Valid launch.geometry) (hcta : reader.cta = writer.cta)
    {phase later : Nat} (hl : phase < later) (hp : later < cfg.k/16) (reg : Fin 6) (part : Fin 3) :
    BaseOrder candidate (.thread ⟨reader,17*phase+7+reg.val⟩) (.copyWrite ⟨writer,3*later+part.val⟩) := by
  have hphase : phase < cfg.k/16 := by omega
  have harrive := arrival_event h hr hphase 1
  have hreturn := return_event h hw hphase 1
  obtain ⟨op,hcopy,_,hissue⟩ := copy_exists h hw hp part
  have hread : ProgramOrder candidate (.thread ⟨reader,17*phase+7+reg.val⟩) (.thread ⟨reader,17*phase+15⟩) :=
    po_of_present (read_present h hr hphase reg) (present_of_event harrive) rfl (by have hh := reg.isLt; simp; omega)
  have hbar : BarrierSync candidate (.thread ⟨reader,17*phase+15⟩) (.thread ⟨writer,17*phase+16⟩) :=
    ⟨hcta,0,2*phase+1,harrive,hreturn⟩
  have hi : IssueBefore candidate (.thread ⟨writer,17*phase+16⟩) (.copyRead ⟨writer,3*later+part.val⟩) :=
    ⟨present_of_event hreturn,rfl,17*later+part.val,op,hissue,hcopy,by simp; omega⟩
  have hc : candidate.Present (.copyRead ⟨writer,3*later+part.val⟩) := by
    change (candidate.copyAt ⟨writer,3*later+part.val⟩).isSome = true
    rw [hcopy]
    rfl
  exact .trans (thread_program_causal hread) (.trans (barrier_causal hbar)
    (.trans (issue_causal hi) (copy_internal_causal hc)))

theorem copy_before_later_copy {cfg launch candidate} (h : SourceInfo cfg launch candidate) {earlierWriter laterWriter : ThreadId}
    (he : earlierWriter.Valid launch.geometry) (hl : laterWriter.Valid launch.geometry)
    (hcta : earlierWriter.cta = laterWriter.cta) {earlier later : Nat} (hp : earlier < later) (hb : later < cfg.k/16)
    (a b : Fin 3) : BaseOrder candidate (.copyWrite ⟨earlierWriter,3*earlier+a.val⟩) (.copyWrite ⟨laterWriter,3*later+b.val⟩) :=
  .trans (copy_before_read h he he rfl (by omega) a 0) (read_before_later_copy h he hl hcta hp hb 0 b)

end
end Ptx.AmpereTiledPhaseOrder
