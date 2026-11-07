import Ptx.Hopper.CompletePrefix
import Ptx.Hopper.RegionLoans
import Ptx.Async.AccessLifetime

/-! Ordinary byte accesses and opaque mbarrier storage reservations. Resource
operations are actual resourceAt records, not fabricated readByte/writeByte
values. The layout-v0 mbarrier storage span is eight bytes (PTX ISA 8.0,
9.7.12.14.1). Reserving this span does not encode its opaque contents or prove
allocation/alignment validity. Whole-kernel completion is deliberately
conservative; existing TMA/native work retains its finer completion guards.
-/
namespace Ptx.Hopper.Progress
open Ptx.ISA
noncomputable section

inductive KernelUse (resolve : Tma.SharedResolver) (candidate : Unified.Candidate) :
    Unified.ControlNode → Location → Ptx.Async.Mode → Prop
  | read {id kind loc value} (he : candidate.view.eventAt id = some (.ampere (.ordinary kind)))
      (hb : kind.readByte loc = some value) : KernelUse resolve candidate (.base (.source id)) loc .read
  | write {id kind loc value} (he : candidate.view.eventAt id = some (.ampere (.ordinary kind)))
      (hb : kind.writeByte loc = some value) : KernelUse resolve candidate (.base (.source id)) loc .write
  | resource {origin event offset} (he : Tma.resourceAt resolve candidate.view origin = some event)
      (ho : offset < 8) : KernelUse resolve candidate (.base origin.node) (event.location.add offset) .write

/-- Generic combined async/ordinary/resource use, independent of any one
kernel's layout, work-ticket mapping or allocation certificate. -/
inductive UnifiedUse (resolve : Tma.SharedResolver) (descriptor : Access.DescriptorResolver) (candidate : Unified.Candidate) :
    Work → Unified.ControlNode → Location → Ptx.Async.Mode → Prop
  | async {work control node loc mode} (hu : Use resolve descriptor candidate work control node loc mode) :
      UnifiedUse resolve descriptor candidate work control loc mode
  | kernel {control loc mode} (hu : KernelUse resolve candidate control loc mode) :
      UnifiedUse resolve descriptor candidate .kernel control loc mode

theorem ordinary_read_use {resolve descriptor candidate id loc value}
    (hr : Unified.readByte resolve descriptor candidate (.base (.tma (.source id))) loc = some value) :
    KernelUse resolve candidate (.base (.source id)) loc .read := by
  cases he : candidate.view.eventAt id with
  | none => simp [Unified.readByte,Unified.kind,Access.kind,he] at hr
  | some event =>
    cases event with
    | ampere event =>
      cases event with
      | ordinary kind => exact .read he (by simpa [Unified.readByte,Unified.kind,Access.kind,he] using hr)
      | issue _ _ | commit _ | wait _ _ | mmaEntry _ | mmaReturn _ =>
        simp [Unified.readByte,Unified.kind,Access.kind,he] at hr
    | tmaIssue _ | proxyFenceAsyncShared _ | barrier _ | wgmma _ =>
      simp [Unified.readByte,Unified.kind,Access.kind,he] at hr

theorem ordinary_write_use {resolve descriptor candidate id loc value}
    (hw : Unified.writeByte resolve descriptor candidate (.base (.tma (.source id))) loc = some value) :
    KernelUse resolve candidate (.base (.source id)) loc .write := by
  cases he : candidate.view.eventAt id with
  | none => simp [Unified.writeByte,Unified.kind,Access.kind,he] at hw
  | some event =>
    cases event with
    | ampere event =>
      cases event with
      | ordinary kind => exact .write he (by simpa [Unified.writeByte,Unified.kind,Access.kind,he] using hw)
      | issue _ _ | commit _ | wait _ _ | mmaEntry _ | mmaReturn _ =>
        simp [Unified.writeByte,Unified.kind,Access.kind,he] at hw
    | tmaIssue _ | proxyFenceAsyncShared _ | barrier _ | wgmma _ =>
      simp [Unified.writeByte,Unified.kind,Access.kind,he] at hw

theorem kernel_use_present {resolve candidate control loc mode}
    (hu : KernelUse resolve candidate control loc mode) : Present candidate control := by
  cases hu with
  | read he _ | write he _ => simp [Present,Tma.Present,Hopper.Candidate.Present,he]
  | @resource origin event offset he ho =>
    cases origin with
    | source id =>
      change candidate.view.Present id
      change candidate.view.barrierAt id = some event at he
      cases ha : candidate.view.eventAt id with
      | none => simp [Hopper.Candidate.barrierAt,ha] at he
      | some actual => simp [Hopper.Candidate.Present,ha]
    | notification id =>
      obtain ⟨op,hcopy,_,_⟩ := Tma.notification_has_actual_copy he
      simp [Present,Tma.Origin.node,Tma.Present,hcopy]

theorem completed_kernel_use_done {resolve candidate histories cluster done control loc mode}
    (hc : Completed resolve candidate histories cluster done .kernel)
    (hu : KernelUse resolve candidate control loc mode) : done control := by
  cases hc with
  | kernel _ hd => exact hd control (kernel_use_present hu)

theorem pending_kernel_use_not_completed {resolve candidate histories cluster done control loc mode}
    (hu : KernelUse resolve candidate control loc mode) (hp : ¬done control) :
    ¬Completed resolve candidate histories cluster done .kernel := fun hc => hp (completed_kernel_use_done hc hu)

theorem acquired_kernel_use_done {resolve candidate histories cluster plan state event next frontier ticket control loc mode}
    (hf : Bridge.Faithful resolve candidate histories cluster plan state)
    (ha : Ptx.Async.await state.protocol event = .ok next) (he : Ptx.Async.getEvent state.protocol event = .ok frontier)
    (hcover : Ptx.Async.covers frontier ticket = true) (hm : plan ticket = some .kernel)
    (hu : KernelUse resolve candidate control loc mode) : state.done control :=
  completed_kernel_use_done (hf ticket .kernel hm (Ptx.Async.acquired_covered_complete ha he hcover)) hu

theorem pending_kernel_use_blocks_acquire {resolve candidate histories cluster plan state event frontier ticket control loc mode}
    (hf : Bridge.Faithful resolve candidate histories cluster plan state)
    (he : Ptx.Async.getEvent state.protocol event = .ok frontier) (hcover : Ptx.Async.covers frontier ticket = true)
    (hm : plan ticket = some .kernel) (hu : KernelUse resolve candidate control loc mode) (hp : ¬state.done control) :
    ∀ next, Ptx.Async.await state.protocol event ≠ .ok next := by
  intro next ha
  exact hp (acquired_kernel_use_done hf ha he hcover hm hu)

/-- A root ticket cannot acquire or drop its storage reservation while any
actual ordinary access/resource operation it covers is still outside the cut. -/
theorem pending_kernel_use_keeps_loan {resolve candidate histories cluster plan state ticket bid mode control loc useMode}
    (hf : Bridge.Faithful resolve candidate histories cluster plan state)
    (hm : plan ticket = some .kernel) (hh : Ptx.Async.Holds state.protocol bid ⟨ticket,mode⟩)
    (hu : KernelUse resolve candidate control loc useMode) (hp : ¬state.done control) :
    Ptx.Async.complete state.protocol ticket ≠ true ∧
    Ptx.Async.reclaim state.protocol bid = .error .outstandingLoan ∧
    ∀ value, Ptx.Async.hostWrite state.protocol bid value = .error .outstandingLoan := by
  refine ⟨fun hc => pending_kernel_use_not_completed hu hp (hf ticket .kernel hm hc),
    Ptx.Async.reclaim_of_holds hh,fun value => Ptx.Async.hostWrite_of_holds hh⟩

end
end Ptx.Hopper.Progress
