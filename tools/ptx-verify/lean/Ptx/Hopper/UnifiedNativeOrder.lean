import Ptx.Hopper.UnifiedSchedules
import Ptx.Hopper.ByteOrder

/-! Byte-specific native async publication and completion. These predicates
refer to actual collective members, source waits, descriptor locations and
observed transfer completions. No desired value, RF map, blanket control edge
or generic-only memory strength is used as a publication premise.
The surrounding admission must also check source/collective/control legality.
-/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

def TmaReady (resolve : Tma.SharedResolver) (candidate : Candidate)
    (histories : Location → List Tma.Entry) (cluster : Access.ClusterScope)
    (copy : Tma.CopyId) (offset : Nat) (issue : Ptx.Event.EventId) (operand : Wgmma.OperandByte) (loc : Location) : Prop :=
  ∃ collective : Collective candidate issue,
    Tma.writeLocation resolve candidate.view copy offset = some loc ∧
    Wgmma.operandLocation issue.thread.cta (collective.calls 0) operand = loc ∧
    ∀ lane, ∃ wait, Access.CompletionObserved resolve candidate.view histories cluster copy wait ∧
      Access.GenericAfter candidate.view wait (collective.sources lane)

def GenericReady (candidate : Candidate) (source issue : Ptx.Event.EventId)
    (operand : Wgmma.OperandByte) (loc : Location) : Prop :=
  ∃ collective : Collective candidate issue,
    Wgmma.operandLocation issue.thread.cta (collective.calls 0) operand = loc ∧ loc.space = .shared issue.thread.cta ∧
    ∀ lane, ∃ fence, candidate.view.eventAt fence = some (.proxyFenceAsyncShared issue.thread.cta) ∧
      fence.thread.cta = issue.thread.cta ∧ Access.GenericAfter candidate.view source fence ∧
      Access.GenericAfter candidate.view fence (collective.sources lane)

def WgmmaCompletedAt (candidate : Candidate) (issue wait : Ptx.Event.EventId) : Prop :=
  ∃ collective : Collective candidate issue, ∃ lane mark groups keep before after query,
    candidate.eventAt wait = some (.wait mark groups keep before after query) ∧
    wait.thread = (collective.sources lane).thread ∧ (collective.sources lane).serial < wait.serial ∧
    mark.warpgroup = (collective.marks lane).warpgroup ∧ (collective.marks lane).sequence < mark.sequence ∧
    (collective.calls lane).group < after ∧ before ≤ after ∧ after ≤ groups ∧ keep < 8

def NativeCompleted (candidate : Candidate) (loc : Location) : Node → Node → Prop
  | .wgmmaRead issue operand,.base (.tma (.source wait)) =>
      WgmmaCompletedAt candidate issue wait ∧ ∃ mark call,
        candidate.representativeAt issue = some (mark,call) ∧ Wgmma.operandLocation issue.thread.cta call operand = loc
  | _,_ => False
def NativeReuse (resolve : Tma.SharedResolver) (candidate : Candidate) (loc : Location) : Node → Node → Prop
  | .wgmmaRead issue operand,.base (.tma (.write copy offset)) =>
      ∃ wait, WgmmaCompletedAt candidate issue wait ∧ Access.GenericAfter candidate.view wait copy.issue ∧
        Tma.writeLocation resolve candidate.view copy offset = some loc ∧ ∃ mark call,
          candidate.representativeAt issue = some (mark,call) ∧ Wgmma.operandLocation issue.thread.cta call operand = loc
  | _,_ => False
def NativePublished (resolve : Tma.SharedResolver) (candidate : Candidate)
    (histories : Location → List Tma.Entry) (cluster : Access.ClusterScope) (loc : Location) : Node → Node → Prop
  | .base (.tma (.write copy offset)),.wgmmaRead issue operand => TmaReady resolve candidate histories cluster copy offset issue operand loc
  | .base (.tma (.source source)),.wgmmaRead issue operand => GenericReady candidate source issue operand loc
  | _,_ => False

theorem tma_ready_has_actual_writer {resolve candidate histories cluster copy offset issue operand loc}
    (h : TmaReady resolve candidate histories cluster copy offset issue operand loc) :
    ∃ op, Tma.copyAt candidate.view copy = some op ∧ offset < op.descriptor.bytes := by
  obtain ⟨_,hl,_⟩ := h
  cases hc : Tma.copyAt candidate.view copy with
  | none => simp [Tma.writeLocation,hc] at hl
  | some op =>
    refine ⟨op,rfl,?_⟩
    simp only [Tma.writeLocation,hc,Option.bind_some] at hl
    split at hl
    · assumption
    · cases hl
theorem tma_ready_has_representative {resolve candidate histories cluster copy offset issue operand loc}
    (h : TmaReady resolve candidate histories cluster copy offset issue operand loc) :
    (candidate.representativeAt issue).isSome = true := by
  obtain ⟨collective,_⟩ := h
  rw [collective_representative collective]
  rfl
theorem generic_ready_requires_fence {candidate source issue operand loc}
    (h : GenericReady candidate source issue operand loc) :
    ∃ fence, candidate.view.eventAt fence = some (.proxyFenceAsyncShared issue.thread.cta) := by
  obtain ⟨_,_,_,h⟩ := h
  obtain ⟨fence,he,_⟩ := h 0
  exact ⟨fence,he⟩
theorem completed_has_actual_wait {candidate issue wait} (h : WgmmaCompletedAt candidate issue wait) :
    ∃ mark groups keep before after query, candidate.eventAt wait = some (.wait mark groups keep before after query) ∧
      before ≤ after ∧ after ≤ groups ∧ keep < 8 := by
  obtain ⟨_,_,mark,groups,keep,before,after,query,he,_,_,_,_,_,hb,ha,hk⟩ := h
  exact ⟨mark,groups,keep,before,after,query,he,hb,ha,hk⟩
theorem no_wait_no_native_completion {candidate issue wait}
    (hn : ∀ mark groups keep before after query, candidate.eventAt wait ≠ some (.wait mark groups keep before after query)) :
    ¬WgmmaCompletedAt candidate issue wait := by
  intro h
  obtain ⟨mark,groups,keep,before,after,query,he,_⟩ := completed_has_actual_wait h
  exact hn _ _ _ _ _ _ he

end
end Ptx.Hopper.Unified
