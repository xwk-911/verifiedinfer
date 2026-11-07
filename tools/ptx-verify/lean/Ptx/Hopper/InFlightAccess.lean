import Ptx.Hopper.ControlPrefix
import Ptx.Hopper.UnifiedBytes
import Ptx.Hopper.ProxyPublication
import Ptx.Async.Model

/-! Actual descriptor/data/native byte uses and their control-prefix lifetime.
Completion is source-matched: a TMA true wait must observe that copy's phase;
native reads require actual native group completion. This supplies access
completion facts, not allocation ownership or physical runtime observation. -/
namespace Ptx.Hopper.Progress
open Ptx.ISA
noncomputable section

inductive Work
  | tma (copy : Tma.CopyId)
  | native (issue : Ptx.Event.EventId)
  | kernel
  deriving Repr, DecidableEq

inductive Use (resolve : Tma.SharedResolver) (descriptor : Access.DescriptorResolver) (candidate : Unified.Candidate) :
    Work → Unified.ControlNode → Unified.Node → Location → Ptx.Async.Mode → Prop
  | descriptor {id op offset} (hc : Tma.copyAt candidate.view id = some op) (ho : offset < 128) :
      Use resolve descriptor candidate (.tma id) (.base (.descriptor id)) (.base (.tma (.descriptor id)))
        ((descriptor id.issue.thread op.descriptorAddress).add offset) .read
  | tmaRead {id offset loc value} (hl : Tma.readLocation candidate.view id offset = some loc)
      (hv : Tma.transferByte candidate.view id offset = some value) :
      Use resolve descriptor candidate (.tma id) (.base (.read id offset)) (.base (.tma (.read id offset))) loc .read
  | tmaWrite {id offset loc value} (hl : Tma.writeLocation resolve candidate.view id offset = some loc)
      (hv : Tma.transferByte candidate.view id offset = some value) :
      Use resolve descriptor candidate (.tma id) (.base (.write id offset)) (.base (.tma (.write id offset))) loc .write
  | nativeRead {issue mark call operand} (hr : candidate.representativeAt issue = some (mark,call)) :
      Use resolve descriptor candidate (.native issue) (.operand issue operand) (.wgmmaRead issue operand)
        (Wgmma.operandLocation issue.thread.cta call operand) .read

inductive Completed (resolve : Tma.SharedResolver) (candidate : Unified.Candidate) (histories : Location → List Tma.Entry)
    (cluster : Access.ClusterScope) (done : Cut) : Work → Prop
  | tma {id op wait} (hc : Tma.copyAt candidate.view id = some op) (hp : 0 < op.descriptor.bytes)
      (ho : Access.CompletionObserved resolve candidate.view histories cluster id wait) (hd : done (.base (.source wait))) :
      Completed resolve candidate histories cluster done (.tma id)
  | native {issue wait} (hc : Unified.WgmmaCompletedAt candidate issue wait) (hd : done (.base (.source wait))) :
      Completed resolve candidate histories cluster done (.native issue)
  /-- Source termination and every actual control node; no physical progress assumption. -/
  | kernel (hc : Unified.Complete candidate) (hd : ∀ node, Present candidate node → done node) :
      Completed resolve candidate histories cluster done .kernel

theorem use_actual {resolve descriptor candidate work control node loc mode}
    (hu : Use resolve descriptor candidate work control node loc mode) :
    match mode with
    | .read => ∃ value, Unified.readByte resolve descriptor candidate node loc = some value
    | .write => ∃ value, Unified.writeByte resolve descriptor candidate node loc = some value := by
  cases hu with
  | descriptor hc ho => exact ⟨_,Access.descriptor_read (resolve := resolve) (descriptor := descriptor) hc ho⟩
  | tmaRead hl hv => exact ⟨_,Access.tensor_read (resolve := resolve) (descriptor := descriptor) hl hv⟩
  | tmaWrite hl hv => exact ⟨_,Access.tensor_write (resolve := resolve) (descriptor := descriptor) hl hv⟩
  | nativeRead hr => exact ⟨_,Unified.native_read_byte (resolve := resolve) (descriptor := descriptor) hr⟩

theorem read_write_present {candidate id offset loc} (hl : Tma.readLocation candidate id offset = some loc) :
    Tma.WritePresent candidate id offset := by
  cases hc : Tma.copyAt candidate id with
  | none => simp [Tma.readLocation,hc] at hl
  | some op =>
    have hs : Tma.sourceByte op.descriptor op.coordinates offset = some loc := by simpa only [Tma.readLocation,hc,Option.bind_some] using hl
    simp only [Tma.WritePresent,hc]
    exact (Tma.source_byte_some hs).1

theorem location_write_present {resolve candidate id offset loc} (hl : Tma.writeLocation resolve candidate id offset = some loc) :
    Tma.WritePresent candidate id offset := by
  cases hc : Tma.copyAt candidate id with
  | none => simp [Tma.writeLocation,hc] at hl
  | some op =>
    simp only [Tma.writeLocation,hc,Option.bind_some] at hl
    simp only [Tma.WritePresent,hc]
    split at hl
    · assumption
    · cases hl

theorem source_transfer_byte_exists {candidate code launch id op offset}
    (hw : Unified.WellFormed code launch candidate) (hc : Tma.copyAt candidate.view id = some op) (ho : offset < op.descriptor.bytes) :
    ∃ value, Tma.transferByte candidate.view id offset = some value := by
  have hlen := Unified.tma_copy_payload_length hw hc
  have hb : offset < op.payload.length := by omega
  exact ⟨op.payload[offset],by simp [Tma.transferByte,hc,hb]⟩

theorem source_tma_read_use {resolve descriptor candidate code launch id offset loc}
    (hw : Unified.WellFormed code launch candidate) (hl : Tma.readLocation candidate.view id offset = some loc) :
    Use resolve descriptor candidate (.tma id) (.base (.read id offset)) (.base (.tma (.read id offset))) loc .read := by
  cases hc : Tma.copyAt candidate.view id with
  | none => simp [Tma.readLocation,hc] at hl
  | some op =>
    have hb : offset < op.descriptor.bytes := by simpa only [Tma.WritePresent,hc] using read_write_present hl
    obtain ⟨value,hv⟩ := source_transfer_byte_exists hw hc hb
    exact .tmaRead hl hv

theorem source_tma_write_use {resolve descriptor candidate code launch id offset loc}
    (hw : Unified.WellFormed code launch candidate) (hl : Tma.writeLocation resolve candidate.view id offset = some loc) :
    Use resolve descriptor candidate (.tma id) (.base (.write id offset)) (.base (.tma (.write id offset))) loc .write := by
  cases hc : Tma.copyAt candidate.view id with
  | none => simp [Tma.writeLocation,hc] at hl
  | some op =>
    have hb : offset < op.descriptor.bytes := by simpa only [Tma.WritePresent,hc] using location_write_present hl
    obtain ⟨value,hv⟩ := source_transfer_byte_exists hw hc hb
    exact .tmaWrite hl hv

theorem tma_use_before_notice {block resolve descriptor candidate id control node loc mode op}
    {histories : Location → List Tma.Entry}
    (hu : Use resolve descriptor candidate (.tma id) control node loc mode)
    (hc : Tma.copyAt candidate.view id = some op) (hp : 0 < op.descriptor.bytes) :
    Ptx.Event.Path (Unified.ControlEdge block candidate histories) control (.base (.notify id)) := by
  cases hu with
  | descriptor actual ho =>
    have hw : Tma.WritePresent candidate.view id 0 := by simp only [Tma.WritePresent,hc]; exact hp
    exact .trans (.single (Unified.base_control_edge (.inr (.inr (.inl (.descriptorWrite hw))))))
      (.single (Unified.base_control_edge (.inr (.inr (.inl (.complete hw))))))
  | tmaRead hl hv =>
    have hr := congrArg Option.isSome hl
    change _ = true at hr
    exact .trans (.single (Unified.base_control_edge (.inr (.inr (.inl (.data hr))))))
      (.single (Unified.base_control_edge (.inr (.inr (.inl (.complete (read_write_present hl)))))))
  | tmaWrite hl hv => exact .single (Unified.base_control_edge (.inr (.inr (.inl (.complete (location_write_present hl))))))

theorem completed_monotone {resolve candidate histories cluster before after work}
    (hm : ∀ node, before node → after node) (hc : Completed resolve candidate histories cluster before work) :
    Completed resolve candidate histories cluster after work := by
  cases hc with
  | tma hcopy hp ho hd => exact .tma hcopy hp ho (hm _ hd)
  | native hc hd => exact .native hc (hm _ hd)
  | kernel hc hd => exact .kernel hc (fun node hn => hm node (hd node hn))

theorem native_use_before_wait {block resolve descriptor candidate histories issue wait control node loc mode}
    (hu : Use resolve descriptor candidate (.native issue) control node loc mode)
    (hc : Unified.WgmmaCompletedAt candidate issue wait) :
    Unified.ControlEdge block candidate histories control (.base (.source wait)) := by
  cases hu with
  | nativeRead hr => exact .inr (.inr (.inr (.inr hc)))

theorem completed_use_done {block resolve descriptor candidate histories cluster done work control node loc mode}
    (hclosed : Closed block candidate histories done)
    (hc : Completed resolve candidate histories cluster done work)
    (hu : Use resolve descriptor candidate work control node loc mode) : done control := by
  cases hc with
  | tma hcopy hpositive hobservation hdone =>
    have hnotice : done (.base (.notify _)) := hclosed _ _
      (Unified.base_control_edge (.inr (.inr (.inr (Access.observed_resource_edge hobservation))))) hdone
    exact closed_path hclosed (tma_use_before_notice hu hcopy hpositive) hnotice
  | native hcompletion hdone =>
    exact hclosed _ _ (native_use_before_wait hu hcompletion) hdone
  | kernel hc hd => cases hu

theorem pending_use_not_completed {block resolve descriptor candidate histories cluster done work control node loc mode}
    (hclosed : Closed block candidate histories done)
    (hu : Use resolve descriptor candidate work control node loc mode) (hp : ¬done control) :
    ¬Completed resolve candidate histories cluster done work := fun hc => hp (completed_use_done hclosed hc hu)

theorem reached_completed_use_done {block resolve descriptor candidate histories cluster done work control node loc mode}
    (hr : Reached block candidate histories done)
    (hc : Completed resolve candidate histories cluster done work)
    (hu : Use resolve descriptor candidate work control node loc mode) : done control :=
  completed_use_done (reached_valid hr).1 hc hu

end
end Ptx.Hopper.Progress
