import Ptx.Iris.ByteContentsSequence

/-! A source-checked future-read invariant for constructing value scripts.
Initial-source bytes stay initial while their reader is pending; selected
writer bytes agree with that writer once it completes. The extra frontier
properties are source obligations, not assumptions of the PTX memory model.
-/
namespace Ptx.ByteContentsHeap
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

structure ReadFrontier (ctx : Context) (rf : Unified.ReadsFrom) : Prop where
  initialAfter : ∀ read loc value, ByteContents.readByte ctx.candidate read loc = some value → rf read loc = none →
    ∀ writer written, ByteContents.writeByte ctx.candidate writer loc = some written →
      Unified.memoryControlNode writer = Unified.memoryControlNode read ∨
        Ptx.Event.Path (Unified.ControlEdge ctx.block ctx.candidate ctx.histories) (Unified.memoryControlNode read) (Unified.memoryControlNode writer)
  writerBefore : ∀ read loc value, ByteContents.readByte ctx.candidate read loc = some value →
    ∀ writer, rf read loc = some writer →
      Ptx.Event.Path (Unified.ControlEdge ctx.block ctx.candidate ctx.histories) (Unified.memoryControlNode writer) (Unified.memoryControlNode read)
  writerPhase : ∀ read loc value, ByteContents.readByte ctx.candidate read loc = some value →
    ∀ writer, rf read loc = some writer → ∀ other written, ByteContents.writeByte ctx.candidate other loc = some written →
      Unified.memoryControlNode other = Unified.memoryControlNode read ∨ other = writer ∨
        Ptx.Event.Path (Unified.ControlEdge ctx.block ctx.candidate ctx.histories) (Unified.memoryControlNode other) (Unified.memoryControlNode writer) ∨
        Ptx.Event.Path (Unified.ControlEdge ctx.block ctx.candidate ctx.histories) (Unified.memoryControlNode read) (Unified.memoryControlNode other)

def FutureReads (ctx : Context) (initial : Unified.ProxyMemory) (rf : Unified.ReadsFrom) (state : State) : Prop :=
  ∀ read loc value, ByteContents.readByte ctx.candidate read loc = some value → ¬state.coupled.done (Unified.memoryControlNode read) →
    (rf read loc = none → ByteContents.valueAt state loc = some (initial read.proxy loc)) ∧
      (∀ writer, rf read loc = some writer → state.coupled.done (Unified.memoryControlNode writer) →
        ByteContents.valueAt state loc = ByteContents.writeByte ctx.candidate writer loc)

theorem ready_path_before {ctx : Context} {done node before}
    (hv : Closed ctx.block ctx.candidate ctx.histories done)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories done node)
    (hp : Ptx.Event.Path (Unified.ControlEdge ctx.block ctx.candidate ctx.histories) before node) : done before := by
  have hgo : ∀ left right, Ptx.Event.Path (Unified.ControlEdge ctx.block ctx.candidate ctx.histories) left right →
      (done right ∨ right = node) → done left := by
    intro left right path
    induction path with
    | single he =>
      rintro (hd | rfl)
      · exact hv _ _ he hd
      · exact hr.2.2 _ he
    | trans _ _ ih₁ ih₂ => exact fun h => ih₁ (.inl (ih₂ h))
  exact hgo _ _ hp (.inr rfl)

theorem future_realizes_at_ready {ctx : Context} {initial rf state memory}
    (hv : Valid ctx.block ctx.candidate ctx.histories state.coupled.done)
    (hf : ReadFrontier ctx rf) (hi : FutureReads ctx initial rf state)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories state.coupled.done (Unified.memoryControlNode memory)) :
    ByteContents.RealizesRF ctx.candidate initial rf memory state := by
  intro loc value hread
  have hh := hi memory loc value hread hr.2.1
  cases hs : rf memory loc with
  | none => exact hh.1 hs
  | some writer =>
    have hd := ready_path_before hv.1 hr (hf.writerBefore memory loc value hread writer hs)
    simpa only [hs,Unified.sourceValue,ByteContents.writeByte] using hh.2 writer hs hd

theorem future_reads_at_ready {ctx : Context} {initial rf co scope state memory}
    (hm : Unified.CausalConstraints Tma.localShared Access.globalDescriptor ctx.candidate initial rf co ctx.histories scope)
    (he : ∀ read loc value, ByteContents.readByte ctx.candidate read loc = some value →
      Unified.Eligible Tma.localShared Access.globalDescriptor ctx.candidate ctx.histories scope rf read loc)
    (hv : Valid ctx.block ctx.candidate ctx.histories state.coupled.done)
    (hf : ReadFrontier ctx rf) (hi : FutureReads ctx initial rf state)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories state.coupled.done (Unified.memoryControlNode memory)) :
    ByteContents.Reads ctx.candidate memory state :=
  ByteContents.reads_from_agreement hm (he memory) (future_realizes_at_ready hv hf hi hr)

theorem future_initial {ctx : Context} {initial rf state}
    (hd : ∀ node, ¬state.coupled.done node)
    (hi : ∀ read loc value, ByteContents.readByte ctx.candidate read loc = some value → rf read loc = none →
      ByteContents.valueAt state loc = some (initial read.proxy loc)) : FutureReads ctx initial rf state := by
  intro read loc value hread hp
  exact ⟨hi read loc value hread,fun _ _ hw => (hd _ hw).elim⟩

theorem future_action_preserved {ctx : Context} {initial rf co scope action state next}
    (hm : Unified.CausalConstraints Tma.localShared Access.globalDescriptor ctx.candidate initial rf co ctx.histories scope)
    (he : ∀ read loc value, ByteContents.readByte ctx.candidate read loc = some value →
      Unified.Eligible Tma.localShared Access.globalDescriptor ctx.candidate ctx.histories scope rf read loc)
    (hv : Valid ctx.block ctx.candidate ctx.histories state.coupled.done)
    (hf : ReadFrontier ctx rf) (hi : FutureReads ctx initial rf state)
    (hs : transition ctx action state = .ok next) : FutureReads ctx initial rf next := by
  intro read loc value hread hp
  have hpBefore : ¬state.coupled.done (Unified.memoryControlNode read) := fun hd => hp (action_done_monotone ctx hs _ hd)
  have hprev := hi read loc value hread hpBefore
  have hsource : ∀ writer, rf read loc = some writer → ByteContents.writeByte ctx.candidate writer loc = some value := by
    intro writer hrf
    have ha := hm.agreement read loc value (he read loc value hread) hread
    simpa only [hrf,Unified.sourceValue,ByteContents.writeByte] using ha
  cases action with
  | claim request =>
    obtain ⟨old,_,_,hn,_⟩ := ByteContents.claim_spec hs
    rw [ByteContents.claim_preserves_value hs loc]
    rw [hn]
    exact hprev
  | control node =>
    have hc := ByteContents.finishControl_spec hs
    constructor
    · intro hrf
      rw [ByteContents.finishControl_preserves_value hs loc]
      exact hprev.1 hrf
    · intro writer hrf hd
      rw [hc.2.1] at hd
      rcases hd with hd | hnew
      · rw [ByteContents.finishControl_preserves_value hs loc]
        exact hprev.2 writer hrf hd
      · have hw := hsource writer hrf
        have hn := (hc.1 writer hnew loc).2
        rw [hw] at hn
        cases hn
  | finish memory demands =>
    have hc := ByteContents.finish_spec hs
    have hvalid := action_valid ctx hv hs
    constructor
    · intro hrf
      have hn : ByteContents.writeByte ctx.candidate memory loc = none := by
        cases hw : ByteContents.writeByte ctx.candidate memory loc with
        | none => rfl
        | some written =>
          have hdone : next.coupled.done (Unified.memoryControlNode memory) := by rw [hc.2.2.1]; exact .inr rfl
          rcases hf.initialAfter read loc value hread hrf memory written hw with heq | hpath
          · rw [heq] at hdone
            exact (hp hdone).elim
          · exact (hp (closed_path hvalid.1 hpath hdone)).elim
      rw [ByteContents.finish_preserves_unwritten hs hn]
      exact hprev.1 hrf
    · intro writer hrf hd
      rw [hc.2.2.1] at hd
      rcases hd with hd | hnew
      · have hn : ByteContents.writeByte ctx.candidate memory loc = none := by
          cases hw : ByteContents.writeByte ctx.candidate memory loc with
          | none => rfl
          | some written =>
            have hdone : next.coupled.done (Unified.memoryControlNode memory) := by rw [hc.2.2.1]; exact .inr rfl
            rcases hf.writerPhase read loc value hread writer hrf memory written hw with hself | hwriter | hbefore | hafter
            · rw [hself] at hdone
              exact (hp hdone).elim
            · subst memory
              exact (hc.2.2.2.2.2.2.1 hd).elim
            · exact (hc.2.2.2.2.2.2.1 (closed_path hv.1 hbefore hd)).elim
            · exact (hp (closed_path hvalid.1 hafter hdone)).elim
        rw [ByteContents.finish_preserves_unwritten hs hn]
        exact hprev.2 writer hrf hd
      · have hw := hsource writer hrf
        have hn := hc.1.2 writer hnew ⟨loc,value,Or.inr hw⟩
        subst writer
        exact (ByteContents.finish_writes_byte hs hw).trans hw.symm

theorem future_run_preserved (ctx : Context) (actions : List Action) {initial rf co scope state next}
    (hm : Unified.CausalConstraints Tma.localShared Access.globalDescriptor ctx.candidate initial rf co ctx.histories scope)
    (he : ∀ read loc value, ByteContents.readByte ctx.candidate read loc = some value →
      Unified.Eligible Tma.localShared Access.globalDescriptor ctx.candidate ctx.histories scope rf read loc)
    (hv : Valid ctx.block ctx.candidate ctx.histories state.coupled.done)
    (hf : ReadFrontier ctx rf) (hi : FutureReads ctx initial rf state)
    (hr : IrisExecution.run (transition ctx) actions state = .ok next) : FutureReads ctx initial rf next := by
  induction actions generalizing state with
  | nil => cases hr; exact hi
  | cons head rest ih =>
    change (transition ctx head state).bind (fun mid => IrisExecution.run (transition ctx) rest mid) = .ok next at hr
    cases hs : transition ctx head state with
    | error error => simp [hs,Except.bind] at hr
    | ok mid =>
      exact ih (action_valid ctx hv hs) (future_action_preserved hm he hv hf hi hs) (by simpa only [hs,Except.bind] using hr)

end
end Ptx.ByteContentsHeap
