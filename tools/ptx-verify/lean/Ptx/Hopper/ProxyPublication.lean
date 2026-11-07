import Ptx.Hopper.TmaObservation
import Ptx.Hopper.InputValues

/-! Directional async-to-generic publication and generic-to-async shared-memory
protection. Resource/control order is not reused wholesale as memory causality.
Only a transfer's own byte writes are published by its observed completion.
Scope membership is explicit; full launch/cluster/CTA/ISA admission is separate.
The guarded visibility rules below are memory-fragment rules, not a complete
proxy-aware PTX consistency/observer/race model. -/
namespace Ptx.Hopper.Access
open Ptx.ISA
noncomputable section

/-- The current source wait is acquire.cta. Notification release scope is
cluster; an eventual launch adapter must supply checked cluster membership. -/
abbrev ClusterScope := ThreadId → ThreadId → Prop

def CompletionObserved (resolve : Tma.SharedResolver) (c : Candidate)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope)
    (id : Tma.CopyId) (wait : Ptx.Event.EventId) : Prop :=
  cluster id.issue.thread wait.thread ∧ ∃ loc noticeIndex waitIndex,
    loc.space = .shared wait.thread.cta ∧
    Tma.HistoryValid resolve c loc (histories loc) ∧
    Tma.observation (histories loc) noticeIndex waitIndex = some (id,wait)

def GenericEdge (c : Candidate) (a b : Ptx.Event.EventId) : Prop :=
  Hopper.ProgramOrder c a b ∨ Hopper.CTAControl c a b
def GenericAfter (c : Candidate) := Ptx.Event.Path (GenericEdge c)

/-- These are byte-specific edges, not releases of arbitrary issuer prefixes. -/
def Published (resolve : Tma.SharedResolver) (c : Candidate)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope)
    (writer read : Node) (loc : Location) : Prop :=
  match writer,read with
  | .tma (.write id offset),.tma (.source event) => ∃ wait,
      Tma.writeLocation resolve c id offset = some loc ∧
      loc.space = .shared wait.thread.cta ∧ CompletionObserved resolve c histories cluster id wait ∧
      GenericAfter c wait event
  | _,_ => False

/-- A same-thread shared proxy fence protects prior generic accesses against
the subsequent TMA access. Cooperative readers need an additional checked CTA
publication/participation argument; it is not inferred from resource order. -/
def Protected (resolve : Tma.SharedResolver) (c : Candidate)
    (read writer : Node) (loc : Location) : Prop :=
  match read,writer with
  | .tma (.source event),.tma (.write id offset) => ∃ fence,
      c.eventAt fence = some (.proxyFenceAsyncShared event.thread.cta) ∧
      Hopper.ProgramOrder c event fence ∧ Hopper.ProgramOrder c fence id.issue ∧
      Tma.writeLocation resolve c id offset = some loc ∧ loc.space = .shared event.thread.cta
  | _,_ => False

theorem generic_program_after {c a b} (h : Hopper.ProgramOrder c a b) : GenericAfter c a b := .single (.inl h)
theorem generic_cta_after {c a b} (h : Hopper.CTAControl c a b) : GenericAfter c a b := .single (.inr h)

theorem generic_after_control {c histories a b} (h : GenericAfter c a b) :
    Ptx.Event.Path (Tma.ControlEdge c histories) (.source a) (.source b) := by
  induction h with
  | single he => exact .single (he.elim (fun hp => .inl hp) (fun hc => .inr (.inl hc)))
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem observed_resource_edge {resolve c histories cluster id wait}
    (h : CompletionObserved resolve c histories cluster id wait) :
    Tma.ResourceEdge histories (.notify id) (.source wait) := by
  obtain ⟨_,loc,ni,wi,_,hv,ho⟩ := h
  obtain ⟨count,parity,_,_,hn,hw,_⟩ := Tma.observation_shape ho
  exact ⟨loc,_,List.mem_of_getElem? hn,_,List.mem_of_getElem? hw,Tma.observation_before hv ho,rfl,rfl⟩

theorem published_control_path {resolve c histories cluster id offset event loc}
    (h : Published resolve c histories cluster (.tma (.write id offset)) (.tma (.source event)) loc) :
    Ptx.Event.Path (Tma.ControlEdge c histories) (.write id offset) (.source event) := by
  obtain ⟨wait,hl,_,hc,ha⟩ := h
  have hp : Tma.WritePresent c id offset := by
    cases hh : Tma.copyAt c id with
    | none => simp [Tma.writeLocation,hh] at hl
    | some op =>
      unfold Tma.WritePresent
      rw [hh]
      simp only [Tma.writeLocation,hh,Option.bind_some] at hl
      split at hl
      · assumption
      · cases hl
  exact .trans (.single (.inr (.inr (.inl (.complete hp)))))
    (.trans (.single (.inr (.inr (.inr (observed_resource_edge hc))))) (generic_after_control ha))

theorem observed_has_actual_notification {resolve c histories cluster id wait}
    (h : CompletionObserved resolve c histories cluster id wait) :
    ∃ loc copy parity before after noticeIndex waitIndex,
      Tma.copyAt c id = some copy ∧ loc = resolve id.issue.thread copy.barrier ∧
      c.barrierAt wait = some ⟨loc,.tryWaitParity parity true⟩ ∧
      Mbarrier.run none (((histories loc).map Tma.Entry.operation).take noticeIndex) = some (some before) ∧
      Mbarrier.run none (((histories loc).map Tma.Entry.operation).take waitIndex) = some (some after) ∧
      Tma.lifetimeBefore (histories loc) noticeIndex = Tma.lifetimeBefore (histories loc) waitIndex ∧
      before.phase+1 = after.phase ∧ 0 < after.phase ∧ parity%2 ≠ after.phase%2 := by
  obtain ⟨_,loc,ni,wi,_,hv,ho⟩ := h
  obtain ⟨copy,parity,before,after,hc,hl,hw,hb,ha,he,hp,hpos,hpar⟩ := Tma.observation_actual_phase hv ho
  exact ⟨loc,copy,parity,before,after,ni,wi,hc,hl,hw,hb,ha,he,hp,hpos,hpar⟩

theorem published_requires_observed_completion {resolve c histories cluster id offset event loc}
    (h : Published resolve c histories cluster (.tma (.write id offset)) (.tma (.source event)) loc) :
    ∃ wait, CompletionObserved resolve c histories cluster id wait ∧ GenericAfter c wait event := by
  obtain ⟨wait,_,_,hc,ha⟩ := h
  exact ⟨wait,hc,ha⟩

theorem published_not_issuer_prefix (resolve c histories cluster issuer read loc) :
    ¬ Published resolve c histories cluster (.tma (.source issuer)) read loc := by
  cases read <;> simp [Published]

theorem published_only_async_to_generic {resolve c histories cluster writer read loc}
    (h : Published resolve c histories cluster writer read loc) : writer.proxy = .async ∧ read.proxy = .generic := by
  cases writer with
  | copyRead _ | copyWrite _ => cases h
  | tma w =>
    cases w <;> cases read with
    | copyRead _ | copyWrite _ => cases h
    | tma r => cases r <;> simp_all [Published,Node.proxy,Tma.Node.proxy]

theorem protected_only_generic_to_async {resolve c read writer loc}
    (h : Protected resolve c read writer loc) : read.proxy = .generic ∧ writer.proxy = .async := by
  cases read with
  | copyRead _ | copyWrite _ => cases h
  | tma r =>
    cases r <;> cases writer with
    | copyRead _ | copyWrite _ => cases h
    | tma w => cases w <;> simp_all [Protected,Node.proxy,Tma.Node.proxy]

/-- Minimal rf/co fragment needed by a consumer visibility argument. Coherence
initialization, no-stale publication and no-future protection are separate from
read-value agreement. Eligibility must later be derived by full race admission. -/
structure VisibilityConditions (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (initial : ProxyMemory) (eligible : Node → Location → Prop) (rf : ReadsFrom)
    (co : Location → Option Node → Option Node → Prop)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) : Prop where
  agreement : ReadAgreement resolve descriptor c initial eligible rf
  initialization : ∀ writer loc value, writeByte resolve descriptor c writer loc = some value → co loc none (some writer)
  noStale : ∀ writer read loc vw vr, eligible read loc →
    writeByte resolve descriptor c writer loc = some vw → readByte resolve descriptor c read loc = some vr →
    Published resolve c histories cluster writer read loc → ¬ co loc (rf read loc) (some writer)
  noFuture : ∀ read writer loc vr vw, eligible read loc →
    readByte resolve descriptor c read loc = some vr → writeByte resolve descriptor c writer loc = some vw →
    Protected resolve c read writer loc → rf read loc ≠ some writer

theorem published_unique_writer_source {resolve descriptor c initial eligible rf co histories cluster writer read loc vw vr}
    (hv : VisibilityConditions resolve descriptor c initial eligible rf co histories cluster)
    (he : eligible read loc) (hw : writeByte resolve descriptor c writer loc = some vw)
    (hr : readByte resolve descriptor c read loc = some vr) (hp : Published resolve c histories cluster writer read loc)
    (hu : ∀ other value, writeByte resolve descriptor c other loc = some value → other = writer) :
    rf read loc = some writer := by
  cases hs : rf read loc with
  | none => exact (hv.noStale writer read loc vw vr he hw hr hp (hs ▸ hv.initialization writer loc vw hw)).elim
  | some other =>
    have ha := hv.agreement read loc vr he hr
    have ho : writeByte resolve descriptor c other loc = some vr := by simpa [sourceValue,hs] using ha
    simpa only [hu other vr ho] using hs

theorem published_unique_writer_value {resolve descriptor c initial eligible rf co histories cluster writer read loc vw vr}
    (hv : VisibilityConditions resolve descriptor c initial eligible rf co histories cluster)
    (he : eligible read loc) (hw : writeByte resolve descriptor c writer loc = some vw)
    (hr : readByte resolve descriptor c read loc = some vr) (hp : Published resolve c histories cluster writer read loc)
    (hu : ∀ other value, writeByte resolve descriptor c other loc = some value → other = writer) : vr = vw := by
  have hs := published_unique_writer_source hv he hw hr hp hu
  have ha := hv.agreement read loc vr he hr
  rw [hs] at ha
  change writeByte resolve descriptor c writer loc = some vr at ha
  exact Option.some.inj (ha.symm.trans hw)

theorem protected_future_writer_excluded {resolve descriptor c initial eligible rf co histories cluster read writer loc vr vw}
    (hv : VisibilityConditions resolve descriptor c initial eligible rf co histories cluster)
    (he : eligible read loc) (hr : readByte resolve descriptor c read loc = some vr)
    (hw : writeByte resolve descriptor c writer loc = some vw) (hp : Protected resolve c read writer loc) :
    rf read loc ≠ some writer := hv.noFuture read writer loc vr vw he hr hw hp

/-- Repeated buffer writes are permitted. Earlier phases must be before the
selected writer in coherence; later phases must be protected against this read.
No chosen rf or desired load reply occurs in this classification premise. -/
theorem published_phase_writer_source {resolve descriptor c initial eligible rf co histories cluster writer read loc vw vr}
    (hv : VisibilityConditions resolve descriptor c initial eligible rf co histories cluster)
    (he : eligible read loc) (hw : writeByte resolve descriptor c writer loc = some vw)
    (hr : readByte resolve descriptor c read loc = some vr) (hp : Published resolve c histories cluster writer read loc)
    (hc : ∀ other value, writeByte resolve descriptor c other loc = some value →
      other = writer ∨ co loc (some other) (some writer) ∨ Protected resolve c read other loc) :
    rf read loc = some writer := by
  cases hs : rf read loc with
  | none => exact (hv.noStale writer read loc vw vr he hw hr hp (hs ▸ hv.initialization writer loc vw hw)).elim
  | some other =>
    have ha := hv.agreement read loc vr he hr
    have ho : writeByte resolve descriptor c other loc = some vr := by simpa [sourceValue,hs] using ha
    rcases hc other vr ho with hid | hbefore | hafter
    · simpa only [hid] using hs
    · exact (hv.noStale writer read loc vw vr he hw hr hp (hs ▸ hbefore)).elim
    · exact (hv.noFuture read other loc vr vr he hr ho hafter hs).elim

theorem published_phase_writer_value {resolve descriptor c initial eligible rf co histories cluster writer read loc vw vr}
    (hv : VisibilityConditions resolve descriptor c initial eligible rf co histories cluster)
    (he : eligible read loc) (hw : writeByte resolve descriptor c writer loc = some vw)
    (hr : readByte resolve descriptor c read loc = some vr) (hp : Published resolve c histories cluster writer read loc)
    (hc : ∀ other value, writeByte resolve descriptor c other loc = some value →
      other = writer ∨ co loc (some other) (some writer) ∨ Protected resolve c read other loc) : vr = vw := by
  have hs := published_phase_writer_source hv he hw hr hp hc
  have ha := hv.agreement read loc vr he hr
  rw [hs] at ha
  change writeByte resolve descriptor c writer loc = some vr at ha
  exact Option.some.inj (ha.symm.trans hw)

end
end Ptx.Hopper.Access
