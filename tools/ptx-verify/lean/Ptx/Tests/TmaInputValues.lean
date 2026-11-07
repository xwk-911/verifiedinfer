import Ptx.Hopper.InputValues
import Ptx.Tests.Tma

/-! Concrete independent read-fragment witness and adversarial combined-graph
checks. InputSites classifies the sites used by this fragment; it is not a claim
that full proxy-aware PTX eligibility/admission has already been established. -/
namespace Ptx.TmaInputTests
open Ptx.ISA Ptx.Hopper
open Ptx.TmaTests (view candidate operation copy)
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def initial : Access.ProxyMemory
  | .tensormap,loc => if loc.space = .global ∧ 4096 ≤ loc.address ∧ loc.address < 4096+128 then
      .tensorMapPart view (loc.address-4096) else .bits (byte 0)
  | _,loc => TmaTests.initial loc
def rf : Access.ReadsFrom := fun _ _ => none

def InputSites (node : Access.Node) (loc : Location) : Prop :=
  (∃ offset, offset < 128 ∧ node = .tma (.descriptor operation) ∧ loc = (⟨.global,4096⟩ : Location).add offset) ∨
  (∃ offset, Tma.readLocation candidate operation offset = some loc ∧ node = .tma (.read operation offset))

theorem stored : TensorMap.Stored (initial .tensormap) ⟨.global,4096⟩ view := by
  intro offset ho
  simp [initial,Location.add,show 4096+offset < 4224 by omega]

theorem only_copy {actual op} (hc : Tma.copyAt candidate actual = some op) : actual = operation ∧ op = copy := by
  have hm := Tma.copy_present_mem hc
  rw [TmaTests.copies_exact] at hm
  have hid := List.mem_singleton.mp hm
  subst actual
  exact ⟨rfl,Option.some.inj (hc.symm.trans TmaTests.copy_from_actual_issue)⟩

theorem no_ampere_event {event e} (he : candidate.eventAt event = some (.ampere e)) : False := by
  obtain ⟨t,ht,_,hg⟩ := Ptx.Hopper.eventAt_trace he
  have ht : t = TmaTests.trace := List.mem_singleton.mp ht
  subst t
  have hm := List.mem_of_getElem? hg
  simp [TmaTests.trace,TmaTests.events] at hm

theorem no_nonbulk (event : Ptx.Event.EventId) : Access.copyAt candidate event = none := by
  cases he : Access.copyAt candidate event with
  | none => rfl
  | some op =>
    obtain ⟨ordinal,hh⟩ := Access.nonbulk_has_actual_issue he
    exact (no_ampere_event hh).elim

theorem no_ordinary (event : Ptx.Event.EventId) :
    Access.kind Tma.localShared Access.globalDescriptor candidate (.tma (.source event)) = none := by
  cases he : candidate.eventAt event with
  | none => simp [Access.kind,he]
  | some e =>
    cases e with
    | ampere e => exact (no_ampere_event he).elim
    | tmaIssue _ | proxyFenceAsyncShared _ | barrier _ | wgmma _ => simp [Access.kind,he]

theorem global_immutable (address : Nat) : Access.Immutable Tma.localShared Access.globalDescriptor candidate ⟨.global,address⟩ := by
  intro writer
  cases writer with
  | copyRead issue | copyWrite issue => simp [Access.writeByte,Access.kind,no_nonbulk]
  | tma node =>
    cases node with
    | source event => simp [Access.writeByte,no_ordinary]
    | descriptor id => exact Access.descriptor_no_write _ _ _ _ _
    | read id offset => exact Access.tensor_read_no_write _ _ _ _ _ _
    | notify id => rfl
    | write id offset =>
      cases hc : Tma.copyAt candidate id <;> cases hb : Tma.transferByte candidate id offset <;>
        simp [Access.writeByte,Access.kind,Tma.writeLocation,Tma.localShared,hc,hb,Ptx.Event.Kind.writeByte,Ptx.Event.payloadByte]
      all_goals split_ifs <;> simp [Location.add,Ptx.Event.Kind.writeByte,Ptx.Event.payloadByte]

theorem agreement : Access.ReadAgreement Tma.localShared Access.globalDescriptor candidate initial InputSites rf := by
  intro read loc value he hr
  rcases he with ⟨offset,ho,rfl,rfl⟩ | ⟨offset,hl,rfl⟩
  · have hh := Access.descriptor_read (resolve := Tma.localShared) (descriptor := Access.globalDescriptor)
      TmaTests.copy_from_actual_issue ho
    have hv := Option.some.inj (hr.symm.trans hh)
    subst value
    simpa [Access.sourceValue,rf,Access.Node.proxy,Tma.Node.proxy,Access.globalDescriptor,TmaTests.copy,TmaTests.operation] using
      congrArg some (stored offset ho)
  · obtain ⟨op,hc,ho⟩ := Tma.read_has_copy (by rw [hl]; rfl)
    have hop : op = copy := (only_copy hc).2
    subst op
    have hp := TmaTests.payload_byte ⟨offset,ho⟩
    have hb : Tma.transferByte candidate operation offset = some (Tma.byteValue view TmaTests.coords TmaTests.initial offset) := by
      simpa [Tma.transferByte,TmaTests.copy_from_actual_issue,TmaTests.copy] using hp
    have hh := Access.tensor_read (resolve := Tma.localShared) (descriptor := Access.globalDescriptor) hl hb
    have hv := Option.some.inj (hr.symm.trans hh)
    have hs : Tma.sourceByte view TmaTests.coords offset = some loc := by
      simpa [Tma.readLocation,TmaTests.copy_from_actual_issue,TmaTests.copy] using hl
    rw [Tma.copied_byte hs] at hv
    simp [Access.sourceValue,rf,Access.Node.proxy,Tma.Node.proxy,initial,hv]

theorem descriptor_from_memory : Tma.DescriptorAgreement candidate TmaTests.maps := by
  apply Access.descriptor_agreement_from_memory agreement
  · intro actual op hc
    obtain ⟨rfl,rfl⟩ := only_copy hc
    exact ⟨view,rfl,stored⟩
  · intro actual op hc offset ho
    obtain ⟨rfl,rfl⟩ := only_copy hc
    exact .inl ⟨offset,ho,rfl,rfl⟩
  · intro actual op hc offset ho
    exact global_immutable _

theorem zero_fill : Access.ZeroFill candidate := by
  intro actual op hc offset ho hs
  obtain ⟨rfl,rfl⟩ := only_copy hc
  have all : ∀ i : Fin 32, (Tma.sourceByte view TmaTests.coords i.val).isSome = true := by decide
  have hh := all ⟨offset,ho⟩
  change Tma.sourceByte view TmaTests.coords offset = none at hs
  rw [hs] at hh
  cases hh

theorem payload_from_memory : Tma.PayloadAgreement candidate TmaTests.initial := by
  apply Access.payload_agreement_from_memory TmaTests.formed agreement zero_fill
  · intro actual offset loc hl
    obtain ⟨op,hc,_⟩ := Tma.read_has_copy (by rw [hl]; rfl)
    obtain ⟨rfl,_⟩ := only_copy hc
    exact .inr ⟨offset,hl,rfl⟩
  · intro actual offset loc hl
    obtain ⟨op,hc,_⟩ := Tma.read_has_copy (by rw [hl]; rfl)
    have hs : Tma.sourceByte op.descriptor op.coordinates offset = some loc := by
      simpa [Tma.readLocation,hc] using hl
    have hspace := (Tma.source_byte_some hs).2.2.1
    cases loc with | mk space address => cases hspace; exact global_immutable address

/-- Deliberately malformed source candidates are used only to test inventory
preservation, never advertised as source-produced or legal executions. -/
def ordinaryOverwrite : Candidate := ⟨[{TmaTests.trace with events := [.ampere (.ordinary (.write ⟨.global,196⟩ [.bits (byte 7)]))]}]⟩
def nonbulkOverwrite : Candidate := ⟨[{TmaTests.trace with events := [.ampere (.issue 0 ⟨.ca,0,⟨.global,900⟩,⟨.shared .zero,196⟩,List.replicate 4 (.bits (byte 9))⟩)]}]⟩

theorem ordinary_write_preserved : Access.writeByte Tma.localShared Access.globalDescriptor ordinaryOverwrite
    (.tma (.source (TmaTests.eid 0))) ⟨.global,196⟩ = some (.bits (byte 7)) := by rfl
theorem nonbulk_write_preserved : Access.writeByte Tma.localShared Access.globalDescriptor nonbulkOverwrite
    (.copyWrite (TmaTests.eid 0)) ⟨.shared .zero,196⟩ = some (.bits (byte 9)) := by rfl
theorem ordinary_overwrite_invalidates_immutability : ¬ Access.Immutable Tma.localShared Access.globalDescriptor ordinaryOverwrite ⟨.global,196⟩ := by
  intro h; exact Access.immutable_excludes_actual_write h ordinary_write_preserved
theorem nonbulk_overwrite_invalidates_immutability : ¬ Access.Immutable Tma.localShared Access.globalDescriptor nonbulkOverwrite ⟨.shared .zero,196⟩ := by
  intro h; exact Access.immutable_excludes_actual_write h nonbulk_write_preserved

def rmwOverwrite : Candidate := ⟨[{TmaTests.trace with events := [.ampere (.ordinary (.rmw .gpu ⟨.global,196⟩
  ⟨List.replicate 4 (.bits (byte 0)),List.replicate 4 (.bits (byte 7)),by rfl⟩))]}]⟩
theorem rmw_read_preserved : Access.readByte Tma.localShared Access.globalDescriptor rmwOverwrite
    (.tma (.source (TmaTests.eid 0))) ⟨.global,196⟩ = some (.bits (byte 0)) := by rfl
theorem rmw_write_preserved : Access.writeByte Tma.localShared Access.globalDescriptor rmwOverwrite
    (.tma (.source (TmaTests.eid 0))) ⟨.global,196⟩ = some (.bits (byte 7)) := by rfl
theorem rmw_invalidates_immutability : ¬ Access.Immutable Tma.localShared Access.globalDescriptor rmwOverwrite ⟨.global,196⟩ := by
  intro h; exact Access.immutable_excludes_actual_write h rmw_write_preserved

theorem proxy_views_are_separate : initial .generic ⟨.global,4096⟩ = .bits (byte 0) ∧
    initial .tensormap ⟨.global,4096⟩ = .tensorMapPart view 0 := by constructor <;> rfl

theorem wrong_payload_fails_read_agreement :
    ¬ Access.ReadAgreement Tma.localShared Access.globalDescriptor TmaTests.badCandidate initial InputSites rf := by
  intro h
  have he : InputSites (.tma (.read operation 0)) ⟨.global,196⟩ := .inr ⟨0,by rfl,rfl⟩
  have hh := h (.tma (.read operation 0)) ⟨.global,196⟩ (.bits (byte 0)) he (by rfl)
  change some (Symbolic.Byte.bits (byte 196)) = some (Symbolic.Byte.bits (byte 0)) at hh
  exact (by decide : byte 196 ≠ byte 0) (Symbolic.Byte.bits.inj (Option.some.inj hh))

def wrongView : Tma.Descriptor2D := {view with base := 256}
def wrongCopy : TmaCopy := {copy with descriptor := wrongView}
def wrongTrace : ThreadTrace := {TmaTests.trace with
  oracle := {TmaTests.oracle with descriptor := fun _ => wrongView}
  events := [.barrier ⟨TmaTests.loc,.init 1⟩,.proxyFenceAsyncShared .zero,
    .barrier ⟨TmaTests.loc,.arriveExpectTx 32⟩,.tmaIssue wrongCopy,
    .barrier ⟨TmaTests.loc,.tryWaitParity 0 true⟩,.barrier ⟨TmaTests.loc,.inval⟩]
}
def wrongCandidate : Candidate := ⟨[wrongTrace]⟩

theorem wrong_descriptor_source_returns : Produced Generated.hopper_tma_copy.program TmaTests.ctx.params .one wrongTrace := by rfl
theorem wrong_descriptor_keeps_byte_count : wrongView.bytes = view.bytes := by decide
theorem wrong_descriptor_fails_read_agreement :
    ¬ Access.ReadAgreement Tma.localShared Access.globalDescriptor wrongCandidate initial InputSites rf := by
  intro h
  have he : InputSites (.tma (.descriptor operation)) ⟨.global,4096⟩ := .inl ⟨0,by decide,rfl,rfl⟩
  have hh := h (.tma (.descriptor operation)) ⟨.global,4096⟩ (.tensorMapPart wrongView 0) he (by rfl)
  change some (Symbolic.Byte.tensorMapPart view 0) = some (.tensorMapPart wrongView 0) at hh
  have hv := (Symbolic.Byte.tensorMapPart.inj (Option.some.inj hh)).1
  have hb := congrArg TensorMap.Descriptor2D.base hv
  exact (by decide : (128 : Nat) ≠ 256) hb

def zeroCoords : Tma.Coordinates := ⟨-1,1⟩
def zeroPayload : List Symbolic.Byte := List.ofFn (fun offset : Fin 32 => Tma.byteValue view zeroCoords TmaTests.initial offset.val)
def zeroCopy : TmaCopy := {copy with coordinates := zeroCoords,payload := zeroPayload}
def zeroCode : List Hopper.Instr := [.tmaLoad2D ⟨.imm 16,0⟩ (.imm 4096) (.imm 4294967295) (.imm 1) ⟨.imm 0,0⟩]
def zeroOracle : Oracle := {TmaTests.oracle with tmaBytes := fun _ => zeroPayload}
def zeroTrace : ThreadTrace := ⟨TmaTests.id,zeroOracle,1,(issueTma {} zeroCopy).1,[.tmaIssue zeroCopy]⟩
def zeroCandidate : Candidate := ⟨[zeroTrace]⟩
def zeroOperation : Tma.CopyId := ⟨TmaTests.eid 0⟩

theorem oob_actual_source : Produced zeroCode [] .one zeroTrace := by rfl
theorem oob_no_read : Tma.readLocation zeroCandidate zeroOperation 0 = none := by decide
theorem oob_has_destination : Tma.writeLocation Tma.localShared zeroCandidate zeroOperation 0 = some ⟨.shared .zero,16⟩ := by decide
theorem oob_destination_is_zero : Access.writeByte Tma.localShared Access.globalDescriptor zeroCandidate
    (.tma (.write zeroOperation 0)) ⟨.shared .zero,16⟩ = some (.bits (byte 0)) := by rfl
theorem oob_zero_fill_legal : Access.ZeroFill zeroCandidate := by
  intro actual op hc offset ho hs
  have hm := Tma.copy_present_mem hc
  have hx : Tma.copies zeroCandidate = [zeroOperation] := by rfl
  rw [hx] at hm
  have hid := List.mem_singleton.mp hm
  subst actual
  have hop : op = zeroCopy := Option.some.inj (hc.symm.trans (show Tma.copyAt zeroCandidate zeroOperation = some zeroCopy by rfl))
  subst op
  have all : ∀ i : Fin 32, zeroPayload[i.val]? = some (Tma.byteValue view zeroCoords TmaTests.initial i.val) := by
    intro i; fin_cases i <;> rfl
  have hp := all ⟨offset,ho⟩
  change Tma.sourceByte view zeroCoords offset = none at hs
  simpa [Tma.byteValue,hs,zeroCopy] using hp

/-- Same source instruction and byte count, but an illegal OOB fill value.
Read agreement cannot detect this: there is no memory read at the OOB byte. -/
def badZeroCopy : TmaCopy := {zeroCopy with payload := List.replicate 32 (.bits (byte 7))}
def badZeroTrace : ThreadTrace := {zeroTrace with
  oracle := {zeroOracle with tmaBytes := fun _ => badZeroCopy.payload}
  final := (issueTma {} badZeroCopy).1
  events := [.tmaIssue badZeroCopy]
}
def badZeroCandidate : Candidate := ⟨[badZeroTrace]⟩
theorem bad_oob_actual_source : Produced zeroCode [] .one badZeroTrace := by rfl
theorem bad_oob_fill_rejected : ¬ Access.ZeroFill badZeroCandidate := by
  intro h
  have hh := h zeroOperation badZeroCopy (by rfl) 0 (by decide) (by decide)
  change some (Symbolic.Byte.bits (byte 7)) = some (.bits (byte 0)) at hh
  exact (by decide : byte 7 ≠ byte 0) (Symbolic.Byte.bits.inj (Option.some.inj hh))

end
end Ptx.TmaInputTests
