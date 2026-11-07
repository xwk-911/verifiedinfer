import Ptx.Tests.TmaPublication

/-! Synthetic protocol histories test phase/lifetime discrimination; only the
separately identified source prefixes below are actual source-run witnesses.
These histories are not advertised as full allowed kernel executions. -/
namespace Ptx.TmaPhaseTests
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def eid := TmaTests.eid
def second : Tma.CopyId := ⟨eid 100⟩
def third : Tma.CopyId := ⟨eid 101⟩
def first : List Tma.Entry := TmaPublicationTests.history.take 4
def two : List Tma.Entry := first ++ [⟨.source (eid 8),.arriveExpectTx 32⟩,
  ⟨.notification second,.completeTx 32⟩,⟨.source (eid 9),.tryWaitParity 1 true⟩]
def three : List Tma.Entry := two ++ [⟨.source (eid 10),.arriveExpectTx 32⟩,
  ⟨.notification third,.completeTx 32⟩,⟨.source (eid 11),.tryWaitParity 0 true⟩]
def restarted : List Tma.Entry := first ++ [⟨.source (eid 8),.inval⟩,⟨.source (eid 9),.init 1⟩,
  ⟨.source (eid 10),.arriveExpectTx 32⟩,⟨.notification second,.completeTx 32⟩,
  ⟨.source (eid 11),.tryWaitParity 0 true⟩]
def explicitOnly : List Tma.Entry :=
  [⟨.source (eid 0),.init 1⟩,⟨.source (eid 1),.arriveExpectTx 32⟩,
   ⟨.source (eid 2),.completeTx 32⟩,⟨.source (eid 3),.tryWaitParity 0 true⟩]
def falseWait : List Tma.Entry := first.take 3 ++ [⟨.source (eid 4),.tryWaitParity 0 false⟩]

theorem two_protocol : Mbarrier.Admitted (two.map Tma.Entry.operation) := ⟨some ⟨2,1,1,0,true⟩,by decide⟩
theorem three_protocol : Mbarrier.Admitted (three.map Tma.Entry.operation) := ⟨some ⟨3,1,1,0,true⟩,by decide⟩
theorem restarted_protocol : Mbarrier.Admitted (restarted.map Tma.Entry.operation) := ⟨some ⟨1,1,1,0,true⟩,by decide⟩
theorem second_observed : Tma.observation two 5 6 = some (second,eid 9) := by decide
theorem third_observed : Tma.observation three 8 9 = some (third,eid 11) := by decide
theorem old_not_latest : Tma.observation three 2 9 = none := by decide
theorem same_parity_different_completed_phase :
    Tma.stampBefore three 2 = some ⟨1,0⟩ ∧ Tma.stampBefore three 9 = some ⟨1,3⟩ := by decide
theorem reinitialized_same_phase_numbers :
    Tma.stampBefore restarted 2 = some ⟨1,0⟩ ∧ Tma.stampBefore restarted 8 = some ⟨2,1⟩ := by decide
theorem reinitialized_old_observation_rejected : Tma.observation restarted 2 8 = none :=
  Tma.observation_no_reinitialized_object (by decide)
theorem reinitialized_new_observation_accepted : Tma.observation restarted 7 8 = some (second,eid 11) := by decide
theorem explicit_protocol : Mbarrier.Admitted (explicitOnly.map Tma.Entry.operation) := ⟨some ⟨1,1,1,0,true⟩,by decide⟩
theorem explicit_completion_does_not_publish_tma : Tma.observation explicitOnly 2 3 = none := by decide
theorem false_wait_not_observation : Tma.observation falseWait 2 3 = none := by decide
theorem backwards_observation_rejected : Tma.observation first 2 1 = none := by decide

def transfer : TmaCopy := {TmaTests.copy with queryBase := 1}
def reuseCode : List Hopper.Instr := [
  .ampere (.scalar (.integer (.load .shared "%r" ⟨.imm 16,0⟩))),
  .proxyFenceAsyncShared,
  .tmaLoad2D ⟨.imm 16,0⟩ (.imm 4096) (.imm 2) (.imm 1) ⟨.imm 0,0⟩]
def prefixDone : State := {scalar := {core := {thread := {pc := 3,regs := [("%r",0)]},queries := 3}}}
def reuseEvents : List Hopper.Event := [
  .ampere (.ordinary (.read ⟨.shared .zero,16⟩ (TmaPublicationTests.bytes 0))),
  .proxyFenceAsyncShared .zero,.tmaIssue transfer]
def reuseTrace : ThreadTrace := ⟨TmaTests.id,TmaPublicationTests.oracle 0,3,prefixDone,reuseEvents⟩
def reuseCandidate : Candidate := ⟨[reuseTrace]⟩
def nextCopy : Tma.CopyId := ⟨eid 2⟩
def noFenceCode : List Hopper.Instr := reuseCode.take 1 ++ reuseCode.drop 2
def noFenceTrace : ThreadTrace := {reuseTrace with count := 2,final := {prefixDone with scalar := {prefixDone.scalar with core := {
  prefixDone.scalar.core with thread := {prefixDone.scalar.core.thread with pc := 2}}}},events := reuseEvents.take 1 ++ reuseEvents.drop 2}
def noFenceCandidate : Candidate := ⟨[noFenceTrace]⟩

theorem protected_actual_source_prefix : Produced reuseCode [] .one reuseTrace := by rfl
theorem missing_fence_actual_source_prefix : Produced noFenceCode [] .one noFenceTrace := by rfl
theorem fence_protects_future_byte : Access.Protected Tma.localShared reuseCandidate
    (.tma (.source (eid 0))) (.tma (.write nextCopy 0)) ⟨.shared .zero,16⟩ :=
  ⟨eid 1,by rfl,⟨by rfl,by rfl,rfl,by decide⟩,⟨by rfl,by rfl,rfl,by decide⟩,by rfl,rfl⟩
theorem missing_fence_not_protected : ¬ Access.Protected Tma.localShared noFenceCandidate
    (.tma (.source (eid 0))) (.tma (.write ⟨eid 1⟩ 0)) ⟨.shared .zero,16⟩ := by
  rintro ⟨fence,hf,_⟩
  obtain ⟨t,ht,_,hg⟩ := Ptx.Hopper.eventAt_trace hf
  have ht : t = noFenceTrace := List.mem_singleton.mp ht
  subst t
  have hm := List.mem_of_getElem? hg
  simp [noFenceTrace,reuseEvents] at hm

end
end Ptx.TmaPhaseTests
