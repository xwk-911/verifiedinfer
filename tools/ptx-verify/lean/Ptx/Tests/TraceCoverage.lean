import Ptx.Kernels.BarrierPublishUniversal
import Ptx.Kernels.CopyEvent

/-! Regression theorems for trace authenticity and contract non-vacuity. These
do not replace the universally quantified kernel proofs or close the external
allocation, observer-embedding and GPU execution boundaries. -/
namespace Ptx.TraceCoverageTests
open Ptx Ptx.ISA Ptx.Event Ptx.BarrierPublish

theorem forged_count_rejected (base value answer n : Nat) (hn : n ≠ 10) :
    ¬ ThreadTrace.Produced code (params base value) {consumer base value answer with count := n} := by
  intro hp
  have hs := consumer_trace_shape hp rfl rfl
  exact hn hs.1

theorem forged_store_rejected (base value answer : Nat) :
    ¬ ThreadTrace.Produced code (params base value)
      {consumer base value answer with events := (consumer base value answer).events ++
        [.write ⟨.global, 4096⟩ (bytes answer)]} := by
  intro hp
  have hs := consumer_trace_shape hp rfl rfl
  have hlen := congrArg List.length hs.2.2
  change (4 : Nat) = 3 at hlen
  contradiction

def stopped (base value answer : Nat) : Candidate := {
  traces := [{producer base value with final := { (producer base value).final with
    thread := { (producer base value).final.thread with status := .running } }}, consumer base value answer]
}

theorem stopped_same_events (base value answer : Nat) : SameEvents (stopped base value answer) (graph base value answer) := by
  funext event
  simp [Candidate.eventAt, stopped, graph, List.find?]
  split <;> rfl

theorem stopped_not_complete (base value answer : Nat) : ¬ (stopped base value answer).Complete := by
  intro hd
  have h := hd {producer base value with final := { (producer base value).final with
      thread := { (producer base value).final.thread with status := .running } }}
    (by simp [stopped])
  change Status.running = .done at h
  cases h

/-- Equal event views must not silently manufacture completion metadata. -/
theorem stopped_not_observable (base value answer : Nat) (initial : ByteMap)
    (sources : ReadsFrom) (order : Coherence) (o : Observation) :
    ¬ ObserverConditions (stopped base value answer) initial sources order o :=
  fun ho => stopped_not_complete base value answer ho.complete

theorem witnessed_contract (base value : Nat) (initial : ByteMap) :
    ∃ c sources order o, c.WellFormed code (launch base value initial) ∧
      GenericMemoryConditions c initial sources order ∧ ObserverConditions c initial sources order o ∧
      o.domain = wordDomain base ∧ outputWord o.output base = wrap 32 value := by
  have hp : Pre base value (launch base value initial) := ⟨rfl,rfl⟩
  obtain ⟨c,sources,order,o,hw,hc,ho,hd⟩ := nonvacuous base value _ hp
  exact ⟨c,sources,order,o,hw,hc,ho,hd,Event.triple_apply (correct base value) hp hw hc ho hd⟩

theorem masked_copy_has_no_events (c : CopyContract.Config) {tid : Nat} {t : ThreadTrace} {parameters : Bindings}
    (ht : tid < c.count) (hp : CopyContract.Params c parameters) (hzero : c.n = 0)
    (hid : t.id = CopyEvent.id tid) (hr : t.Produced CopyEvent.code parameters)
    (hd : t.final.thread.status = .done) : t.events = [] :=
  (CopyEvent.masked_trace_shape c ht hp (by omega) hid hr hd).2.2

end Ptx.TraceCoverageTests
