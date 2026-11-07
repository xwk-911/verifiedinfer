import Ptx.Kernels.SharedEventWitness
import Ptx.Tests.SharedSwap

/-! Universal rejection checks and finite execution comparisons for the same
SharedSwap AST. Finite computations do not replace `correct`/`nonvacuous`.
-/
namespace Ptx.SharedEventTests
open Ptx.ISA Ptx.Event Ptx.SharedEvent

def launch (c : SharedContract.Config) (fallback : ByteMap) : Launch := {
  geometry := geometry
  params := (SharedContract.initial c).params
  initial := Cells.encode c.before fallback
}

theorem launch_pre (c : SharedContract.Config) (fallback : ByteMap) : Pre c (launch c fallback) :=
  ⟨rfl,(SharedContract.initial_pre c).params,Cells.encode_represents _ _⟩

theorem witnessed_contract (c : SharedContract.Config) (fallback : ByteMap) :
    ∃ execution sources order o, execution.WellFormed code (launch c fallback) ∧
      GenericMemoryConditions execution (launch c fallback).initial sources order ∧
      ObserverConditions execution (launch c fallback).initial sources order o ∧
      o.domain = domain c ∧ BytePost c (launch c fallback).initial o.output := by
  have hp := launch_pre c fallback
  obtain ⟨execution,sources,order,o,hw,hc,ho,hd⟩ := nonvacuous c _ hp
  exact ⟨execution,sources,order,o,hw,hc,ho,hd,Event.triple_apply (correct c) hp hw hc ho hd⟩

theorem wrong_shared_read_rejected (c : SharedContract.Config) {l execution sources order tid answer offset}
    (hw : execution.WellFormed code l) (hd : execution.Complete) (hp : Pre c l)
    (ht : tid < 2) (hoffset : offset < 4)
    (hr : execution.eventAt ⟨id tid,4⟩ = some (.read (sharedLoc (SharedContract.other tid)) (payload answer)))
    (hwrong : wordByte answer offset ≠ wordByte (c.input (SharedContract.other tid)) offset) :
    ¬ GenericMemoryConditions execution l.initial sources order := by
  intro hc
  exact hwrong (shared_byte_correct c hw hd hp.1 hp.2.1 hp.2.2 hc ht hr offset hoffset)

/-- A stale initial source is forbidden even when its value equals the write.
This checks the synchronization/source constraint independently of output values. -/
theorem stale_shared_source_rejected (c : SharedContract.Config) {l execution sources order tid offset}
    (hw : execution.WellFormed code l) (hd : execution.Complete) (hp : Pre c l)
    (ht : tid < 2) (hoffset : offset < 4)
    (hs : sources ⟨SharedEvent.id tid,4⟩ ((sharedLoc (SharedContract.other tid)).add offset) = .initial) :
    ¬ GenericMemoryConditions execution l.initial sources order := by
  intro hc
  obtain ⟨first,second,he⟩ := events_present c hw hd hp.1 hp.2.1 tid ht
  obtain ⟨otherFirst,otherSecond,hoe⟩ := events_present c hw hd hp.1 hp.2.1 (SharedContract.other tid) (SharedContract.other_lt ht)
  have hr : execution.readByte ⟨id tid,4⟩ ((sharedLoc (SharedContract.other tid)).add offset) = some (wordByte second offset) := by
    simp only [Candidate.readByte,he,events,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.bind_some,Kind.readByte]
    exact Cells.wordByte_payload _ _ _ hoffset
  have hwrite : execution.writeByte ⟨id (SharedContract.other tid),1⟩ ((sharedLoc (SharedContract.other tid)).add offset) =
      some (wordByte otherFirst offset) := by
    simp only [Candidate.writeByte,hoe,events,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.bind_some,Kind.writeByte]
    exact Cells.wordByte_payload _ _ _ hoffset
  have hn := (race_free_eligible (no_races c hw hd hp.1 hp.2.1 sources) ⟨id tid,4⟩
    ((sharedLoc (SharedContract.other tid)).add offset)).1
  exact stale_initial_forbidden hc hn hwrite hr (write_read_order c hw hd hp.1 hp.2.1 hwrite hr) hs

theorem wrong_output_rejected (c : SharedContract.Config) {l execution sources order o tid offset}
    (hw : execution.WellFormed code l) (hp : Pre c l)
    (hc : GenericMemoryConditions execution l.initial sources order) (hd : o.domain = domain c)
    (ht : tid < 2) (hoffset : offset < 4)
    (hwrong : o.output ((dstLoc c tid).add offset) ≠ wordByte (c.input (SharedContract.other tid)) offset) :
    ¬ ObserverConditions execution l.initial sources order o := by
  intro ho
  exact hwrong ((Event.triple_apply (correct c) hp hw hc ho hd).1 tid ht offset hoffset)

def oracleTrace (c : SharedContract.Config) (tid first second : Nat) : ThreadTrace := {
  id := id tid
  oracle := fun q => if q = 0 then first else second
  count := 17
  final := finalState c tid first second
  events := events c tid first second
}

theorem independent_answers_produced (c : SharedContract.Config) (tid first second : Nat)
    (ht : tid < 2) : (oracleTrace c tid first second).Produced code (SharedContract.initial c).params := by
  simpa only [ThreadTrace.Produced,oracleTrace,ite_true,ite_false,reduceCtorEq]
    using run_thread c tid (oracleTrace c tid first second).oracle (SharedContract.initial c).params ht
      (SharedContract.initial_pre c).params

/-- Removing barrier events from a completed trace of THIS AST is a forgery.
The distinct missing_sync AST still has its own operational negative tests. -/
theorem forged_missing_barrier_rejected (c : SharedContract.Config) (tid first second : Nat) (ht : tid < 2) :
    ¬ ThreadTrace.Produced code (SharedContract.initial c).params
      ({oracleTrace c tid first second with events := [
      .read (srcLoc c tid) (payload first),.write (sharedLoc tid) (payload first),
      .read (sharedLoc (SharedContract.other tid)) (payload second),.write (dstLoc c tid) (payload second)]} : ThreadTrace) := by
  intro h
  have hs := trace_shape c ht (SharedContract.initial_pre c).params rfl h rfl
  have he := congrArg List.length hs.2.2
  change (4 : Nat) = 6 at he
  contradiction

def observedWord (c : SharedContract.Config) (fallback : ByteMap) (cell : Nat) : Nat :=
  let output := (canonicalObservation c (launch c fallback).initial).output
  decodeLE [output (Cells.location cell 0),output (Cells.location cell 1),
    output (Cells.location cell 2),output (Cells.location cell 3)]

theorem pair_exact_words :
    (List.range 4).map (observedWord SharedInstances.pair (fun _ => byte 165)) =
      [4294967295,11,11,4294967295] := by decide

theorem reverse_exact_words_and_frame :
    (List.range 6).map (observedWord SharedInstances.reverse (fun _ => byte 165)) =
      [4294967295,0,777,0,4294967295,888] := by decide

theorem pair_executed_agreement :
    ∃ m, SharedInstances.result = .ok m ∧
      ∀ cell : Fin 4, ∀ offset : Fin 4,
        (canonicalObservation SharedInstances.pair (launch SharedInstances.pair (fun _ => byte 165)).initial).output
            (Cells.location cell offset) =
          Cells.encode m.globalMem (launch SharedInstances.pair (fun _ => byte 165)).initial (Cells.location cell offset) := by
  let m := SharedInstances.result.toOption.getD SharedInstances.start
  exact ⟨m,by decide,by decide⟩

theorem reverse_executed_agreement :
    ∃ m, SharedInstances.reverseResult = .ok m ∧
      ∀ cell : Fin 6, ∀ offset : Fin 4,
        (canonicalObservation SharedInstances.reverse (launch SharedInstances.reverse (fun _ => byte 165)).initial).output
            (Cells.location cell offset) =
          Cells.encode m.globalMem (launch SharedInstances.reverse (fun _ => byte 165)).initial (Cells.location cell offset) := by
  let m := SharedInstances.reverseResult.toOption.getD (SharedContract.initial SharedInstances.reverse)
  exact ⟨m,by decide,by decide⟩

def frameConfig : SharedContract.Config where
  toConfig := {
    src := 1, dst := 3, n := 2, count := 2
    input := fun i => if i = 0 then 0x12345678 else 0xFEDCBA98
    before := [none,some 0x12345678,some 0xFEDCBA98,none,none,none]
    coverage := by decide
    count32 := by decide
    src64 := by decide
    dst64 := by decide
    srcBound := by decide
    dstBound := by decide
    disjoint := Or.inl (by decide)
    initialized := by
      intro i hi
      have he : i = 0 ∨ i = 1 := by omega
      rcases he with rfl | rfl <;> decide
  }
  n_two := rfl
  count_two := rfl

theorem unknown_frame_preserved :
    observedWord frameConfig (fun _ => byte 165) 0 = 0xA5A5A5A5 ∧
    observedWord frameConfig (fun _ => byte 165) 5 = 0xA5A5A5A5 ∧
    observedWord frameConfig (fun _ => byte 165) 3 = 0xFEDCBA98 ∧
    observedWord frameConfig (fun _ => byte 165) 4 = 0x12345678 := by decide

end Ptx.SharedEventTests
