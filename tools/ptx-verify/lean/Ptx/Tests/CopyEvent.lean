import Ptx.Kernels.CopyEventWitness
import Ptx.Tests.Copy

/-! Cross-model regressions, including u32 truncation, reversed layout, inactive
threads, arbitrary initial bytes and rejection of wrong or stale observations.
Finite computations below are execution tests; general contracts are separate.
-/
namespace Ptx.CopyEventTests
open Ptx.ISA Ptx.Event Ptx.CopyEvent

def launch (c : CopyContract.Config) (fallback : ByteMap) : Launch := {
  geometry := geometry c
  params := (CopyContract.initial c []).params
  initial := Cells.encode c.before fallback
}

theorem launch_pre (c : CopyContract.Config) (fallback : ByteMap) (hp : 0 < c.count) :
    Pre c (launch c fallback) :=
  ⟨hp,rfl,(CopyContract.initial_pre c []).params,Cells.encode_represents _ _⟩

theorem witnessed_contract (c : CopyContract.Config) (fallback : ByteMap) (hp : 0 < c.count) :
    ∃ execution sources order o, execution.WellFormed code (launch c fallback) ∧
      GenericMemoryConditions execution (launch c fallback).initial sources order ∧
      ObserverConditions execution (launch c fallback).initial sources order o ∧
      o.domain = domain c ∧ BytePost c (launch c fallback).initial o.output := by
  have hpre := launch_pre c fallback hp
  obtain ⟨execution,sources,order,o,hw,hc,ho,hd⟩ := nonvacuous c _ hpre
  exact ⟨execution,sources,order,o,hw,hc,ho,hd,Event.triple_apply (correct c) hpre hw hc ho hd⟩

theorem incorrect_read_rejected (c : CopyContract.Config) {l execution sources order tid answer offset}
    (hw : execution.WellFormed code l) (hd : execution.Complete) (hp : Pre c l)
    (ht : tid < c.n) (hoffset : offset < 4)
    (hr : execution.eventAt ⟨id tid,0⟩ = some (.read (srcLoc c tid) (payload answer)))
    (hwrong : wordByte answer offset ≠ wordByte (c.input tid) offset) :
    ¬ GenericMemoryConditions execution l.initial sources order := by
  intro hc
  exact hwrong ((read_byte_matches_initial c hw hd hp.2.1 hp.2.2.1 hc ht hr offset hoffset).trans
    (initialized_of_representation c hp.2.2.2 tid ht offset hoffset))

theorem incorrect_output_rejected (c : CopyContract.Config) {l execution sources order o tid offset}
    (hw : execution.WellFormed code l) (hp : Pre c l)
    (hc : GenericMemoryConditions execution l.initial sources order) (hd : o.domain = domain c)
    (ht : tid < c.n) (hoffset : offset < 4)
    (hwrong : o.output ((dstLoc c tid).add offset) ≠ wordByte (c.input tid) offset) :
    ¬ ObserverConditions execution l.initial sources order o := by
  intro ho
  exact hwrong ((Event.triple_apply (correct c) hp hw hc ho hd).1 tid ht offset hoffset)

/-- Reject initialization as a source even when its value happens to equal the
store. Value-only comparisons would miss an invalid missing-write selector. -/
theorem stale_source_rejected (c : CopyContract.Config) {l execution sources order o tid offset}
    (hw : execution.WellFormed code l) (hp : Pre c l)
    (hc : GenericMemoryConditions execution l.initial sources order) (hd : o.domain = domain c)
    (ht : tid < c.n) (hoffset : offset < 4)
    (hs : o.source ((dstLoc c tid).add offset) = .initial) :
    ¬ ObserverConditions execution l.initial sources order o := by
  intro ho
  obtain ⟨answer,_,hwrite⟩ := active_events_present c hw ho.complete hp.2.1 hp.2.2.1 tid ht
  have hb : execution.writeByte ⟨id tid,1⟩ ((dstLoc c tid).add offset) = some (wordByte answer offset) := by
    simp only [Candidate.writeByte,hwrite,Option.bind_some,Kind.writeByte]
    exact Cells.wordByte_payload _ _ _ hoffset
  have hn := (race_free_observer_eligible (no_races c hw ho.complete hp.2.1 hp.2.2.1 sources)
    ((dstLoc c tid).add offset)).1
  apply ho.noStale _ (hd.symm ▸ destination_in_domain c ht hoffset) hn _ _ hb
  rw [hs]
  exact (hc.coherence hn).initialization _ _ _ hb

def observedWord (c : CopyContract.Config) (fallback : ByteMap) (cell : Nat) : Nat :=
  let output := (canonicalObservation c (launch c fallback).initial).output
  decodeLE [output (Cells.location cell 0),output (Cells.location cell 1),
    output (Cells.location cell 2),output (Cells.location cell 3)]

theorem masked_exact_words :
    (List.range 6).map (observedWord CopyInstances.maskedConfig (fun _ => byte 165)) =
      [0,4294967295,7,0,4294967295,7] := by decide

theorem reverse_words_and_frame :
    (List.range 6).map (observedWord CopyInstances.reverseConfig (fun _ => byte 165)) =
      [10,20,777,10,20,888] := by decide

/-- Reconcile the event output with an actually executed, interleaved operational
schedule, rather than assuming an operational result with the expected values. -/
theorem masked_executed_agreement :
    ∃ m, CopyInstances.maskedResult = .ok m ∧
      ∀ cell, cell < CopyInstances.maskedConfig.before.length → ∀ offset, offset < 4 →
        (canonicalObservation CopyInstances.maskedConfig
          (launch CopyInstances.maskedConfig (fun _ => byte 165)).initial).output (Cells.location cell offset) =
        Cells.encode m.globalMem (launch CopyInstances.maskedConfig (fun _ => byte 165)).initial
          (Cells.location cell offset) := by
  obtain ⟨m,hr,hm⟩ := CopyInstances.masked_generic_post
  refine ⟨m,hr,?_⟩
  have hp := launch_pre CopyInstances.maskedConfig (fun _ => byte 165) (by decide)
  have hw := canonical_wellFormed CopyInstances.maskedConfig hp.1 hp.2.1 hp.2.2.1
  have hc := canonical_memory CopyInstances.maskedConfig hp.1 hp.2.1 hp.2.2.1
    (initialized_of_representation _ hp.2.2.2)
  have ho := canonical_observation CopyInstances.maskedConfig hp.1 hp.2.1 hp.2.2.1
  have hb := Event.triple_apply (correct CopyInstances.maskedConfig) hp hw hc ho rfl
  intro cell hcell offset hoffset
  exact post_encoding_agreement _ hp.2.2.2 hb hm cell offset hcell hoffset

theorem reverse_executed_agreement :
    ∃ m, CopyInstances.reverseResult = .ok m ∧
      ∀ cell, cell < CopyInstances.reverseConfig.before.length → ∀ offset, offset < 4 →
        (canonicalObservation CopyInstances.reverseConfig
          (launch CopyInstances.reverseConfig (fun _ => byte 165)).initial).output (Cells.location cell offset) =
        Cells.encode m.globalMem (launch CopyInstances.reverseConfig (fun _ => byte 165)).initial
          (Cells.location cell offset) := by
  obtain ⟨m,hr,hm⟩ := CopyInstances.reverse_generic_post
  refine ⟨m,hr,?_⟩
  have hp := launch_pre CopyInstances.reverseConfig (fun _ => byte 165) (by decide)
  have hw := canonical_wellFormed CopyInstances.reverseConfig hp.1 hp.2.1 hp.2.2.1
  have hc := canonical_memory CopyInstances.reverseConfig hp.1 hp.2.1 hp.2.2.1
    (initialized_of_representation _ hp.2.2.2)
  have ho := canonical_observation CopyInstances.reverseConfig hp.1 hp.2.1 hp.2.2.1
  have hb := Event.triple_apply (correct CopyInstances.reverseConfig) hp hw hc ho rfl
  intro cell hcell offset hoffset
  exact post_encoding_agreement _ hp.2.2.2 hb hm cell offset hcell hoffset

def frameConfig : CopyContract.Config where
  src := 1
  dst := 3
  n := 1
  count := 2
  input := fun _ => 0x12345678
  before := [none,some 0x12345678,some 777,none,none]
  coverage := by decide
  count32 := by decide
  src64 := by decide
  dst64 := by decide
  srcBound := by decide
  dstBound := by decide
  disjoint := Or.inl (by decide)
  initialized := by
    intro i hi
    have he : i = 0 := by omega
    subst i
    decide

theorem unknown_frame_preserved :
    observedWord frameConfig (fun _ => byte 165) 0 = 0xA5A5A5A5 ∧
    observedWord frameConfig (fun _ => byte 165) 4 = 0xA5A5A5A5 ∧
    observedWord frameConfig (fun _ => byte 165) 3 = 0x12345678 := by decide

theorem empty_copy_unchanged (fallback : ByteMap) :
    (canonicalObservation CopyInstances.emptyConfig fallback).output = fallback := by
  funext loc
  have hn : ¬ Destination CopyInstances.emptyConfig loc := by
    intro h; change loc.space = .global ∧ 0 ≤ loc.address ∧ loc.address < 0 at h; omega
  simp [canonicalObservation,selectedObservation,select,hn]

def zeroConfig := CopyContract.contiguous [] 0 (by decide) (by decide)

theorem zero_threads_not_a_launch (l : Launch) : ¬ Pre zeroConfig l := by
  intro hp
  have h := hp.1
  change 0 < 0 at h
  omega

end Ptx.CopyEventTests
