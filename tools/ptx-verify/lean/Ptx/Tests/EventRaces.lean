import Ptx.Event.Consistency
import Ptx.Tests.Event

/-! Race-classification checks. The uniform-size traces come from one shared
integer program. Mixed-size byte graphs exercise the relation layer only: the
current frontend/interpreter does not accept byte loads. Classification alone
is not a full consistent-execution witness for either graph. -/
namespace Ptx.EventRaceTests
open Ptx Ptx.ISA Ptx.Event

def writer : ThreadId := EventTests.id0
def reader : ThreadId := ⟨.zero, ⟨1, 0, 0⟩⟩
def w : EventId := ⟨writer, 0⟩
def r : EventId := ⟨reader, 0⟩
def loc : Location := ⟨.global, 0⟩
def readPayload (mixed : Bool) (value : Nat) : List Byte :=
  if mixed then [byte value] else encodeU32 (wrap 32 value)

def code : List Instr := [
  .mov 32 "%i" .tid,
  .setp .eq "%p" (.reg "%i") (.imm 0),
  .branch "%p" true 5,
  .load .global "%r" ⟨.imm 0, 0⟩,
  .ret,
  .store .global ⟨.imm 0, 0⟩ (.imm 1),
  .ret]

def writeTrace : ThreadTrace := {
  id := writer
  oracle := fun _ => 0
  count := 5
  final := { thread := { pc := 6, regs := [("%p", 1), ("%i", 0)], status := .done } }
  events := [.write loc (encodeU32 1)]
}
def readTrace (mixed : Bool) (value : Nat) : ThreadTrace := {
  id := reader
  oracle := fun _ => value
  count := 5
  final := { thread := { pc := 4, regs := [("%r", wrap 32 value), ("%p", 0), ("%i", 1)], status := .done }, queries := 1 }
  events := [.read loc (readPayload mixed value)]
}
def graph (mixed : Bool) (value : Nat) : Candidate := ⟨[writeTrace, readTrace mixed value]⟩

theorem writer_produced : writeTrace.Produced code [] := by rfl
theorem uniform_reader_produced (value : Nat) : (readTrace false value).Produced code [] := by rfl

theorem event_shape {mixed value id kind} (he : (graph mixed value).eventAt id = some kind) :
    (kind = .write loc (encodeU32 1) ∨ kind = .read loc (readPayload mixed value)) ∧
      id.serial = 0 := by
  obtain ⟨t, ht, hk, hn⟩ := eventAt_mem he
  simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht
  · subst t
    simp only [writeTrace, List.mem_singleton] at hk
    exact ⟨.inl hk, by simpa [writeTrace] using hn⟩
  · subst t
    simp only [readTrace, List.mem_singleton] at hk
    exact ⟨.inr hk, by simpa [readTrace] using hn⟩

theorem no_edges (mixed : Bool) (value : Nat) (a b) :
    ¬ (ProgramOrder (graph mixed value) a b ∨ BarrierSync (graph mixed value) a b) := by
  intro hedge
  rcases hedge with hp | hs
  · have hzero : ∀ id, (graph mixed value).Present id → id.serial = 0 := by
      intro id h
      cases he : (graph mixed value).eventAt id with
      | none => simp [Candidate.Present, he] at h
      | some kind => exact (event_shape he).2
    have ha := hzero a hp.1
    have hb := hzero b hp.2.1
    have := hp.2.2.2
    omega
  · obtain ⟨_, id, generation, ha, _⟩ := hs
    rcases (event_shape ha).1 with hk | hk <;> cases hk

theorem no_base (mixed : Bool) (value : Nat) (a b) :
    ¬ BaseCausality (graph mixed value) a b :=
  fun h => h.impossible (no_edges mixed value)

theorem no_causality (mixed : Bool) (value : Nat) (rf : ReadsFrom) (a b) :
    ¬ Causality (graph mixed value) rf a b := by
  rintro (⟨_, hb⟩ | ⟨middle, _, _, hb⟩)
  · exact no_base mixed value _ _ hb
  · exact no_base mixed value _ _ hb

theorem racing (mixed : Bool) (value : Nat) (rf : ReadsFrom) :
    DataRace (graph mixed value) rf r w := by
  refine ⟨?_, ?_, no_causality mixed value rf _ _, no_causality mixed value rf _ _, ?_⟩
  · refine ⟨loc, .inl ?_, .inr ?_⟩
    · cases mixed <;> rfl
    · rfl
  · exact .inr ⟨loc, byte 1, rfl⟩
  · intro hs
    have hn : ¬ (graph mixed value).IsRMW r := by
      rintro ⟨_,_,_,he⟩
      rcases (event_shape he).1 with hk | hk <;> cases hk
    exact (show reader ≠ writer by decide) ((morally_strong_of_no_rmw hn).mp hs).1

theorem tainted (mixed : Bool) (value : Nat) (rf : ReadsFrom) :
    Tainted (graph mixed value) rf r loc :=
  race_taints_read (by rfl) (racing mixed value rf)

theorem racing_read_not_eligible (mixed : Bool) (value : Nat) (rf : ReadsFrom) :
    ¬ Eligible (graph mixed value) rf r loc := fun h => h.2 (tainted mixed value rf)

theorem uniform_no_mixed_race (value : Nat) (rf : ReadsFrom) :
    ¬ MixedSizeRace (graph false value) rf := by
  have hfoot : ∀ id, (graph false value).Present id →
      ((graph false value).eventAt id).bind Kind.footprint = some (loc, 4) := by
    intro id hp
    cases he : (graph false value).eventAt id with
    | none => simp [Candidate.Present, he] at hp
    | some kind =>
      rcases (event_shape he).1 with hk | hk
      · simp [hk, Kind.footprint]
      · simp [hk, Kind.footprint, readPayload]
  rintro ⟨a,b,hr,hn⟩
  obtain ⟨address,ha,hb⟩ := hr.overlap
  exact hn ⟨(loc,4), hfoot a (accesses_present ha), hfoot b (accesses_present hb)⟩

theorem mixed_race_exists (value : Nat) (rf : ReadsFrom) :
    MixedSizeRace (graph true value) rf := by
  refine ⟨r, w, racing true value rf, ?_⟩
  rintro ⟨footprint,ha,hb⟩
  have hra : ((graph true value).eventAt r).bind Kind.footprint = some (loc, 1) := by rfl
  have hrb : ((graph true value).eventAt w).bind Kind.footprint = some (loc, 4) := by rfl
  have heq := (Option.some.inj (ha.symm.trans hra)).symm.trans (Option.some.inj (hb.symm.trans hrb))
  have : (1 : Nat) = 4 := congrArg Prod.snd heq
  contradiction

theorem mixed_disables_all_reads (value : Nat) (rf : ReadsFrom) (read address) :
    ¬ Eligible (graph true value) rf read address :=
  mixed_size_disables_eligibility (mixed_race_exists value rf) read address

end Ptx.EventRaceTests
