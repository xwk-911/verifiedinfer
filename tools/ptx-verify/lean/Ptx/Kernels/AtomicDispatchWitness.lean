import Ptx.Kernels.AtomicDispatchRace
import Ptx.Kernels.AtomicDispatchCounter
import Ptx.Kernels.AtomicDispatchCandidate
import Ptx.Event.RankedObservation

/-! Independent global consistency/observation construction, reusing an actual
source assignment without assuming the universal output theorem or memory
consistency. Either CTA may receive the first job. -/
namespace Ptx.AtomicDispatchEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.AtomicDispatchTrace
noncomputable section

def witnessRank {execution} (jobs : Assignment execution) (event : EventId) : Nat :=
  if event.thread = jobs.first.id then event.serial else 2+event.serial
def witnessRf {execution} (jobs : Assignment execution) : ReadsFrom :=
  fun read _ => if read.thread = jobs.first.id then .initial else .write (firstCounter jobs)
def witnessWriters {execution} (jobs : Assignment execution) : List EventId :=
  [firstCounter jobs,firstJob jobs,secondCounter jobs,secondJob jobs]

theorem assignment_read_agreement (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Pre cfg launch) (jobs : Assignment execution)
    {read loc value} (hr : execution.readByte read loc = some value) :
    sourceByte execution launch.initial loc (witnessRf jobs read loc) = some value := by
  have hl := read_region cfg hw hd hp.1 hp.2.1 hr
  obtain ⟨offset,ho,hloc⟩ := word_region_offset hl
  have hloc' : loc = (counterLoc cfg).add offset := hloc
  subst loc
  rcases counter_reader_pair cfg hw hd hp.1 hp.2.1 jobs hr with rfl | rfl
  · have hbyte := counter_read_byte cfg hw hd hp.2.1 jobs.firstMember ho
    rw [jobs.firstTicket] at hbyte
    have hv := Option.some.inj (hr.symm.trans hbyte)
    simpa only [witnessRf,firstCounter,ite_true,sourceByte,hv,counterLoc] using congrArg some (hp.2.2 offset ho)
  · have hbyte := counter_read_byte cfg hw hd hp.2.1 jobs.secondMember ho
    rw [jobs.secondTicket] at hbyte
    have hv := Option.some.inj (hr.symm.trans hbyte)
    have hids := assigned_ids_ne hw jobs
    simpa only [witnessRf,secondCounter,Ne.symm hids,ite_false,sourceByte,hv,counterLoc]
      using first_counter_byte cfg hw hd hp.2.1 jobs ho

theorem assignment_rank_injective (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Params cfg.counter cfg.x cfg.y launch.params) (jobs : Assignment execution)
    {a b loc va vb} (ha : execution.writeByte a loc = some va) (hb : execution.writeByte b loc = some vb)
    (he : witnessRank jobs a = witnessRank jobs b) : a = b := by
  have hids := assigned_ids_ne hw jobs
  have hia := assigned_inventory cfg hw hd hp jobs (accesses_present (Or.inr (by rw [ha]; rfl)))
  have hib := assigned_inventory cfg hw hd hp jobs (accesses_present (Or.inr (by rw [hb]; rfl)))
  rcases hia with rfl | rfl | rfl | rfl <;> rcases hib with rfl | rfl | rfl | rfl
  all_goals first | rfl | (simp [witnessRank,firstCounter,secondCounter,firstJob,secondJob,Ne.symm hids] at he)

theorem assignment_rf_rank (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Pre cfg launch) (jobs : Assignment execution)
    {read writer loc vr vw} (hr : execution.readByte read loc = some vr) (_ : execution.writeByte writer loc = some vw)
    (hs : witnessRf jobs read loc = .write writer) : witnessRank jobs writer < witnessRank jobs read := by
  have hids := assigned_ids_ne hw jobs
  rcases counter_reader_pair cfg hw hd hp.1 hp.2.1 jobs hr with rfl | rfl
  · simp [witnessRf,firstCounter] at hs
  · have he : writer = firstCounter jobs := by simpa [witnessRf,secondCounter,Ne.symm hids] using hs.symm
    subst writer
    simp [witnessRank,firstCounter,secondCounter,Ne.symm hids]

theorem assignment_fr_rank (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Pre cfg launch) (jobs : Assignment execution)
    {read writer loc vr vw} (hne : read ≠ writer)
    (hr : execution.readByte read loc = some vr) (hwri : execution.writeByte writer loc = some vw)
    (hc : RankedCo execution launch.initial (witnessRank jobs) loc (witnessRf jobs read loc) (.write writer)) :
    witnessRank jobs read < witnessRank jobs writer := by
  have hids := assigned_ids_ne hw jobs
  have hl := read_region cfg hw hd hp.1 hp.2.1 hr
  have hiw := counter_writer_pair cfg hw hd hp.1 hp.2.1 jobs hl hwri
  rcases counter_reader_pair cfg hw hd hp.1 hp.2.1 jobs hr with rfl | rfl
  · rcases hiw with rfl | rfl
    · exact (hne rfl).elim
    · simp [witnessRank,firstCounter,secondCounter,Ne.symm hids]
  · rcases hiw with rfl | rfl
    · have hlt := hc.2.2
      simp [witnessRf,secondCounter,Ne.symm hids,sourceRank] at hlt
    · exact (hne rfl).elim

theorem assignment_consistent (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Pre cfg launch) (jobs : Assignment execution) :
    GenericMemoryConditions execution launch.initial (witnessRf jobs)
      (RankedCo execution launch.initial (witnessRank jobs)) := by
  have hn := no_returns cfg hw hd hp.1 hp.2.1
  apply ranked_co_conditions (witnessRank jobs)
  · intro a b hpo
    have ht := hpo.2.2.1
    have hs := hpo.2.2.2
    unfold witnessRank
    rw [ht]
    split <;> omega
  · rintro a b ⟨_,bid,generation,_,hreturn⟩
    exact (hn b bid generation hreturn).elim
  · rintro a b ⟨_,_,_,_,_,bid,generation,hreturn,_⟩
    exact (hn b bid generation hreturn).elim
  · intro event bid generation he
    exact (hn event bid generation he).elim
  · exact no_races_of_assignment cfg hw hd hp.1 hp.2.1 jobs (witnessRf jobs)
  · intro loc a b va vb ha hb he
    exact assignment_rank_injective cfg hw hd hp.2.1 jobs ha hb he
  · intro read loc value hr
    exact assignment_read_agreement cfg hw hd hp jobs hr
  · intro read writer loc vr vw hr hwrite hs
    exact assignment_rf_rank cfg hw hd hp jobs hr hwrite hs
  · intro read writer loc vr vw hne hr hwrite hc
    exact assignment_fr_rank cfg hw hd hp jobs hne hr hwrite hc

theorem assignment_observed (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Pre cfg launch) (jobs : Assignment execution) (domain : List Location)
    (hglobal : ∀ loc ∈ domain, loc.space = .global) :
    ObserverConditions execution launch.initial (witnessRf jobs) (RankedCo execution launch.initial (witnessRank jobs))
      (selectedObservation execution launch.initial (rankedWriterSelector execution (witnessRank jobs) (witnessWriters jobs)) domain) := by
  apply ranked_observation hd hglobal
  intro writer loc value hwrite
  have hi := assigned_inventory cfg hw hd hp.2.1 jobs (accesses_present (Or.inr (by rw [hwrite]; rfl)))
  simpa only [witnessWriters,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using hi

def witnessValues (reverse : Bool) (cta : Nat) : Nat := if reverse then 1-cta else cta

theorem canonical_two_traces (cfg : Config) (values : Nat → Nat) {t : Scalar.ThreadTrace}
    (ht : t ∈ (canonical cfg values).traces) : t = canonicalTrace cfg values 0 ∨ t = canonicalTrace cfg values 1 := by
  obtain ⟨cta,hin,rfl⟩ := List.mem_map.mp ht
  have hc := List.mem_range.mp hin
  have he : cta = 0 ∨ cta = 1 := by omega
  rcases he with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

def canonicalAssignment (cfg : Config) (reverse : Bool) : Assignment (canonical cfg (witnessValues reverse)) := by
  cases reverse with
  | false => exact {
      first := canonicalTrace cfg (witnessValues false) 0
      second := canonicalTrace cfg (witnessValues false) 1
      firstMember := canonical_member cfg _ (by decide)
      secondMember := canonical_member cfg _ (by decide)
      covers := fun _ ht => canonical_two_traces cfg _ ht
      firstTicket := rfl,secondTicket := rfl
    }
  | true => exact {
      first := canonicalTrace cfg (witnessValues true) 1
      second := canonicalTrace cfg (witnessValues true) 0
      firstMember := canonical_member cfg _ (by decide)
      secondMember := canonical_member cfg _ (by decide)
      covers := fun _ ht => (canonical_two_traces cfg _ ht).symm
      firstTicket := rfl,secondTicket := rfl
    }

theorem canonical_allowed (cfg : Config) (reverse : Bool) {launch : Scalar.Launch} (hp : Pre cfg launch)
    (domain : List Location) (hglobal : ∀ loc ∈ domain, loc.space = .global) :
    ∃ rf co o, Scalar.WellFormed code launch (canonical cfg (witnessValues reverse)) ∧
      GenericMemoryConditions (canonical cfg (witnessValues reverse)) launch.initial rf co ∧
      ObserverConditions (canonical cfg (witnessValues reverse)) launch.initial rf co o ∧ o.domain = domain := by
  let execution := canonical cfg (witnessValues reverse)
  let jobs := canonicalAssignment cfg reverse
  have hw := canonical_wellFormed cfg (witnessValues reverse) hp.1 hp.2.1
  have hd := canonical_complete cfg (witnessValues reverse)
  exact ⟨witnessRf jobs,RankedCo execution launch.initial (witnessRank jobs),
    selectedObservation execution launch.initial (rankedWriterSelector execution (witnessRank jobs) (witnessWriters jobs)) domain,
    hw,assignment_consistent cfg hw hd hp jobs,assignment_observed cfg hw hd hp jobs domain hglobal,rfl⟩

theorem nonvacuous (cfg : Config) (domain : List Location) (hglobal : ∀ loc ∈ domain, loc.space = .global) :
    Scalar.Nonvacuous code (Pre cfg) (fun _ => domain) := by
  intro launch hp
  obtain ⟨rf,co,o,hw,hm,ho,hdom⟩ := canonical_allowed cfg false hp domain hglobal
  exact ⟨canonical cfg (witnessValues false),rf,co,o,hw,hm,ho,hdom⟩

end
end Ptx.AtomicDispatchEvent
