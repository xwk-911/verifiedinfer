import Ptx.Event.SourceRun
import Ptx.Event.Relations
import Ptx.ISA.BarrierSites

/-! Actual integer-source event origins and dynamic aligned-barrier admission.
The old graph/byte model is retained. Equal resource/generation is supplemented
by equal source PCs for each matched arrival/return; different generations may
legitimately use different PCs. This is not a full SIMT/ISA UB model. -/
namespace Ptx.Event
open Ptx.ISA

theorem run_eq_plain (ctx : Context) (oracle : Oracle) (code : List Instr) (n : Nat) (s : State) :
    run ctx oracle code n s = SourceRun.plain (step ctx oracle code) n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [run,SourceRun.plain,ih]

def runLocated (ctx : Context) (oracle : Oracle) (code : List Instr) (n : Nat) (s : State) :=
  SourceRun.run (step ctx oracle code) (fun state => state.thread.pc) n s

theorem run_located_exists {ctx oracle code n s last events}
    (h : run ctx oracle code n s = .ok (last,events)) :
    ∃ located, runLocated ctx oracle code n s = .ok (last,located) ∧ located.map SourceRun.Located.kind = events :=
  SourceRun.of_plain ((run_eq_plain ctx oracle code n s) ▸ h)

theorem located_run_erases {ctx oracle code n s last events}
    (h : runLocated ctx oracle code n s = .ok (last,events)) :
    run ctx oracle code n s = .ok (last,events.map SourceRun.Located.kind) := by
  rw [run_eq_plain]
  exact SourceRun.erases h

def Candidate.sourceAt (c : Candidate) (code : List Instr) (params : Bindings) (id : EventId) :
    Option (SourceRun.Located Kind) :=
  (c.traces.find? (fun t => t.id == id.thread)).bind fun t =>
    (runLocated ⟨t.id,params⟩ t.oracle code t.count {}).toOption.bind fun result => result.2[id.serial]?

def Candidate.sourcePC (c : Candidate) (code : List Instr) (params : Bindings) (id : EventId) : Option Nat :=
  (c.sourceAt code params id).map SourceRun.Located.pc

theorem sourceAt_of_trace {c : Candidate} {t : ThreadTrace} {id : EventId} {code params}
    (hn : (c.traces.map ThreadTrace.id).Nodup) (ht : t ∈ c.traces) (hid : id.thread = t.id) :
    c.sourceAt code params id =
      (runLocated ⟨t.id,params⟩ t.oracle code t.count {}).toOption.bind (fun result => result.2[id.serial]?) := by
  unfold Candidate.sourceAt
  rw [find_trace hn ht hid]
  rfl

theorem source_event {c : Candidate} {code launch id kind}
    (hw : c.WellFormed code launch) (he : c.eventAt id = some kind) :
    ∃ located, c.sourceAt code launch.params id = some located ∧ located.kind = kind ∧
      ∃ oracle before after emitted, step ⟨id.thread,launch.params⟩ oracle
        code before = .ok (after,emitted) ∧ kind ∈ emitted ∧ located.pc = before.thread.pc := by
  obtain ⟨t,ht,htid,hindex⟩ := eventAt_trace he
  obtain ⟨located,hr,herase⟩ := run_located_exists (hw.2.2.1 t ht).2
  rw [← herase,List.getElem?_map] at hindex
  cases hs : located[id.serial]? with
  | none => simp [hs] at hindex
  | some source =>
    have hk : source.kind = kind := by simpa [hs] using hindex
    refine ⟨source,?_,hk,?_⟩
    · rw [sourceAt_of_trace hw.2.1 ht htid.symm,hr]
      exact hs
    · obtain ⟨before,after,emitted,hstep,hmem,hpc⟩ := SourceRun.event_origin hr hs
      exact ⟨t.oracle,before,after,emitted,by simpa only [htid] using hstep,hk ▸ hmem,hpc⟩

def BarrierKind {ByteValue : Type} (bid generation : Nat) (kind : Kind ByteValue) : Prop :=
  kind = .barrierArrival bid generation ∨ kind = .barrierReturn bid generation

theorem step_barrier_source {ctx oracle code s next emitted kind bid generation}
    (hs : step ctx oracle code s = .ok (next,emitted)) (hm : kind ∈ emitted)
    (hk : BarrierKind bid generation kind) : code[s.thread.pc]? = some (.barrier bid) := by
  have hr : s.thread.status = .running := by
    by_cases h : s.thread.status = .running
    · exact h
    · simp [step,h,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs
  cases hc : code[s.thread.pc]? with
  | none => simp [step,hr,hc,bind,Except.bind] at hs
  | some instruction =>
    cases instruction with
    | load space dst address =>
      cases ha : evalAddr ctx.id.tid.x s.thread address <;>
        simp [step,hr,hc,ha,bind,Except.bind,pure,Except.pure] at hs
      rcases hs with ⟨rfl,rfl⟩
      simp only [List.mem_singleton] at hm
      subst kind
      rcases hk with hk | hk <;> cases hk
    | store space address value =>
      cases ha : evalAddr ctx.id.tid.x s.thread address <;>
        simp [step,hr,hc,ha,bind,Except.bind,pure,Except.pure] at hs
      cases hv : eval ctx.id.tid.x s.thread value <;>
        simp [hv,bind,Except.bind,pure,Except.pure] at hs
      rcases hs with ⟨rfl,rfl⟩
      simp only [List.mem_singleton] at hm
      subst kind
      rcases hk with hk | hk <;> cases hk
    | barrier actual =>
      simp [step,hr,hc,bind,Except.bind,pure,Except.pure] at hs
      rcases hs with ⟨rfl,rfl⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl <;> rcases hk with hk | hk <;> cases hk
      all_goals rfl
    | _ =>
      simp [step,hr,hc,bind,Except.bind,pure,Except.pure] at hs
      split at hs <;> simp_all

theorem barrier_source {c : Candidate} {code launch id kind bid generation}
    (hw : c.WellFormed code launch) (he : c.eventAt id = some kind) (hk : BarrierKind bid generation kind) :
    ∃ pc, c.sourcePC code launch.params id = some pc ∧ code[pc]? = some (.barrier bid) := by
  obtain ⟨source,hs,hkind,oracle,before,after,emitted,hstep,hmem,hpc⟩ := source_event hw he
  refine ⟨source.pc,by simp [Candidate.sourcePC,hs],?_⟩
  rw [hpc]
  exact step_barrier_source hstep hmem hk

variable {ByteValue Answers : Type}

def AlignedBarrierSources (c : Candidate ByteValue Answers) (sourcePC : EventId → Option Nat) : Prop :=
  ∀ a b, BarrierSync c a b → ∃ pc, sourcePC a = some pc ∧ sourcePC b = some pc

def Candidate.SourceAligned (c : Candidate) (code : List Instr) (params : Bindings) : Prop :=
  AlignedBarrierSources c (c.sourcePC code params)

theorem aligned_of_unique_sites {c : Candidate} {code launch}
    (hw : c.WellFormed code launch) (hu : uniqueBarrierSites code = true) : c.SourceAligned code launch.params := by
  rintro a b ⟨_,bid,generation,ha,hb⟩
  obtain ⟨pa,hpa,hca⟩ := barrier_source hw ha (.inl rfl)
  obtain ⟨pb,hpb,hcb⟩ := barrier_source hw hb (.inr rfl)
  have heq := unique_barrier_sites hu hca hcb
  exact ⟨pa,hpa,by simpa only [heq] using hpb⟩

end Ptx.Event
