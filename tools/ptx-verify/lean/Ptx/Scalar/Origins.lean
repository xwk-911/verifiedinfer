import Ptx.Scalar.Execution
import Ptx.Event.Origins

/-! Source-PC instrumentation of the actual mixed interpreter, with its complete
float bank and actual launch block. Integer skeletons are not substituted for
mixed program execution. Generic event-source matching is shared with integers. -/
namespace Ptx.Scalar
open Ptx.ISA
noncomputable section

theorem run_eq_plain (ctx : Context) (oracle : Oracle) (code : List Instr) (n : Nat) (s : State) :
    run ctx oracle code n s = SourceRun.plain (step ctx oracle code) n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [run,SourceRun.plain,ih]

def runLocated (ctx : Context) (oracle : Oracle) (code : List Instr) (n : Nat) (s : State) :=
  SourceRun.run (step ctx oracle code) (fun state => state.core.thread.pc) n s

theorem run_located_exists {ctx oracle code n s last events}
    (h : run ctx oracle code n s = .ok (last,events)) :
    ∃ located, runLocated ctx oracle code n s = .ok (last,located) ∧ located.map SourceRun.Located.kind = events :=
  SourceRun.of_plain ((run_eq_plain ctx oracle code n s) ▸ h)

theorem located_run_erases {ctx oracle code n s last events}
    (h : runLocated ctx oracle code n s = .ok (last,events)) :
    run ctx oracle code n s = .ok (last,events.map SourceRun.Located.kind) := by
  rw [run_eq_plain]
  exact SourceRun.erases h

def sourceAt (c : Candidate) (code : List Instr) (params : Bindings) (block : Dim3) (id : Event.EventId) :
    Option (SourceRun.Located Kind) :=
  (c.traces.find? (fun t => t.id == id.thread)).bind fun t =>
    (runLocated {id := t.id,params := params,block := block} t.oracle code t.count {}).toOption.bind fun result => result.2[id.serial]?

def sourcePC (c : Candidate) (code : List Instr) (params : Bindings) (block : Dim3) (id : Event.EventId) : Option Nat :=
  (sourceAt c code params block id).map SourceRun.Located.pc

theorem sourceAt_of_trace {c : Candidate} {t : ThreadTrace} {id : Event.EventId} {code params block}
    (hn : (c.traces.map Event.ThreadTrace.id).Nodup) (ht : t ∈ c.traces) (hid : id.thread = t.id) :
    sourceAt c code params block id =
      (runLocated {id := t.id,params := params,block := block} t.oracle code t.count {}).toOption.bind (fun result => result.2[id.serial]?) := by
  unfold sourceAt
  rw [Event.find_trace hn ht hid]
  rfl

theorem source_event {c : Candidate} {code launch id kind}
    (hw : WellFormed code launch c) (he : c.eventAt id = some kind) :
    ∃ located, sourceAt c code launch.params launch.geometry.block id = some located ∧ located.kind = kind ∧
      ∃ oracle before after emitted, step {id := id.thread,params := launch.params,block := launch.geometry.block} oracle
        code before = .ok (after,emitted) ∧ kind ∈ emitted ∧ located.pc = before.core.thread.pc := by
  obtain ⟨t,ht,htid,hindex⟩ := Event.eventAt_trace he
  obtain ⟨floats,hproduced⟩ := (hw.2.2.1 t ht).2
  obtain ⟨located,hr,herase⟩ := run_located_exists hproduced
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

theorem barrier_source {c : Candidate} {code launch id kind bid generation}
    (hw : WellFormed code launch c) (he : c.eventAt id = some kind) (hk : Event.BarrierKind bid generation kind) :
    ∃ pc, sourcePC c code launch.params launch.geometry.block id = some pc ∧
      code[pc]? = some (.integer (.barrier bid)) := by
  obtain ⟨source,hs,hkind,oracle,before,after,emitted,hstep,hmem,hpc⟩ := source_event hw he
  refine ⟨source.pc,by simp [sourcePC,hs],?_⟩
  rw [hpc]
  exact step_barrier_source hstep hmem hk

def uniqueBarrierSites (code : List Instr) : Bool :=
  (List.range code.length).all fun a => (List.range code.length).all fun b =>
    match code[a]?,code[b]? with
    | some (.integer (.barrier x)),some (.integer (.barrier y)) => !(x == y) || a == b
    | _,_ => true

theorem unique_barrier_sites {code : List Instr} {a b bid : Nat} (hu : Scalar.uniqueBarrierSites code = true)
    (ha : code[a]? = some (.integer (.barrier bid))) (hb : code[b]? = some (.integer (.barrier bid))) : a = b := by
  have h := List.all_eq_true.mp hu a (List.mem_range.mpr (List.getElem?_eq_some_iff.mp ha).1)
  have h' := List.all_eq_true.mp h b (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hb).1)
  simpa [ha,hb] using h'

def SourceAligned (code : List Instr) (launch : Launch) (c : Candidate) : Prop :=
  Event.AlignedBarrierSources c (sourcePC c code launch.params launch.geometry.block)

theorem aligned_of_unique_sites {c : Candidate} {code launch}
    (hw : WellFormed code launch c) (hu : Scalar.uniqueBarrierSites code = true) : SourceAligned code launch c := by
  rintro a b ⟨_,bid,generation,ha,hb⟩
  obtain ⟨pa,hpa,hca⟩ := barrier_source hw ha (.inl rfl)
  obtain ⟨pb,hpb,hcb⟩ := barrier_source hw hb (.inr rfl)
  have heq := Scalar.unique_barrier_sites hu hca hcb
  exact ⟨pa,hpa,by simpa only [heq] using hpb⟩

end
end Ptx.Scalar
