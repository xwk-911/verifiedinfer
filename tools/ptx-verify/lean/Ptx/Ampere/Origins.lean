import Ptx.Ampere.Source
import Ptx.Scalar.Origins

/-! Instrument the actual Ampere source run with pre-step PCs. Async operations
retain their own instruction slots; scalar skeletons are used only at scalar
steps, never as a replacement source execution. -/
namespace Ptx.Ampere
open Ptx.ISA
noncomputable section

theorem run_eq_plain (ctx : Scalar.Context) (oracle : Oracle) (code : List Instr) (n : Nat) (s : State) :
    run ctx oracle code n s = SourceRun.plain (step ctx oracle code) n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [run,SourceRun.plain,ih]

def runLocated (ctx : Scalar.Context) (oracle : Oracle) (code : List Instr) (n : Nat) (s : State) :=
  SourceRun.run (step ctx oracle code) (fun state => state.scalar.core.thread.pc) n s

theorem run_located_exists {ctx oracle code n s last events}
    (h : run ctx oracle code n s = .ok (last,events)) :
    ∃ located, runLocated ctx oracle code n s = .ok (last,located) ∧ located.map SourceRun.Located.kind = events :=
  SourceRun.of_plain ((run_eq_plain ctx oracle code n s) ▸ h)

theorem located_run_erases {ctx oracle code n s last events}
    (h : runLocated ctx oracle code n s = .ok (last,events)) :
    run ctx oracle code n s = .ok (last,events.map SourceRun.Located.kind) := by
  rw [run_eq_plain]
  exact SourceRun.erases h

def sourceAt (c : Candidate) (code : List Instr) (params : Bindings) (block : Dim3) (id : Ptx.Event.EventId) :
    Option (SourceRun.Located Event) :=
  (c.traceAt id.thread).bind fun t =>
    (runLocated {id := t.id,params := params,block := block} t.oracle code t.count {}).toOption.bind fun result => result.2[id.serial]?

def sourcePC (c : Candidate) (code : List Instr) (params : Bindings) (block : Dim3) (id : Ptx.Event.EventId) : Option Nat :=
  (sourceAt c code params block id).map SourceRun.Located.pc

theorem sourceAt_of_trace {c : Candidate} {t : ThreadTrace} {id : Ptx.Event.EventId} {code params block}
    (hn : (c.traces.map ThreadTrace.id).Nodup) (ht : t ∈ c.traces) (hid : id.thread = t.id) :
    sourceAt c code params block id =
      (runLocated {id := t.id,params := params,block := block} t.oracle code t.count {}).toOption.bind (fun result => result.2[id.serial]?) := by
  unfold sourceAt
  rw [hid,traceAt_of_member hn ht]
  rfl

theorem source_event {c : Candidate} {code launch id kind}
    (hw : WellFormed code launch c) (he : c.eventAt id = some kind) :
    ∃ located, sourceAt c code launch.params launch.geometry.block id = some located ∧ located.kind = kind ∧
      ∃ oracle before after emitted, step {id := id.thread,params := launch.params,block := launch.geometry.block} oracle
        code before = .ok (after,emitted) ∧ kind ∈ emitted ∧ located.pc = before.scalar.core.thread.pc := by
  unfold Candidate.eventAt at he
  cases ht : c.traceAt id.thread with
  | none => simp [ht] at he
  | some t =>
    have hmem := List.mem_of_find?_eq_some ht
    have hid : t.id = id.thread := by simpa only [beq_iff_eq] using List.find?_some ht
    have hindex : t.events[id.serial]? = some kind := by simpa only [ht,Option.bind_some] using he
    obtain ⟨located,hr,herase⟩ := run_located_exists (hw.2.2.1 t hmem).2
    rw [← herase,List.getElem?_map] at hindex
    cases hs : located[id.serial]? with
    | none => simp [hs] at hindex
    | some source =>
      have hk : source.kind = kind := by simpa [hs] using hindex
      refine ⟨source,?_,hk,?_⟩
      · simp only [sourceAt,ht,Option.bind_some,hr,Except.toOption,Option.bind_some]
        exact hs
      · obtain ⟨before,after,emitted,hstep,hsource,hpc⟩ := SourceRun.event_origin hr hs
        exact ⟨t.oracle,before,after,emitted,by simpa only [hid] using hstep,hk ▸ hsource,hpc⟩

theorem step_barrier_source {ctx oracle code s next emitted kind bid generation}
    (hs : step ctx oracle code s = .ok (next,emitted)) (hm : Event.ordinary kind ∈ emitted)
    (hk : Ptx.Event.BarrierKind bid generation kind) :
    code[s.scalar.core.thread.pc]? = some (.scalar (.integer (.barrier bid))) := by
  have hr : s.scalar.core.thread.status = .running := by
    by_cases h : s.scalar.core.thread.status = .running
    · exact h
    · simp [step,h,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs
  cases hc : code[s.scalar.core.thread.pc]? with
  | none => simp [step,hr,hc,bind,Except.bind] at hs
  | some instruction =>
    cases instruction with
    | scalar i =>
      cases ht : Scalar.step ctx oracle.scalar (scalarSkeleton code) s.scalar with
      | error fault => simp [step,hr,hc,ht,liftScalar,bind,Except.bind] at hs
      | ok result =>
        rcases result with ⟨last,events⟩
        have he := (scalar_step hr hc ht).symm.trans hs
        cases Except.ok.inj he
        obtain ⟨original,hmemory,hevent⟩ := List.mem_map.mp hm
        have hkind : original = kind := by cases hevent; rfl
        subst original
        have hb := Scalar.step_barrier_source ht hmemory hk
        rw [scalarSkeleton_slot hc] at hb
        cases Option.some.inj hb
        rfl
    | copy cache dst src size =>
      by_cases hsize : CopySize cache size
      · cases hsrc : evalAddr ctx.id.tid.x s.scalar.core.thread src with
        | error fault => simp [step,hr,hc,hsize,hsrc,liftInteger,bind,Except.bind] at hs
        | ok srcAddr =>
          cases hdst : evalAddr ctx.id.tid.x s.scalar.core.thread dst with
          | error fault => simp [step,hr,hc,hsize,hsrc,hdst,liftInteger,bind,Except.bind] at hs
          | ok dstAddr =>
            by_cases hbytes : (oracle.bytes s.scalar.core.queries).length = size
            · have he := (copy_step hr hc hsize hsrc hdst hbytes).symm.trans hs
              cases Except.ok.inj he
              simp at hm
            · simp [step,hr,hc,hsize,hsrc,hdst,hbytes,liftInteger,bind,Except.bind] at hs
      · simp [step,hr,hc,hsize,bind,Except.bind] at hs
    | commit =>
      have he := (commit_step hr hc).symm.trans hs
      cases Except.ok.inj he
      simp at hm
    | wait keep =>
      by_cases hkeep : keep < 8
      · have he := (wait_step hr hc hkeep).symm.trans hs
        cases Except.ok.inj he
        simp at hm
      · simp [step,hr,hc,Nat.le_of_not_gt hkeep,bind,Except.bind] at hs
    | waitAll =>
      have he := (wait_all_step hr hc).symm.trans hs
      cases Except.ok.inj he
      simp at hm
    | loadWord32 space dst address =>
      cases ha : evalAddr ctx.id.tid.x s.scalar.core.thread address with
      | error fault => simp [step,hr,hc,ha,liftInteger,bind,Except.bind] at hs
      | ok addr =>
        have he := (word_step hr hc ha).symm.trans hs
        cases Except.ok.inj he
        have hkind := Event.ordinary.inj (List.mem_singleton.mp hm)
        subst kind
        rcases hk with hk | hk <;> cases hk
    | mma d a b c =>
      by_cases hd : d.names.Nodup
      · cases hin : readMmaInputs s a b c with
        | error fault => simp [step,hr,hc,hd,hin,bind,Except.bind] at hs
        | ok inputs =>
          have he := (mma_step hr hc hd hin).symm.trans hs
          cases Except.ok.inj he
          simp at hm
      · simp [step,hr,hc,hd,bind,Except.bind] at hs

theorem barrier_source {c : Candidate} {code launch id kind bid generation}
    (hw : WellFormed code launch c) (he : c.eventAt id = some (.ordinary kind))
    (hk : Ptx.Event.BarrierKind bid generation kind) :
    ∃ pc, sourcePC c code launch.params launch.geometry.block id = some pc ∧
      code[pc]? = some (.scalar (.integer (.barrier bid))) := by
  obtain ⟨source,hs,hkind,oracle,before,after,emitted,hstep,hmem,hpc⟩ := source_event hw he
  refine ⟨source.pc,by simp [sourcePC,hs],?_⟩
  rw [hpc]
  exact step_barrier_source hstep hmem hk

theorem step_mma_source {ctx oracle code s next emitted call}
    (hs : step ctx oracle code s = .ok (next,emitted)) (hm : Event.mmaEntry call ∈ emitted ∨ Event.mmaReturn call ∈ emitted) :
    ∃ d a b c, code[s.scalar.core.thread.pc]? = some (.mma d a b c) ∧ call.pc = s.scalar.core.thread.pc := by
  have hr : s.scalar.core.thread.status = .running := by
    by_cases h : s.scalar.core.thread.status = .running
    · exact h
    · simp [step,h,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs
  cases hc : code[s.scalar.core.thread.pc]? with
  | none => simp [step,hr,hc,bind,Except.bind] at hs
  | some instruction =>
    cases instruction with
    | scalar i =>
      cases ht : Scalar.step ctx oracle.scalar (scalarSkeleton code) s.scalar with
      | error fault => simp [step,hr,hc,ht,liftScalar,bind,Except.bind] at hs
      | ok result =>
        have he := (scalar_step hr hc ht).symm.trans hs
        cases Except.ok.inj he
        rcases hm with hm | hm <;> obtain ⟨kind,_,heq⟩ := List.mem_map.mp hm <;> cases heq
    | copy cache dst src size =>
      by_cases hsize : CopySize cache size
      · cases hsrc : evalAddr ctx.id.tid.x s.scalar.core.thread src with
        | error fault => simp [step,hr,hc,hsize,hsrc,liftInteger,bind,Except.bind] at hs
        | ok srcAddr =>
          cases hdst : evalAddr ctx.id.tid.x s.scalar.core.thread dst with
          | error fault => simp [step,hr,hc,hsize,hsrc,hdst,liftInteger,bind,Except.bind] at hs
          | ok dstAddr =>
            by_cases hbytes : (oracle.bytes s.scalar.core.queries).length = size
            · have he := (copy_step hr hc hsize hsrc hdst hbytes).symm.trans hs
              cases Except.ok.inj he
              simp at hm
            · simp [step,hr,hc,hsize,hsrc,hdst,hbytes,liftInteger,bind,Except.bind] at hs
      · simp [step,hr,hc,hsize,bind,Except.bind] at hs
    | commit =>
      have he := (commit_step hr hc).symm.trans hs
      cases Except.ok.inj he
      simp at hm
    | wait keep =>
      by_cases hkeep : keep < 8
      · have he := (wait_step hr hc hkeep).symm.trans hs
        cases Except.ok.inj he
        simp at hm
      · simp [step,hr,hc,Nat.le_of_not_gt hkeep,bind,Except.bind] at hs
    | waitAll =>
      have he := (wait_all_step hr hc).symm.trans hs
      cases Except.ok.inj he
      simp at hm
    | loadWord32 space dst address =>
      cases ha : evalAddr ctx.id.tid.x s.scalar.core.thread address with
      | error fault => simp [step,hr,hc,ha,liftInteger,bind,Except.bind] at hs
      | ok addr =>
        have he := (word_step hr hc ha).symm.trans hs
        cases Except.ok.inj he
        simp at hm
    | mma d a b c =>
      by_cases hd : d.names.Nodup
      · cases hin : readMmaInputs s a b c with
        | error fault => simp [step,hr,hc,hd,hin,bind,Except.bind] at hs
        | ok inputs =>
          have he := (mma_step hr hc hd hin).symm.trans hs
          cases Except.ok.inj he
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
          rcases hm with (hm | hm) | (hm | hm) <;> cases hm
          all_goals exact ⟨d,a,b,c,rfl,rfl⟩
      · simp [step,hr,hc,hd,bind,Except.bind] at hs

theorem step_mma_return_source {ctx oracle code s next emitted call}
    (hs : step ctx oracle code s = .ok (next,emitted)) (hm : Event.mmaReturn call ∈ emitted) :
    ∃ d a b c, code[s.scalar.core.thread.pc]? = some (.mma d a b c) ∧ call.pc = s.scalar.core.thread.pc :=
  step_mma_source hs (.inr hm)

theorem mma_source_pc {c : Candidate} {code launch event call} (hw : WellFormed code launch c)
    (he : c.eventAt event = some (.mmaEntry call) ∨ c.eventAt event = some (.mmaReturn call)) :
    sourcePC c code launch.params launch.geometry.block event = some call.pc := by
  rcases he with he | he
  all_goals
    obtain ⟨located,hsource,_,oracle,before,after,emitted,hstep,hmem,hloc⟩ := source_event hw he
    have hm : Event.mmaEntry call ∈ emitted ∨ Event.mmaReturn call ∈ emitted := by
      first | exact .inl hmem | exact .inr hmem
    obtain ⟨_,_,_,_,_,hpc⟩ := step_mma_source hstep hm
    simp only [sourcePC,hsource,Option.map_some]
    exact congrArg some (hloc.trans hpc.symm)

def noMmaCode (code : List Instr) : Bool := code.all (fun i => match i with | .mma .. => false | _ => true)
theorem no_mma_returns_of_code {c : Candidate} {code launch}
    (hw : WellFormed code launch c) (hn : noMmaCode code = true) (event call) :
    c.eventAt event ≠ some (.mmaReturn call) := by
  intro he
  obtain ⟨located,_,_,oracle,before,after,emitted,hstep,hm,_⟩ := source_event hw he
  obtain ⟨d,a,b,c,hi,_⟩ := step_mma_return_source hstep hm
  have hf := List.all_eq_true.mp hn (.mma d a b c) (List.mem_of_getElem? hi)
  cases hf

def uniqueBarrierSites (code : List Instr) : Bool := Scalar.uniqueBarrierSites (scalarSkeleton code)

theorem unique_barrier_sites {code : List Instr} {a b bid : Nat} (hu : uniqueBarrierSites code = true)
    (ha : code[a]? = some (.scalar (.integer (.barrier bid))))
    (hb : code[b]? = some (.scalar (.integer (.barrier bid)))) : a = b :=
  Scalar.unique_barrier_sites hu (scalarSkeleton_slot ha) (scalarSkeleton_slot hb)

def SourceAligned (code : List Instr) (launch : Scalar.Launch) (c : Candidate) : Prop :=
  ∀ a b, BarrierSync c (.thread a) (.thread b) → ∃ pc,
    sourcePC c code launch.params launch.geometry.block a = some pc ∧
    sourcePC c code launch.params launch.geometry.block b = some pc

theorem aligned_of_unique_sites {c : Candidate} {code launch}
    (hw : WellFormed code launch c) (hu : uniqueBarrierSites code = true) : SourceAligned code launch c := by
  rintro a b ⟨_,bid,generation,ha,hb⟩
  obtain ⟨pa,hpa,hca⟩ := barrier_source hw ha (.inl rfl)
  obtain ⟨pb,hpb,hcb⟩ := barrier_source hw hb (.inr rfl)
  have heq := unique_barrier_sites hu hca hcb
  exact ⟨pa,hpa,by simpa only [heq] using hpb⟩

end
end Ptx.Ampere
