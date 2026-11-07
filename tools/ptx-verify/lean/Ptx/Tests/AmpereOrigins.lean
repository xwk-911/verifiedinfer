import Ptx.Ampere.Checked
import Ptx.Tests.Ampere
import Mathlib.Tactic.IntervalCases

/-! Dynamic source matching accepts multiple sites used in distinct generations,
but rejects a matching barrier number at different PCs in the same generation.
Async control slots remain present in the actual instrumented execution. -/
namespace Ptx.AmpereOriginsTests
open Ptx.ISA Ptx.Ampere
noncomputable section

theorem helper_unique_site : uniqueBarrierSites Generated.cp_async_copy.program = true := by decide
theorem helper_aligned : SourceAligned Generated.cp_async_copy.program AmpereTests.launch AmpereTests.good :=
  aligned_of_unique_sites AmpereTests.good_wellFormed helper_unique_site
theorem helper_arrival_pc : sourcePC AmpereTests.good Generated.cp_async_copy.program AmpereTests.params .one
    (AmpereTests.event 3) = some 5 := by rfl
theorem helper_return_pc : sourcePC AmpereTests.good Generated.cp_async_copy.program AmpereTests.params .one
    (AmpereTests.event 4) = some 5 := by rfl

theorem helper_barrier_participation : BarrierParticipation AmpereTests.good := by
  intro leave bid generation he
  obtain ⟨t,ht,hid,hi⟩ := eventAt_trace he
  have ht' : t = AmpereTests.goodTrace := List.mem_singleton.mp ht
  subst t
  rcases leave with ⟨thread,serial⟩
  change AmpereTests.id = thread at hid
  subst thread
  have hb := (List.getElem?_eq_some_iff.mp hi).1
  change serial < 13 at hb
  interval_cases serial <;> cases hi
  refine ⟨⟨AmpereTests.event 3,rfl,by decide,rfl⟩,?_⟩
  intro t ht _
  have ht' : t = AmpereTests.goodTrace := List.mem_singleton.mp ht
  subst t
  exact .inl (List.mem_of_getElem? (show AmpereTests.goodTrace.events[3]? = some (.ordinary (.barrierArrival 0 0)) by rfl))

theorem helper_control_serial {ev : Ptx.Event.EventId} {kind : Event}
    (he : AmpereTests.good.eventAt ev = some kind) :
    match kind with
    | .issue _ _ => ev.serial = 0
    | .commit _ => ev.serial = 1
    | .wait _ _ => ev.serial = 2
    | .ordinary (.barrierArrival _ _) => ev.serial = 3
    | .ordinary (.barrierReturn _ _) => ev.serial = 4
    | _ => True := by
  obtain ⟨t,ht,_,hi⟩ := eventAt_trace he
  have ht' : t = AmpereTests.goodTrace := List.mem_singleton.mp ht
  subst t
  have hb := (List.getElem?_eq_some_iff.mp hi).1
  change ev.serial < 13 at hb
  interval_cases hserial : ev.serial <;> cases hi <;> trivial

theorem helper_barrier_id {ev : Ptx.Event.EventId} {kind : Scalar.Kind} {bid generation}
    (he : AmpereTests.good.eventAt ev = some (.ordinary kind))
    (hk : Ptx.Event.BarrierKind bid generation kind) : bid = 0 ∧ generation = 0 := by
  obtain ⟨t,ht,_,hi⟩ := eventAt_trace he
  have ht' : t = AmpereTests.goodTrace := List.mem_singleton.mp ht
  subst t
  have hb := (List.getElem?_eq_some_iff.mp hi).1
  change ev.serial < 13 at hb
  interval_cases hserial : ev.serial <;> cases hi
  all_goals rcases hk with hk | hk <;> cases hk <;> exact ⟨rfl,rfl⟩

def helperRank : Node → Nat
  | .thread ev => 4*ev.serial
  | .copyRead _ => 1
  | .copyWrite _ => 2

theorem helper_base_rank (a b : Node) (he : BaseEdge AmpereTests.good a b) : helperRank a < helperRank b := by
  rcases he with hpo | hbar | hissue | hcopy | hcompletion
  · cases a <;> cases b <;> try exact False.elim hpo
    exact Nat.mul_lt_mul_of_pos_left hpo.2.2.2 (by decide)
  · cases a <;> cases b <;> try exact False.elim hbar
    obtain ⟨_,bid,generation,ha,hb⟩ := hbar
    have h₁ := helper_control_serial ha
    have h₂ := helper_control_serial hb
    change _ < _
    simp only [helperRank,h₁,h₂]
    decide
  · cases a <;> cases b <;> try exact False.elim hissue
    obtain ⟨_,_,serial,op,hs,_,hlt⟩ := hissue
    have hserial := helper_control_serial hs
    change serial = 0 at hserial
    change _ < _
    simp only [helperRank]
    omega
  · cases a <;> cases b <;> try exact False.elim hcopy
    simp [helperRank]
  · cases a <;> cases b <;> try exact False.elim hcompletion
    obtain ⟨_,op,groups,keep,_,hs,_⟩ := hcompletion
    have hserial := helper_control_serial hs
    change _ < _
    simp only [helperRank,hserial]
    decide

theorem helper_no_exit_edges (a b : Node) : ¬ ExitBeforeReturn AmpereTests.good a b := by
  cases a <;> cases b <;> try exact id
  rintro ⟨_,t,ht,_,_,bid,generation,hret,hd,hprior⟩
  have hid := helper_barrier_id hret (.inr rfl)
  rcases hid with ⟨rfl,rfl⟩
  have ht' : t = AmpereTests.goodTrace := List.mem_singleton.mp ht
  subst t
  have hh := hprior 0 (List.mem_of_getElem? (show AmpereTests.goodTrace.events[3]? = some (.ordinary (.barrierArrival 0 0)) by rfl))
  omega

theorem helper_control_acyclic : ControlAcyclic AmpereTests.good :=
  control_acyclic_of_rank helperRank helper_base_rank (fun a b h => (helper_no_exit_edges a b h).elim)
    (fun a b h => (no_mma_control_of_no_code AmpereTests.good_wellFormed (by decide) a b h).elim)

def left : ThreadId := ⟨.zero,.zero⟩
def right : ThreadId := ⟨.zero,⟨1,0,0⟩⟩
def geometry : Geometry := ⟨.one,⟨2,1,1⟩⟩
def launch : Scalar.Launch := ⟨geometry,[],fun _ => .bits (byte 0)⟩
def oracle : Oracle := ⟨fun _ => .integer 0,fun _ => [],fun _ => .integer 0,fun _ _ => 0⟩
def badCode : List Ampere.Instr := [
  .scalar (.integer (.mov 32 "%i" .tid)),
  .scalar (.integer (.setp .eq "%p" (.reg "%i") (.imm 0))),
  .scalar (.integer (.branch "%p" true 5)),
  .scalar (.integer (.barrier 0)),.scalar (.integer .ret),
  .commit,.scalar (.integer (.barrier 0)),.scalar (.integer .ret)]
def result (code : List Ampere.Instr) (id : ThreadId) (count : Nat) : State × List Event :=
  ((Ampere.run {id := id,params := [],block := geometry.block} oracle code count {}).toOption).getD ({},[])
def trace (code : List Ampere.Instr) (id : ThreadId) (count : Nat) : ThreadTrace :=
  ⟨id,oracle,count,(result code id count).1,(result code id count).2⟩
def bad : Candidate := ⟨[trace badCode left 6,trace badCode right 5]⟩
def event (id : ThreadId) (serial : Nat) : Ptx.Event.EventId := ⟨id,serial⟩

theorem bad_left_produced : Ampere.Produced badCode [] geometry.block (trace badCode left 6) := by rfl
theorem bad_right_produced : Ampere.Produced badCode [] geometry.block (trace badCode right 5) := by rfl
theorem bad_complete : Complete bad := by
  intro t ht
  simp only [bad,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl <;> rfl
theorem valid_cases {id : ThreadId} (hv : id.Valid geometry) : id = left ∨ id = right := by
  rcases id with ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩
  simp only [geometry,ThreadId.Valid,Dim3.Within,Dim3.one] at hv
  have hx : cx = 0 := by omega
  have hy : cy = 0 := by omega
  have hz : cz = 0 := by omega
  have hty : ty = 0 := by omega
  have htz : tz = 0 := by omega
  subst_vars
  have htx : tx = 0 ∨ tx = 1 := by omega
  rcases htx with rfl | rfl
  · exact .inl rfl
  · exact .inr rfl
theorem two_trace_wellFormed (code : List Ampere.Instr) (lc rc : Nat)
    (hl : Ampere.Produced code [] geometry.block (trace code left lc))
    (hr : Ampere.Produced code [] geometry.block (trace code right rc)) :
    WellFormed code launch ⟨[trace code left lc,trace code right rc]⟩ := by
  refine ⟨by norm_num [launch,geometry,Geometry.Valid,Dim3.Positive,Dim3.one],?_,?_,?_⟩
  · change [left,right].Nodup
    decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨by norm_num [trace,launch,left,geometry,ThreadId.Valid,Dim3.Within,Dim3.zero,Dim3.one],hl⟩
    · exact ⟨by norm_num [trace,launch,right,geometry,ThreadId.Valid,Dim3.Within,Dim3.zero,Dim3.one],hr⟩
  · intro id hv
    rcases valid_cases hv with rfl | rfl
    · exact ⟨trace code left lc,by simp,rfl⟩
    · exact ⟨trace code right rc,by simp,rfl⟩
theorem bad_wellFormed : WellFormed badCode launch bad :=
  two_trace_wellFormed _ _ _ bad_left_produced bad_right_produced
theorem bad_sync : BarrierSync bad (.thread (event left 1)) (.thread (event right 1)) :=
  ⟨rfl,0,0,rfl,rfl⟩
theorem bad_left_source : sourcePC bad badCode [] geometry.block (event left 1) = some 6 := by rfl
theorem bad_right_source : sourcePC bad badCode [] geometry.block (event right 1) = some 3 := by rfl
theorem bad_not_aligned : ¬ SourceAligned badCode launch bad := by
  intro ha
  obtain ⟨pc,hl,hr⟩ := ha _ _ bad_sync
  change sourcePC bad badCode [] geometry.block (event left 1) = some pc at hl
  change sourcePC bad badCode [] geometry.block (event right 1) = some pc at hr
  rw [bad_left_source] at hl
  rw [bad_right_source] at hr
  have := Option.some.inj hl
  have := Option.some.inj hr
  omega
theorem bad_checked_rejected (rf : ReadsFrom) (co : Coherence) : ¬ CheckedConditions badCode launch bad rf co :=
  fun h => bad_not_aligned h.barrierSources

def cycleCode : List Ampere.Instr := badCode.set 3 (.scalar (.integer (.barrier 1)))
def cycle : Candidate := ⟨[trace cycleCode left 6,trace cycleCode right 5]⟩
theorem cycle_left_produced : Ampere.Produced cycleCode [] geometry.block (trace cycleCode left 6) := by rfl
theorem cycle_right_produced : Ampere.Produced cycleCode [] geometry.block (trace cycleCode right 5) := by rfl
theorem cycle_wellFormed : WellFormed cycleCode launch cycle :=
  two_trace_wellFormed _ _ _ cycle_left_produced cycle_right_produced
theorem cycle_complete : Complete cycle := by
  intro t ht
  simp only [cycle,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl <;> rfl

theorem cycle_left_exempt : (trace cycleCode left 6).ExitedBeforeGeneration 1 0 := by
  refine ⟨rfl,?_⟩
  intro g hm
  change Event.ordinary (.barrierArrival 1 g) ∈
    [.commit 0,.ordinary (.barrierArrival 0 0),.ordinary (.barrierReturn 0 0)] at hm
  simp at hm
theorem cycle_right_exempt : (trace cycleCode right 5).ExitedBeforeGeneration 0 0 := by
  refine ⟨rfl,?_⟩
  intro g hm
  change Event.ordinary (.barrierArrival 0 g) ∈
    [.ordinary (.barrierArrival 1 0),.ordinary (.barrierReturn 1 0)] at hm
  simp at hm

theorem cycle_barrier_participation : BarrierParticipation cycle := by
  intro leave bid generation he
  obtain ⟨t,ht,hid,hi⟩ := eventAt_trace he
  simp only [cycle,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases leave with ⟨thread,serial⟩
  rcases ht with rfl | rfl
  · change left = thread at hid
    subst thread
    have hb := (List.getElem?_eq_some_iff.mp hi).1
    change serial < 3 at hb
    interval_cases serial <;> cases hi
    refine ⟨⟨event left 1,rfl,by decide,rfl⟩,?_⟩
    intro t ht _
    simp only [cycle,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · exact .inl (List.mem_of_getElem? (show (trace cycleCode left 6).events[1]? = some (.ordinary (.barrierArrival 0 0)) by rfl))
    · exact .inr cycle_right_exempt
  · change right = thread at hid
    subst thread
    have hb := (List.getElem?_eq_some_iff.mp hi).1
    change serial < 2 at hb
    interval_cases serial <;> cases hi
    refine ⟨⟨event right 0,rfl,by decide,rfl⟩,?_⟩
    intro t ht _
    simp only [cycle,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · exact .inr cycle_left_exempt
    · exact .inl (List.mem_of_getElem? (show (trace cycleCode right 5).events[0]? = some (.ordinary (.barrierArrival 1 0)) by rfl))

theorem cycle_left_before_right : ExitBeforeReturn cycle (.thread (event left 2)) (.thread (event right 1)) :=
  ⟨rfl,trace cycleCode left 6,by simp [cycle],rfl,rfl,1,0,rfl,cycle_left_exempt⟩
theorem cycle_right_before_left : ExitBeforeReturn cycle (.thread (event right 1)) (.thread (event left 2)) :=
  ⟨rfl,trace cycleCode right 5,by simp [cycle],rfl,rfl,0,0,rfl,cycle_right_exempt⟩
theorem cycle_control_rejected : ¬ ControlAcyclic cycle := by
  intro hc
  exact hc (.thread (event left 2)) (.trans (.single (.inr (.inl cycle_left_before_right)))
    (.single (.inr (.inl cycle_right_before_left))))
theorem cycle_checked_rejected (rf : ReadsFrom) (co : Coherence) : ¬ CheckedConditions cycleCode launch cycle rf co :=
  fun h => cycle_control_rejected h.control

def repeatedCode : List Ampere.Instr := [.commit,.scalar (.integer (.barrier 0)),.waitAll,
  .scalar (.integer (.barrier 0)),.scalar (.integer .ret)]
def repeated : Candidate := ⟨[trace repeatedCode left 5,trace repeatedCode right 5]⟩
def repeatedEvents : List Event := [.commit 0,.ordinary (.barrierArrival 0 0),.ordinary (.barrierReturn 0 0),
  .commit 1,.wait 2 0,.ordinary (.barrierArrival 0 1),.ordinary (.barrierReturn 0 1)]
def repeatedPCs : List Nat := [0,1,1,2,2,3,3]
theorem repeated_source (id : ThreadId) : Ampere.Produced repeatedCode [] geometry.block (trace repeatedCode id 5) := by rfl
theorem repeated_wellFormed : WellFormed repeatedCode launch repeated :=
  two_trace_wellFormed _ _ _ (repeated_source left) (repeated_source right)
theorem repeated_complete : Complete repeated := by
  intro t ht
  simp only [repeated,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl <;> rfl
theorem repeated_multiple_sites : uniqueBarrierSites repeatedCode = false := by decide

theorem repeated_origin {ev : Ptx.Event.EventId} {kind : Scalar.Kind} {bid generation}
    (he : repeated.eventAt ev = some (.ordinary kind)) (hk : Ptx.Event.BarrierKind bid generation kind) :
    sourcePC repeated repeatedCode [] geometry.block ev = some (1+2*generation) := by
  unfold Candidate.eventAt at he
  cases ht : repeated.traceAt ev.thread with
  | none => simp [ht] at he
  | some t =>
    have hm := List.mem_of_find?_eq_some ht
    have hi : t.events[ev.serial]? = some (.ordinary kind) := by simpa only [ht,Option.bind_some] using he
    have hev : t.events = repeatedEvents := by
      simp only [repeated,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl <;> rfl
    have hpc : sourcePC repeated repeatedCode [] geometry.block ev = repeatedPCs[ev.serial]? := by
      simp only [sourcePC,sourceAt,ht,Option.bind_some]
      simp only [repeated,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl
      all_goals
        change ((repeatedEvents.zipWith (fun kind pc => SourceRun.Located.mk kind pc) repeatedPCs)[ev.serial]?).map SourceRun.Located.pc = _
        rw [← List.getElem?_map]
        rfl
    rw [hpc]
    rw [hev] at hi
    have hb := (List.getElem?_eq_some_iff.mp hi).1
    change ev.serial < 7 at hb
    interval_cases hserial : ev.serial <;> simp [repeatedEvents,hserial] at hi
    all_goals subst kind; rcases hk with hk | hk <;> cases hk <;> rfl
theorem repeated_aligned : SourceAligned repeatedCode launch repeated := by
  rintro a b ⟨_,bid,generation,ha,hb⟩
  exact ⟨1+2*generation,repeated_origin ha (.inl rfl),repeated_origin hb (.inr rfl)⟩

end
end Ptx.AmpereOriginsTests
