import Ptx.Event.AtomicRules
import Ptx.Scalar.Execution

/-! A genuinely consistent completed single-RMW execution, separate from the
separate two-CTA dispatch contract. It guards against vacuous atomicity/SC
constraints. This is symbolic-interpreter/model evidence, not a GPU run. -/
namespace Ptx.AtomicMemoryTests
open Ptx.ISA Ptx.Event Ptx.Scalar
noncomputable section

def id : ThreadId := ⟨.zero,.zero⟩
def event : EventId := ⟨id,0⟩
def base : Location := ⟨.global,64⟩
def code : List Scalar.Instr := [.atomAddU32 "%r" {base := .imm 64} (.imm 1),.integer .ret]
def trace : Scalar.ThreadTrace := {
  id := id,oracle := fun _ => .integer 0,count := 2
  final := {thread := {pc := 1,status := .done,regs := [("%r",0)]},queries := 1}
  events := [.rmw .gpu base (atomicAddBytes 0 1)]
}
def graph : Scalar.Candidate := ⟨[trace]⟩
def initial : Scalar.ByteMap := fun _ => .bits (byte 0)
def rf : ReadsFrom := fun _ _ => .initial
def launch : Scalar.Launch := ⟨⟨.one,.one⟩,[],initial⟩
def domain : List Location := (List.range 4).map (fun offset => base.add offset)

theorem actual_source_produced : Scalar.Produced code [] trace .one := ⟨[],by rfl⟩

theorem event_shape {e kind} (he : graph.eventAt e = some kind) :
    e = event ∧ kind = .rmw .gpu base (atomicAddBytes 0 1) := by
  obtain ⟨t,ht,htid,hindex⟩ := eventAt_trace he
  have ht' : t = trace := by simpa [graph] using ht
  subst t
  have hbound := (List.getElem?_eq_some_iff.mp hindex).1
  have hserial : e.serial = 0 := by
    have hb : e.serial < 1 := by simpa [trace] using hbound
    omega
  have hid : e = event := by cases e; simp_all [event,trace]
  subst e
  exact ⟨rfl,by simpa [event,trace] using hindex.symm⟩

theorem present_shape {e} (hp : graph.Present e) : e = event := by
  cases he : graph.eventAt e with
  | none => simp [Candidate.Present,he] at hp
  | some kind => exact (event_shape he).1

theorem no_returns (e : EventId) (bid generation : Nat) : graph.eventAt e ≠ some (.barrierReturn bid generation) := by
  intro he
  cases (event_shape he).2

theorem no_base_edges (a b : EventId) : ¬ (ProgramOrder graph a b ∨ BarrierSync graph a b) := by
  rintro (hp | ⟨_,_,_,_,hreturn⟩)
  · have ha := present_shape hp.1
    have hb := present_shape hp.2.1
    rw [ha,hb] at hp
    exact Nat.lt_irrefl 0 hp.2.2.2
  · exact no_returns _ _ _ hreturn

theorem no_base (a b : EventId) : ¬ BaseCausality graph a b :=
  fun hp => hp.impossible no_base_edges

theorem no_causality (a b : EventId) : ¬ Causality graph rf a b := by
  rintro (⟨_,hb⟩ | ⟨_,_,_,hb⟩) <;> exact no_base _ _ hb

theorem no_races (a b : EventId) : ¬ DataRace graph rf a b := by
  intro hr
  obtain ⟨loc,ha,hb⟩ := hr.overlap
  have hea := present_shape (accesses_present ha)
  have heb := present_shape (accesses_present hb)
  subst a; subst b
  exact hr.notStrong ⟨Or.inl rfl,(base,4),rfl,rfl⟩

theorem no_mixed : ¬ MixedSizeRace graph rf := by
  rintro ⟨a,b,hr,_⟩
  exact no_races a b hr

theorem writer_shape {e loc value} (hw : graph.writeByte e loc = some value) : e = event :=
  present_shape (accesses_present (Or.inr (by rw [hw]; rfl)))

theorem coherent : Coherent graph initial rf (InitialCo graph) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rintro loc a ⟨hi,w,v,hw,_⟩
    cases hi.symm.trans hw
  · rintro loc a b d ⟨_,w,v,hw,_⟩ ⟨hi,_⟩
    cases hi.symm.trans hw
  · rintro loc a b ⟨rfl,w,v,rfl,hw⟩
    simp [sourceByte,hw]
  · intro loc w v hw
    exact ⟨rfl,w,v,rfl,hw⟩
  · intro loc a b va vb hne ha hb _
    exact (hne ((writer_shape ha).trans (writer_shape hb).symm)).elim
  · intro loc a b hr
    exact (no_races a b hr).elim
  · intro loc a b va vb _ _ hc
    exact (no_causality a b hc).elim

theorem consistent : GenericMemoryConditions graph initial rf (InitialCo graph) := by
  refine ⟨fun e => no_base e e,?_,?_,?_,fun _ => coherent,?_,?_,?_,?_⟩
  · intro e bid generation he
    exact (no_returns e bid generation he).elim
  · exact barrier_control_of_no_returns (fun e => no_base e e) no_returns
  · intro read loc value _ hr
    have hp : graph.Present read := accesses_present (Or.inl (by rw [hr]; rfl))
    have he := present_shape hp
    subst read
    change payloadByte base ((encodeU32 0).map Symbolic.Byte.bits) loc = some value at hr
    have hm := payloadByte_mem hr
    have hv : value = .bits (byte 0) := by simpa [encodeU32] using hm
    exact congrArg some hv.symm
  · intro _
    constructor
    · intro read writer loc vr vw _ _ hc
      exact (no_causality read writer hc).elim
    · intro writer read loc vw vr _ _ hc
      exact (no_causality writer read hc).elim
  · intro _ read writer _ loc vr vw _ _ hs
    cases hs
  · intro _ members hp _ a ha hpath
    apply hpath.impossible (fun x y hedge => ?_)
    rcases hedge.2.2 with hpo | hcom
    · exact no_base_edges x y (Or.inl hpo)
    · rcases hcom with ⟨_,_,_,hs,_⟩ | ⟨_,hi,_⟩ | ⟨hne,_⟩
      · cases hs
      · cases hi
      · exact hne ((present_shape (hp x hedge.1)).trans (present_shape (hp y hedge.2.1)).symm)
  · intro _ atomic writer _ _ loc vr vw _ _ _ other va vb _ _ hco
    cases hco.1

theorem complete : graph.Complete := by
  intro t ht
  have he : t = trace := by simpa [graph] using ht
  subst t
  rfl

theorem wellFormed : Scalar.WellFormed code launch graph := by
  refine ⟨by simp [launch,Geometry.Valid,Dim3.Positive,Dim3.one],by decide,?_,?_⟩
  · intro t ht
    have he : t = trace := by simpa [graph] using ht
    subst t
    exact ⟨by simp [trace,id,launch,ThreadId.Valid,Dim3.Within,Dim3.one,Dim3.zero],actual_source_produced⟩
  · intro thread hv
    have he : thread = id := by
      rcases thread with ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩
      simp only [ThreadId.Valid,launch,Dim3.Within,Dim3.one] at hv
      have hz : cx = 0 ∧ cy = 0 ∧ cz = 0 ∧ tx = 0 ∧ ty = 0 ∧ tz = 0 := by omega
      rcases hz with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
      rfl
    exact ⟨trace,by simp [graph],by simpa [trace] using he.symm⟩

theorem observed : ObserverConditions graph initial rf (InitialCo graph)
    (singleWriterObservation graph initial event domain) := by
  apply single_writer_observation complete
  · intro loc hm
    obtain ⟨offset,_,rfl⟩ := List.mem_map.mp hm
    rfl
  · intro other loc value hw
    exact writer_shape hw

theorem observed_counter_one : (singleWriterObservation graph initial event domain).output base = .bits (byte 1) := by rfl

theorem self_read_excluded {initial' rf' co}
    (hm : GenericMemoryConditions graph initial' rf' co) (hn : ¬ MixedSizeRace graph rf') :
    rf' event base ≠ .write event :=
  rmw_no_self_read hm hn (show graph.readByte event base = some (.bits (byte 0)) from rfl)
    (show graph.writeByte event base = some (.bits (byte 1)) from rfl)

end
end Ptx.AtomicMemoryTests
