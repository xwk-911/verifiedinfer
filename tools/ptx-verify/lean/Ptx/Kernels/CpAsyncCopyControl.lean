import Ptx.Kernels.CpAsyncCopyMemory

/-! Parameterized construct witnesses for the actual helper graph. A ranking
certifies this family; it is not added to universal allowed-execution semantics.
-/
namespace Ptx.CpAsyncCopyGraph
open Ptx.ISA Ptx.Ampere Ptx.CpAsyncCopyTrace
noncomputable section
variable {src dst : Nat} {bytes : List Symbolic.Byte} {answers : Answers}

theorem barrier_participation : BarrierParticipation (graph src dst bytes answers) := by
  intro leave bid generation he
  obtain ⟨t,ht,hid,hi⟩ := eventAt_trace he
  have ht' : t = (trace src dst bytes answers) := List.mem_singleton.mp ht
  subst t
  rcases leave with ⟨owner,serial⟩
  change thread = owner at hid
  subst owner
  have hb := (List.getElem?_eq_some_iff.mp hi).1
  change serial < 13 at hb
  interval_cases serial <;> cases hi
  refine ⟨⟨(⟨thread,3⟩ : Ptx.Event.EventId),rfl,by decide,rfl⟩,?_⟩
  intro t ht _
  have ht' : t = (trace src dst bytes answers) := List.mem_singleton.mp ht
  subst t
  exact .inl (List.mem_of_getElem? (show (trace src dst bytes answers).events[3]? = some (.ordinary (.barrierArrival 0 0)) by rfl))

theorem control_serial {ev : Ptx.Event.EventId} {kind : Event}
    (he : (graph src dst bytes answers).eventAt ev = some kind) :
    match kind with
    | .issue _ _ => ev.serial = 0
    | .commit _ => ev.serial = 1
    | .wait _ _ => ev.serial = 2
    | .ordinary (.barrierArrival _ _) => ev.serial = 3
    | .ordinary (.barrierReturn _ _) => ev.serial = 4
    | _ => True := by
  obtain ⟨t,ht,_,hi⟩ := eventAt_trace he
  have ht' : t = (trace src dst bytes answers) := List.mem_singleton.mp ht
  subst t
  have hb := (List.getElem?_eq_some_iff.mp hi).1
  change ev.serial < 13 at hb
  interval_cases hserial : ev.serial <;> cases hi <;> trivial

theorem barrier_id {ev : Ptx.Event.EventId} {kind : Scalar.Kind} {bid generation}
    (he : (graph src dst bytes answers).eventAt ev = some (.ordinary kind))
    (hk : Ptx.Event.BarrierKind bid generation kind) : bid = 0 ∧ generation = 0 := by
  obtain ⟨t,ht,_,hi⟩ := eventAt_trace he
  have ht' : t = (trace src dst bytes answers) := List.mem_singleton.mp ht
  subst t
  have hb := (List.getElem?_eq_some_iff.mp hi).1
  change ev.serial < 13 at hb
  interval_cases hserial : ev.serial <;> cases hi
  all_goals rcases hk with hk | hk <;> cases hk <;> exact ⟨rfl,rfl⟩

def witnessRank : Node → Nat
  | .thread ev => 4*ev.serial
  | .copyRead _ => 1
  | .copyWrite _ => 2

theorem base_rank (a b : Node) (he : BaseEdge (graph src dst bytes answers) a b) : witnessRank a < witnessRank b := by
  rcases he with hpo | hbar | hissue | hcopy | hcompletion
  · cases a <;> cases b <;> try exact False.elim hpo
    exact Nat.mul_lt_mul_of_pos_left hpo.2.2.2 (by decide)
  · cases a <;> cases b <;> try exact False.elim hbar
    obtain ⟨_,bid,generation,ha,hb⟩ := hbar
    have h₁ := control_serial ha
    have h₂ := control_serial hb
    change _ < _
    simp only [witnessRank,h₁,h₂]
    decide
  · cases a <;> cases b <;> try exact False.elim hissue
    obtain ⟨_,_,serial,op,hs,_,hlt⟩ := hissue
    have hserial := control_serial hs
    change serial = 0 at hserial
    change _ < _
    simp only [witnessRank]
    omega
  · cases a <;> cases b <;> try exact False.elim hcopy
    simp [witnessRank]
  · cases a <;> cases b <;> try exact False.elim hcompletion
    obtain ⟨_,op,groups,keep,_,hs,_⟩ := hcompletion
    have hserial := control_serial hs
    change _ < _
    simp only [witnessRank,hserial]
    decide

theorem no_exit_edges (a b : Node) : ¬ ExitBeforeReturn (graph src dst bytes answers) a b := by
  cases a <;> cases b <;> try exact id
  rintro ⟨_,t,ht,_,_,bid,generation,hret,hd,hprior⟩
  have hid := barrier_id hret (.inr rfl)
  rcases hid with ⟨rfl,rfl⟩
  have ht' : t = (trace src dst bytes answers) := List.mem_singleton.mp ht
  subst t
  have hh := hprior 0 (List.mem_of_getElem? (show (trace src dst bytes answers).events[3]? = some (.ordinary (.barrierArrival 0 0)) by rfl))
  omega

theorem no_mma_returns : NoMmaReturns (graph src dst bytes answers) := by
  apply no_mma_returns_of_events
  intro t ht
  have hh : t = trace src dst bytes answers := List.mem_singleton.mp ht
  subst t
  rfl

theorem control_acyclic : ControlAcyclic (graph src dst bytes answers) :=
  control_acyclic_of_rank witnessRank base_rank (fun a b h => (no_exit_edges a b h).elim)
    (fun a b h => (no_mma_control_of_no_returns no_mma_returns a b h).elim)

end
end Ptx.CpAsyncCopyGraph
