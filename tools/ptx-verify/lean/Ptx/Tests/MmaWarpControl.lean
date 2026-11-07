import Ptx.Tests.MmaWarpGraph

/-! Control and base-order certificates for the actual complete probe source.
MMA rendezvous is included in control, not in memory publication. -/
namespace Ptx.MmaWarpTests
open Ptx.ISA Ptx.Ampere
noncomputable section

def rank : Node → Nat
  | .thread event => event.serial
  | _ => 0

theorem no_barrier {event kind} (he : candidate.eventAt event = some (.ordinary kind))
    (bid generation : Nat) (hb : Ptx.Event.BarrierKind bid generation kind) : False := by
  have hk : candidate.memoryKind (.thread event) = some kind := by simp [Candidate.memoryKind,he]
  obtain ⟨lane,serial,hn⟩ := memory_node_owner hk
  rw [hn,memory_kind] at hk
  have hs : serial < 12 := by
    by_contra hh
    have hm : (kinds lane)[serial]? = none := List.getElem?_eq_none (by change 12 ≤ serial; omega)
    simp [hm] at hk
  interval_cases serial <;> simp [kinds] at hk <;> cases hk
  all_goals rcases hb with h | h <;> cases h

theorem po_rank {a b} (hp : ProgramOrder candidate a b) : rank a < rank b := by
  cases a <;> cases b <;> try exact False.elim hp
  exact hp.2.2.2

theorem base_rank (a b : Node) (he : BaseEdge candidate a b) : rank a < rank b := by
  rcases he with hp | hb | hi | hc | hw
  · exact po_rank hp
  · cases a <;> cases b <;> try exact False.elim hb
    obtain ⟨_,bid,generation,ha,_⟩ := hb
    exact (no_barrier ha bid generation (.inl rfl)).elim
  · cases a <;> cases b <;> try exact False.elim hi
    obtain ⟨_,_,serial,op,_,hcopy,_⟩ := hi
    rw [no_copies] at hcopy
    cases hcopy
  · cases a <;> cases b <;> simp [CopyInternal,Candidate.Present,no_copies] at hc
  · cases a <;> cases b <;> try exact False.elim hw
    obtain ⟨_,op,groups,keep,hcopy,_,_⟩ := hw
    rw [no_copies] at hcopy
    cases hcopy

def mmaTag : Event → Nat
  | .mmaEntry _ => 1
  | .mmaReturn _ => 2
  | _ => 0

theorem trace_mma_tags (lane : Mma.Lane) : (trace lane).events.map mmaTag = [0,0,0,0,0,0,1,2,0,0,0,0] := by
  fin_cases lane <;> rfl

theorem entry_serial {event mc} (he : candidate.eventAt event = some (.mmaEntry mc)) : event.serial = 6 := by
  obtain ⟨t,ht,_,hi⟩ := eventAt_trace he
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
  have hh := congrArg (Option.map mmaTag) hi
  rw [← List.getElem?_map,trace_mma_tags] at hh
  simp only [Option.map_some,mmaTag] at hh
  have hi' : [0,0,0,0,0,0,1,2,0,0,0,0][event.serial]? = some 1 := hh
  have hs : event.serial < 12 := (List.getElem?_eq_some_iff.mp hi').1
  interval_cases hserial : event.serial <;> first | rfl | norm_num at hh

theorem control : ControlAcyclic candidate := by
  apply control_acyclic_of_rank rank base_rank
  · intro a b he
    cases a <;> cases b <;> try exact False.elim he
    obtain ⟨_,t,_,_,_,bid,generation,hret,_⟩ := he
    exact (no_barrier hret bid generation (.inr rfl)).elim
  · intro a b he
    cases a <;> cases b <;> try exact False.elim he
    obtain ⟨_,arriving,returning,ha,hb,_⟩ := he
    have hs := entry_serial ha
    obtain ⟨lane,hleave,_⟩ := return_origin hb
    simp only [rank,hs,hleave]
    decide

theorem barriers : BarrierParticipation candidate := by
  intro event bid generation he
  exact (no_barrier he bid generation (.inr rfl)).elim

end
end Ptx.MmaWarpTests
