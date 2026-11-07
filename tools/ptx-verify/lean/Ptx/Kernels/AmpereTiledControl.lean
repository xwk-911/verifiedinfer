import Ptx.Kernels.AmpereTiledGraph

/-! Full-CTA participation and acyclic actual control order, including
independent copy nodes and MMA rendezvous. The rank is a proved certificate;
it is not an added allowed-execution premise or a memory-publication edge. -/
namespace Ptx.AmpereTiledControl
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledTrace Ptx.AmpereTiledGraph Ptx.AmpereTiledEvents
noncomputable section

theorem arrival_info {cfg launch candidate event bid generation} (h : SourceInfo cfg launch candidate)
    (he : candidate.eventAt event = some (.ordinary (.barrierArrival bid generation))) :
    ∃ phase, phase < cfg.k/16 ∧ ∃ half : Fin 2,
      bid = 0 ∧ generation = 2*phase+half.val ∧ event.serial = 17*phase+5+10*half.val := by
  obtain ⟨_,_,_,_,hget⟩ := event_view h he
  exact AmpereTiledInventory.barrier_arrival_cases hget
theorem return_info {cfg launch candidate event bid generation} (h : SourceInfo cfg launch candidate)
    (he : candidate.eventAt event = some (.ordinary (.barrierReturn bid generation))) :
    ∃ phase, phase < cfg.k/16 ∧ ∃ half : Fin 2,
      bid = 0 ∧ generation = 2*phase+half.val ∧ event.serial = 17*phase+6+10*half.val := by
  obtain ⟨_,_,_,_,hget⟩ := event_view h he
  exact AmpereTiledInventory.barrier_return_cases hget

theorem event_owner_valid {cfg launch candidate event kind} (h : SourceInfo cfg launch candidate)
    (he : candidate.eventAt event = some kind) : event.thread.Valid launch.geometry := by
  obtain ⟨t,ht,hid,_⟩ := eventAt_trace he
  exact hid ▸ (h.formed.2.2.1 t ht).1

theorem peer_arrival {cfg launch candidate} (h : SourceInfo cfg launch candidate) {t : ThreadTrace}
    (ht : t ∈ candidate.traces) {phase : Nat} (hp : phase < cfg.k/16) (half : Fin 2) :
    Event.ordinary (.barrierArrival 0 (2*phase+half.val)) ∈ t.events := by
  have he := arrival_event h (h.formed.2.2.1 t ht).1 hp half
  rw [member_event h ht] at he
  exact List.mem_of_getElem? he

theorem barriers {cfg launch candidate} (h : SourceInfo cfg launch candidate) : BarrierParticipation candidate := by
  intro leave bid generation he
  obtain ⟨phase,hp,half,rfl,rfl,hserial⟩ := return_info h he
  have hv := event_owner_valid h he
  refine ⟨⟨⟨leave.thread,17*phase+5+10*half.val⟩,rfl,by simp; omega,arrival_event h hv hp half⟩,?_⟩
  intro t ht _
  exact .inl (peer_arrival h ht hp half)

def rank : Node → Nat
  | .thread event => 3*event.serial
  | .copyRead operation => 3*(17*(operation.ordinal/3)+operation.ordinal%3)+1
  | .copyWrite operation => 3*(17*(operation.ordinal/3)+operation.ordinal%3)+2

theorem read_rank (id : ThreadId) (phase : Nat) (part : Fin 3) :
    rank (.copyRead ⟨id,3*phase+part.val⟩) = 3*(17*phase+part.val)+1 := by
  have hi := part.isLt
  simp only [rank]
  omega
theorem write_rank (id : ThreadId) (phase : Nat) (part : Fin 3) :
    rank (.copyWrite ⟨id,3*phase+part.val⟩) = 3*(17*phase+part.val)+2 := by
  have hi := part.isLt
  simp only [rank]
  omega

theorem base_rank {cfg launch candidate} (h : SourceInfo cfg launch candidate) (a b : Node)
    (he : BaseEdge candidate a b) : rank a < rank b := by
  rcases he with hpo | hbar | hissue | hcopy | hcompletion
  · cases a <;> cases b <;> try exact False.elim hpo
    exact Nat.mul_lt_mul_of_pos_left hpo.2.2.2 (by decide)
  · cases a <;> cases b <;> try exact False.elim hbar
    obtain ⟨_,bid,generation,ha,hb⟩ := hbar
    obtain ⟨pa,_,ia,_,hga,hsa⟩ := arrival_info h ha
    obtain ⟨pb,_,ib,_,hgb,hsb⟩ := return_info h hb
    have hia := ia.isLt
    have hib := ib.isLt
    simp only [rank]
    omega
  · cases a <;> cases b <;> try exact False.elim hissue
    obtain ⟨_,_,serial,op,hs,_,hlt⟩ := hissue
    obtain ⟨_,_,_,_,hget⟩ := event_view h hs
    obtain ⟨phase,_,part,hordinal,hserial,_⟩ := AmpereTiledInventory.issue_cases hget
    dsimp only at hordinal hserial
    simp only [rank]
    have hi := part.isLt
    omega
  · cases a <;> cases b <;> try exact False.elim hcopy
    obtain ⟨rfl,_⟩ := hcopy
    simp [rank]
  · cases a <;> cases b <;> try exact False.elim hcompletion
    obtain ⟨_,op,groups,keep,hcopy,hwait,hcover⟩ := hcompletion
    obtain ⟨t,_,r,p,hp,part,hoperation,hop⟩ := copy_cases h hcopy
    have hgroup : op.group = p := hop ▸ operation_group _ _ _ r p part
    obtain ⟨_,_,_,_,hget⟩ := event_view h hwait
    obtain ⟨waitPhase,_,hserial,rfl,rfl⟩ := AmpereTiledInventory.wait_cases hget
    rw [hoperation,write_rank]
    simp only [rank]
    have hi := part.isLt
    omega

theorem no_exit_edges {cfg launch candidate} (h : SourceInfo cfg launch candidate) (a b : Node) :
    ¬ ExitBeforeReturn candidate a b := by
  cases a <;> cases b <;> try exact id
  rintro ⟨_,t,ht,_,_,bid,generation,hret,_,hprior⟩
  obtain ⟨phase,hp,half,rfl,rfl,_⟩ := return_info h hret
  have hh := hprior _ (peer_arrival h ht hp half)
  omega

theorem mma_rank {cfg launch candidate} (h : SourceInfo cfg launch candidate) (a b : Node)
    (he : MmaControl candidate a b) : rank a < rank b := by
  cases a <;> cases b <;> try exact False.elim he
  obtain ⟨_,arriving,returning,ha,hb,_,hordinal,_⟩ := he
  obtain ⟨_,_,_,_,hga⟩ := event_view h ha
  obtain ⟨_,_,_,_,hgb⟩ := event_view h hb
  obtain ⟨pa,_,hsa,hca⟩ := AmpereTiledInventory.mma_entry_cases hga
  obtain ⟨pb,_,hsb,hcb⟩ := AmpereTiledInventory.mma_return_cases hgb
  rw [hca,hcb,call_ordinal,call_ordinal] at hordinal
  simp only [rank]
  omega

theorem control {cfg launch candidate} (h : SourceInfo cfg launch candidate) : ControlAcyclic candidate :=
  control_acyclic_of_rank rank (base_rank h) (fun a b he => (no_exit_edges h a b he).elim) (mma_rank h)
theorem base_acyclic {cfg launch candidate} (h : SourceInfo cfg launch candidate) : MemoryGraph.BaseAcyclic candidate.memoryGraph :=
  control_implies_base_acyclic (control h)

end
end Ptx.AmpereTiledControl
