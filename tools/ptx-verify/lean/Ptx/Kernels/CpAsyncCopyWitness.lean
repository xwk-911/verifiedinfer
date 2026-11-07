import Ptx.Kernels.CpAsyncCopyControl
import Ptx.Kernels.CpAsyncCopyPayload
import Ptx.Kernels.CpAsyncCopyCorrect

/-! Independent consistent complete executions from fixed represented inputs.
The explicit rf/co witnesses are certified against actual accesses and source
order. They do not restrict the all-candidate correctness theorem.
-/
namespace Ptx.CpAsyncCopyGraph
open Ptx.ISA Ptx.Ampere Ptx.CpAsyncCopyTrace
noncomputable section

def witnessRF : ReadsFrom
  | .thread _,_ => some (.copyWrite copyId)
  | _,_ => none
def witnessCo (src dst : Nat) (bytes : List Symbolic.Byte) (answers : Answers) : Coherence :=
  MemoryGraph.InitialCo (graph src dst bytes answers).memoryGraph

theorem memory_witness {src dst : Nat} {initial : Ptx.Event.ByteMap Symbolic.Byte} {values : Answers}
    (hi : ∀ i : Fin 4, values i < 2^32 ∧ Scalar.RepresentsU32 initial ⟨.global,src+4*i.val⟩ (values i))
    (hdisjoint : src+16 ≤ dst ∨ dst+16 ≤ src) :
    MemoryConstraints (graph src dst (payload values) values) initial witnessRF (witnessCo src dst (payload values) values) := by
  apply MemoryGraph.initial_co_conditions witnessRank
  · intro a b hp
    cases a <;> cases b <;> try exact False.elim hp
    exact Nat.mul_lt_mul_of_pos_left hp.2.2.2 (by decide)
  · intro a b hp
    exact hp.rank_lt witnessRank base_rank
  · intro loc a b va vb ha hb
    exact unique_writes ha hb
  · intro read loc value hr
    rw [graph_readByte] at hr
    rcases read_cases hr with ⟨rfl,hp⟩ | ⟨i,rfl,hp⟩
    · change some (initial loc) = some value
      exact congrArg some (represented_payload hi hp)
    · have hrf : witnessRF (readNode i) loc = MemoryGraph.writeSource (Node.copyWrite copyId) := rfl
      rw [hrf,MemoryGraph.sourceByte_write,graph_writeByte]
      change ((graph src dst (payload values) values).memoryKind (.copyWrite copyId)).bind _ = _
      rw [copy_write_kind]
      exact payload_word_read hp
  · intro read writer loc vr vw hr hw hs
    rw [graph_readByte] at hr
    rcases read_cases hr with ⟨rfl,_⟩ | ⟨i,rfl,_⟩
    · change none = some writer at hs
      cases hs
    · change some (.copyWrite copyId) = some writer at hs
      have he := Option.some.inj hs
      subst writer
      change 2 < 4*(5+2*i.val)
      omega
  · intro read writer loc vr vw hr hw hs
    rw [graph_readByte] at hr
    rcases read_cases hr with ⟨rfl,hp⟩ | ⟨i,rfl,_⟩
    · obtain ⟨offset,ho,rfl⟩ := Ptx.Event.payload_location hp
      rw [payload_size] at ho
      have hn := input_unwritten (bytes := payload values) (answers := values) hdisjoint offset ho writer
      simp only [graph_writeByte,Location.add] at hw
      rw [hn] at hw
      cases hw
    · change some (Node.copyWrite copyId) = none at hs
      cases hs

def witnessObservation (cfg : CpAsyncCopySpec.Config) (initial : Ptx.Event.ByteMap Symbolic.Byte) (values : Answers) : Observation :=
  MemoryGraph.selectedObservation (graph cfg.src cfg.dst (payload values) values).memoryGraph initial
    (MemoryGraph.writerSelector (graph cfg.src cfg.dst (payload values) values).memoryGraph) (CpAsyncCopySpec.domain cfg)

theorem observer_witness (cfg : CpAsyncCopySpec.Config) (initial : Ptx.Event.ByteMap Symbolic.Byte) (values : Answers) :
    ObserverConstraints (graph cfg.src cfg.dst (payload values) values) initial witnessRF
      (witnessCo cfg.src cfg.dst (payload values) values) (witnessObservation cfg initial values) :=
  MemoryGraph.unique_writers_observation (complete _ _ _ _) (fun _ h => CpAsyncCopySpec.domain_global h)
    (fun _ _ _ _ _ ha hb => unique_writes ha hb)

theorem checked_witness {cfg : CpAsyncCopySpec.Config} {initial : Ptx.Event.ByteMap Symbolic.Byte} {values : Answers}
    (hl : CpAsyncCopySpec.Layout cfg)
    (hi : ∀ i : Fin 4, values i < 2^32 ∧ Scalar.RepresentsU32 initial ⟨.global,cfg.src+4*i.val⟩ (values i)) :
    CheckedConditions code (launch cfg.src cfg.dst initial) (graph cfg.src cfg.dst (payload values) values) witnessRF
      (witnessCo cfg.src cfg.dst (payload values) values) := by
  have hsrc : cfg.src < 2^64 := by obtain ⟨ha,hs,_,_⟩ := hl; omega
  have hdst : cfg.dst+16 ≤ 2^64 := by obtain ⟨ha,_,hd,_⟩ := hl; omega
  exact checked_of_unique_sites (wellFormed _ _ _ _ _ hsrc hdst (payload_size values))
    (by decide) barrier_participation control_acyclic (memory_witness hi hl.2.2.2.2.2)
    (mma_conditions_of_no_code (wellFormed _ _ _ _ _ hsrc hdst (payload_size values)) (by decide))

theorem nonvacuous (cfg : CpAsyncCopySpec.Config) : CheckedNonvacuous code (Pre cfg) (fun _ => CpAsyncCopySpec.domain cfg) := by
  intro l hp
  obtain ⟨values,hi⟩ := hp.2.1
  refine ⟨graph cfg.src cfg.dst (payload values) values,witnessRF,witnessCo cfg.src cfg.dst (payload values) values,
    witnessObservation cfg l.initial values,?_,observer_witness cfg l.initial values,rfl⟩
  rw [hp.2.2]
  exact checked_witness hp.1 hi

end
end Ptx.CpAsyncCopyGraph
