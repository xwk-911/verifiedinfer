import Ptx.Tests.MmaWarpMemory
import Ptx.Tests.MmaWarpControl

/-! Independent complete checked source/rf/co/observer smoke witness for the
generated full-warp MMA probe. This is not universal tiled-matmul correctness. -/
namespace Ptx.MmaWarpTests
open Ptx.ISA Ptx.Ampere
noncomputable section

def witnessRF : ReadsFrom := fun _ _ => none
def witnessCo : Coherence := MemoryGraph.InitialCo candidate.memoryGraph
def domain : List Location := (List.range 1284).map (fun address => ⟨.global,address⟩)
def observation : Observation := MemoryGraph.selectedObservation candidate.memoryGraph representedInitial
  (MemoryGraph.writerSelector candidate.memoryGraph) domain

theorem memory_witness : MemoryConstraints candidate representedInitial witnessRF witnessCo := by
  apply MemoryGraph.initial_co_conditions rank
  · intro a b hp
    exact po_rank hp
  · intro a b hp
    exact hp.rank_lt rank base_rank
  · intro loc a b va vb ha hb
    exact unique_writes ha hb
  · intro read loc value hr
    rw [graph_readByte] at hr
    obtain ⟨lane,i,_,hp⟩ := read_cases hr
    exact congrArg some (initial_read hp)
  · intro read writer loc vr vw hr hw hs
    change none = some writer at hs
    cases hs
  · intro read writer loc vr vw hr hw _
    exact (input_output_disjoint hr hw).elim

theorem observer_witness : ObserverConstraints candidate representedInitial witnessRF witnessCo observation := by
  apply MemoryGraph.unique_writers_observation complete
  · intro loc hm
    obtain ⟨addr,_,rfl⟩ := List.mem_map.mp hm
    rfl
  · intro loc a b va vb ha hb
    exact unique_writes ha hb

theorem checked_witness : CheckedConditions Generated.mma_probe.program representedLaunch candidate witnessRF witnessCo := by
  apply checked_of_unique_sites
  · exact wellFormed
  · decide
  · exact barriers
  · exact control
  · exact memory_witness
  · exact mma_conditions

set_option maxRecDepth 8192 in
theorem complete_legal_execution_exists : ∃ (c : Candidate) (rf : ReadsFrom) (co : Coherence) (o : Observation),
    CheckedConditions Generated.mma_probe.program representedLaunch c rf co ∧
    Complete c ∧ ObserverConstraints c representedInitial rf co o ∧ o.domain = domain :=
  ⟨candidate,witnessRF,witnessCo,observation,checked_witness,complete,observer_witness,rfl⟩

theorem observed_output_byte (lane : Mma.Lane) (slot : Fin 4) (offset : Fin 4) :
    observation.output ((writeBase lane slot).add offset.val) =
      outputBytes[offset.val]'(by change offset.val < 4; exact offset.isLt) := by
  have hw : candidate.writeByte (writeNode lane slot) ((writeBase lane slot).add offset.val) =
      some (outputBytes[offset.val]'(by change offset.val < 4; exact offset.isLt)) := by
    simp only [Candidate.writeByte,write_kind,Option.bind_some,Ptx.Event.Kind.writeByte,Ptx.Event.payloadByte_offset]
    exact List.getElem?_eq_getElem _
  have hs := MemoryGraph.writer_selector_covers (c := candidate.memoryGraph)
    (writer := writeNode lane slot) (loc := (writeBase lane slot).add offset.val)
    (fun _ _ _ _ _ ha hb => unique_writes ha hb) hw
  simp only [observation,MemoryGraph.selectedObservation,hs,graph_writeByte,hw,Option.getD_some]

theorem output_guard_preserved : observation.output ⟨.global,1280⟩ = .bits (byte 165) := by
  classical
  have hn : ¬ ∃ writer value, candidate.memoryGraph.writeByte writer ⟨.global,1280⟩ = some value := by
    rintro ⟨writer,value,hw⟩
    obtain ⟨lane,i,_,hp⟩ := write_cases hw
    have hb := Ptx.Event.payloadByte_bounds hp
    have he : outputBytes.length = 4 := by rfl
    rw [he] at hb
    have hr := (write_bounds lane i).2.2
    have hlt := hb.2.2
    change 1280 < _ at hlt
    omega
  have hn' : ¬ ∃ writer value, candidate.writeByte writer ⟨.global,1280⟩ = some value := hn
  simp [observation,MemoryGraph.selectedObservation,MemoryGraph.writerSelector,hn',representedInitial]

end
end Ptx.MmaWarpTests
