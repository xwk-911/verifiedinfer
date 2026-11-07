import Ptx.Kernels.AmpereTiledWitnessMemory
import Ptx.MemoryGraph.RankedObservation

/-! An independent final global observer from an exhaustive actual-writer
inventory. Shared copies from all K phases remain in the graph/coherence;
neither the inventory nor the selected output is taken from a postcondition. -/
namespace Ptx.AmpereTiledWitnessObservation
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledGraph
open Ptx.AmpereTiledWitnessOracle Ptx.AmpereTiledWitnessMemory
noncomputable section

def copies (cfg : Config) (id : ThreadId) : List Node :=
  (List.range (cfg.k/16)).flatMap (fun phase => (List.finRange 3).map (fun part => .copyWrite ⟨id,3*phase+part.val⟩))
def outputs (cfg : Config) (id : ThreadId) : List Node :=
  (List.finRange 4).map (fun slot => .thread ⟨id,17*(cfg.k/16)+slot.val⟩)
def writers (cfg : Config) (launch : Scalar.Launch) : List Node :=
  launch.geometry.threads.flatMap (fun id => copies cfg id ++ outputs cfg id)
def observation (cfg : Config) (launch : Scalar.Launch) (a b : Matrix) : Ampere.Observation :=
  MemoryGraph.selectedObservation (execution cfg launch a b).memoryGraph launch.initial
    (MemoryGraph.rankedWriterSelector (execution cfg launch a b).memoryGraph AmpereTiledControl.rank (writers cfg launch)) (domain cfg)

theorem copy_mem {cfg launch id phase} (hv : id.Valid launch.geometry) (hp : phase < cfg.k/16) (part : Fin 3) :
    Node.copyWrite ⟨id,3*phase+part.val⟩ ∈ writers cfg launch := by
  apply List.mem_flatMap.mpr
  refine ⟨id,Geometry.mem_threads.mpr hv,?_⟩
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨phase,List.mem_range.mpr hp,List.mem_map.mpr ⟨part,List.mem_finRange _,rfl⟩⟩
theorem output_mem {cfg launch id} (hv : id.Valid launch.geometry) (slot : Fin 4) :
    Node.thread ⟨id,17*(cfg.k/16)+slot.val⟩ ∈ writers cfg launch := by
  apply List.mem_flatMap.mpr
  refine ⟨id,Geometry.mem_threads.mpr hv,?_⟩
  exact List.mem_append_right _ (List.mem_map.mpr ⟨slot,List.mem_finRange _,rfl⟩)

theorem covers_writers {cfg launch a b node loc value} (hp : Pre cfg a b launch) (ha : Active cfg)
    (hw : (execution cfg launch a b).writeByte node loc = some value) : node ∈ writers cfg launch := by
  rcases AmpereTiledGraph.write_cases (source hp ha) hw with ⟨t,ht,_,slot,hn,_⟩ | ⟨t,ht,_,phase,hphase,part,hn,_⟩
  · rw [hn]
    exact output_mem ((source hp ha).formed.2.2.1 t ht).1 slot
  · rw [hn]
    exact copy_mem ((source hp ha).formed.2.2.1 t ht).1 hphase part

theorem observer {cfg launch a b} (hp : Pre cfg a b launch) (ha : Active cfg) :
    ObserverConstraints (execution cfg launch a b) launch.initial rf (co cfg launch a b) (observation cfg launch a b) := by
  apply MemoryGraph.ranked_observation (source hp ha).complete
  · exact fun loc hloc => domain_global hloc
  · intro node loc value hw
    exact covers_writers hp ha hw

theorem observed_domain (cfg : Config) (launch : Scalar.Launch) (a b : Matrix) :
    (observation cfg launch a b).domain = domain cfg := rfl

end
end Ptx.AmpereTiledWitnessObservation
