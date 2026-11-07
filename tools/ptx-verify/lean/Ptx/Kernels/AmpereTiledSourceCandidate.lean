import Ptx.Kernels.AmpereTiledGraph
import Ptx.ISA.Enumeration

/-! Full launch source candidates from actual traces, for arbitrary valid
canonical geometries. This constructor proves provenance/completion only;
memory/warp/observer witnesses remain independent obligations. -/
namespace Ptx.AmpereTiledSourceCandidate
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledTrace Ptx.AmpereTiledGraph
noncomputable section

def trace (cfg : Config) (launch : Scalar.Launch) (oracle : ThreadId → Oracle)
    (replies : ∀ id, ReplySet cfg (context launch id) (oracle id)) (id : ThreadId) : ThreadTrace :=
  ⟨id,oracle id,64+21*(cfg.k/16),finalState cfg (context launch id) (oracle id) (replies id),
    events cfg (context launch id) (oracle id) (replies id)⟩
def candidate (cfg : Config) (launch : Scalar.Launch) (oracle : ThreadId → Oracle)
    (replies : ∀ id, ReplySet cfg (context launch id) (oracle id)) : Candidate :=
  ⟨launch.geometry.threads.map (trace cfg launch oracle replies)⟩

theorem formed {cfg : Config} (h : Layout cfg) (launch : Scalar.Launch) (oracle : ThreadId → Oracle)
    (replies : ∀ id, ReplySet cfg (context launch id) (oracle id)) (hp : AmpereTiledInit.Params cfg launch.params)
    (hg : launch.geometry = geometry cfg) (ha : Active cfg) :
    WellFormed AmpereTiledGraph.code launch (candidate cfg launch oracle replies) := by
  refine ⟨by rw [hg]; exact geometry_valid cfg,?_,?_,?_⟩
  · have he : ((candidate cfg launch oracle replies).traces.map ThreadTrace.id) = launch.geometry.threads := by
      simp [candidate,trace,List.map_map,Function.comp_def]
    rw [he]
    exact Geometry.threads_nodup _
  · intro t ht
    obtain ⟨id,hid,rfl⟩ := List.mem_map.mp ht
    have hv := Geometry.mem_threads.mp hid
    refine ⟨hv,?_⟩
    exact translated_run h (context launch id) (oracle id) (replies id) hp (by simpa only [context,hg] using hv) ha
  · intro id hv
    exact ⟨trace cfg launch oracle replies id,List.mem_map.mpr ⟨id,Geometry.mem_threads.mpr hv,rfl⟩,rfl⟩

theorem complete (cfg : Config) (launch : Scalar.Launch) (oracle : ThreadId → Oracle)
    (replies : ∀ id, ReplySet cfg (context launch id) (oracle id)) : Complete (candidate cfg launch oracle replies) := by
  intro t ht
  obtain ⟨id,_,rfl⟩ := List.mem_map.mp ht
  rfl

theorem source_info {cfg : Config} (h : Layout cfg) (launch : Scalar.Launch) (oracle : ThreadId → Oracle)
    (replies : ∀ id, ReplySet cfg (context launch id) (oracle id)) (hp : AmpereTiledInit.Params cfg launch.params)
    (hg : launch.geometry = geometry cfg) (ha : Active cfg) : SourceInfo cfg launch (candidate cfg launch oracle replies) :=
  ⟨h,hp,hg,ha,formed h launch oracle replies hp hg ha,complete cfg launch oracle replies⟩

end
end Ptx.AmpereTiledSourceCandidate
