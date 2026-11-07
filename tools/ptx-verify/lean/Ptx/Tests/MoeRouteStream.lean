import Ptx.Tests.MoeRouteMemory
import Ptx.Kernels.MoeRouteStream

/-! The actual route component publishes routing into the next initial heap.
No expert/combine contract is replaced by this one-stage regression. -/
namespace Ptx.MoeRouteStreamTests
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeRouteThread Ptx.MoeRouteEvent Ptx.MoeRouteMemoryTests
noncomputable section

def heap : Stream.Heap := fun address => initial ⟨.global,address⟩
def shared : Stream.SharedInitial := fun _ _ => .bits (byte 23)
def inv : Stream.Invocation := invocation cfg launch.params shared domain
theorem ready : HeapPre cfg gates heap := initialized

theorem published_routes {after : Stream.Heap} (hr : Stream.Runs [inv] heap after) :
    Stream.RepresentsWord after 128 0 ∧ Stream.RepresentsWord after 132 1 ∧
    Stream.RepresentsWord after 136 0 ∧ after 250 = .bits (byte 165) := by
  have hp := stream_correct cfg gates launch.params pre.2.1 shared domain covers heap after ready hr
  refine ⟨?_,?_,?_,?_⟩
  · simpa [rLoc,cfg,input,Moe.selected,gates,score] using hp.1 0 (by decide)
  · have h := hp.1 1 (by decide)
    norm_num [rLoc,cfg,input,Moe.selected,gates,score] at h
    exact h
  · simpa [rLoc,cfg,input,Moe.selected,gates,score] using hp.1 2 (by decide)
  · have h := hp.2 250 (by norm_num [InWords,cfg,input])
    simpa [heap,initial] using h

theorem legal_publication : ∃ after, Stream.Runs [inv] heap after ∧
    Stream.RepresentsWord after 128 0 ∧ Stream.RepresentsWord after 132 1 ∧
    Stream.RepresentsWord after 136 0 ∧ after 250 = .bits (byte 165) := by
  obtain ⟨after,hr⟩ := stream_nonvacuous cfg gates launch.params pre.2.1 shared domain covers domain_global heap ready
  exact ⟨after,hr,published_routes hr⟩

theorem initial_route_not_one : ¬ Stream.RepresentsWord heap 132 1 := by
  intro h
  have hh := h 0 (by decide)
  change Symbolic.Byte.bits (byte 165) = Symbolic.Byte.bits (byte 1) at hh
  exact (show byte 165 ≠ byte 1 by decide) (Symbolic.Byte.bits.inj hh)
theorem stale_route_initial_rejected : ¬ Stream.Runs [inv] heap heap := by
  intro h
  exact initial_route_not_one (published_routes h).2.1

def shortDomain : List Location := (List.range 11).map (fun offset => ⟨.global,128+offset⟩)
def lastId : ThreadId := ⟨⟨1,0,0⟩,.zero⟩
theorem last_valid : lastId.Valid geometry := by norm_num [lastId,geometry,ThreadId.Valid,Dim3.Within,Dim3.zero]
theorem short_domain_missing_byte : (⟨.global,139⟩ : Location) ∉ shortDomain := by decide

theorem incomplete_publication_rejected : ¬ CoversGlobalWrites (canonical cfg gates launch.params pre.2.1) shortDomain := by
  intro hcover
  let t := canonicalTrace cfg gates launch.params pre.2.1 lastId
  have ht := canonical_member cfg gates launch.params pre.2.1 last_valid
  have ha : Active cfg t.id := by simp [t,Active,index,col,lastId,cfg,input,geometry,Dim3.zero]
  have hstore := active_write (canonical_wellFormed cfg gates pre.1 pre.2.1)
    (canonical_complete cfg gates launch.params pre.2.1) pre.1 pre.2.1 ht ha
  change (canonical cfg gates launch.params pre.2.1).eventAt ⟨t.id,2⟩ =
    some (.write (rLoc cfg (index cfg t.id)) (u32Bytes (answer t.oracle))) at hstore
  have hbyte : (canonical cfg gates launch.params pre.2.1).writeByte ⟨t.id,2⟩
      ((rLoc cfg (index cfg t.id)).add 3) = some (u32Byte (answer t.oracle) 3) := by
    simpa only [Candidate.writeByte,hstore,Option.bind_some,Kind.writeByte] using
      u32_payload_byte (rLoc cfg (index cfg t.id)) (answer t.oracle) 3 (by decide)
  have hm := hcover _ _ _ rfl hbyte
  have he : (rLoc cfg (index cfg t.id)).add 3 = ⟨.global,139⟩ := by
    simp [t,rLoc,index,col,lastId,cfg,input,geometry,Dim3.zero,Location.add]
  exact short_domain_missing_byte (he ▸ hm)

end
end Ptx.MoeRouteStreamTests
