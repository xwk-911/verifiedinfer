import Ptx.Tests.MoeExpertsMemory
import Ptx.Kernels.MoeExpertsStream

/-! Successor publication includes selected H bytes, leaves unselected H
untouched, and cannot reuse the stale input heap or omit a live output byte. -/
namespace Ptx.MoeExpertsStreamTests
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeExperts Ptx.MoeExpertsLoop Ptx.MoeExpertsEvent Ptx.MoeExpertsMemoryTests
noncomputable section

def heap : Stream.Heap := fun address => initial ⟨.global,address⟩
def shared : Stream.SharedInitial := fun _ _ => .bits (byte 23)
def inv : Stream.Invocation := invocation cfg launch.params shared domain
theorem ready : HeapPre cfg gates x weights heap := initialized

theorem published_result {after : Stream.Heap} (hr : Stream.Runs [inv] heap after) :
    Stream.Represents .f32 after 304 20 ∧ after 268 = .bits (byte 165) ∧ after 500 = .bits (byte 165) := by
  have hp := stream_correct cfg gates x weights launch.params pre.2.1 shared domain covers heap after ready hr
  refine ⟨?_,?_,?_⟩
  · have h := hp.1 1 0 (by decide) (by decide)
    norm_num [hLoc,cfg,input,Moe.selected,gates,Moe.output,Moe.linear,x,weights] at h
    exact h
  · have hu : ¬ SelectedByte cfg gates ⟨.global,268⟩ :=
      unselected_byte cfg gates (e := 0) (r := 1) (c := 0) (offset := 0) (by decide) (by decide) (by decide) (by norm_num [Moe.selected,gates])
    simpa [heap,initial] using hp.2 268 hu
  · have hu : ¬ SelectedByte cfg gates ⟨.global,500⟩ := by
      rintro ⟨r,c,offset,hr,hc,ho,he⟩
      have h := h_footprint cfg (Moe.selected_bound gates r) hr hc ho
      have hindex := Moe.selected_index_bound gates hr hc
      have heq := congrArg Location.address he
      change (Moe.selected gates r*3+r)*3+c < 18 at hindex
      change 500 = 256+4*((Moe.selected gates r*3+r)*3+c)+offset at heq
      omega
    simpa [heap,initial] using hp.2 500 hu

theorem legal_publication : ∃ after, Stream.Runs [inv] heap after ∧
    Stream.Represents .f32 after 304 20 ∧ after 268 = .bits (byte 165) ∧ after 500 = .bits (byte 165) := by
  obtain ⟨after,hr⟩ := stream_nonvacuous cfg gates x weights launch.params pre.2.1 shared domain covers domain_global heap ready
  exact ⟨after,hr,published_result hr⟩

theorem stale_heap_rejected : ¬ Stream.Runs [inv] heap heap := by
  intro h
  have hh := (published_result h).1 0 (by decide)
  norm_num [heap,initial] at hh

def shortDomain : List Location := (List.range 3).map (fun offset => ⟨.global,256+offset⟩)
theorem short_domain_missing_byte : (⟨.global,259⟩ : Location) ∉ shortDomain := by decide
theorem incomplete_publication_rejected :
    ¬ CoversGlobalWrites (canonical cfg gates x weights launch.params pre.2.1) shortDomain := by
  intro hcover
  let t := canonicalTrace cfg gates x weights launch.params pre.2.1 firstId
  have ht := canonical_member cfg gates x weights launch.params pre.2.1 first_valid
  have ha : Active cfg t.id := by simp [t,Active,canonical_trace_id,row,col,firstId,cfg,input,geometry,Dim3.zero]
  have he : expert t.oracle < 2 := by
    simp only [t,canonical_trace_oracle,expertOracle_expert]
    exact Moe.selected_bound _ _
  have hstore := active_write (canonical_wellFormed cfg gates x weights pre.1 pre.2.1)
    (canonical_complete cfg gates x weights launch.params pre.2.1) pre.1 pre.2.1 ht ha he
  change (canonical cfg gates x weights launch.params pre.2.1).eventAt ⟨t.id,1+2*cfg.input.k⟩ =
    some (.write (hLoc cfg (expert t.oracle) (row cfg.geometry.block t.id) (col cfg.geometry.block t.id))
      (Symbolic.encode .f32 (answer cfg t.oracle))) at hstore
  have hbyte : (canonical cfg gates x weights launch.params pre.2.1).writeByte ⟨t.id,1+2*cfg.input.k⟩
      ((hLoc cfg (expert t.oracle) (row cfg.geometry.block t.id) (col cfg.geometry.block t.id)).add 3) =
      some (.realPart .f32 (answer cfg t.oracle) 3) := by
    simpa only [Candidate.writeByte,hstore,Option.bind_some,Kind.writeByte] using encoded_byte .f32 _ _ (by decide : 3 < Symbolic.Format.f32.bytes)
  have hm := hcover _ _ _ rfl hbyte
  have hl : (hLoc cfg (expert t.oracle) (row cfg.geometry.block t.id) (col cfg.geometry.block t.id)).add 3 = ⟨.global,259⟩ := by
    simp [t,canonical_trace_id,canonical_trace_oracle,expertOracle_expert,hLoc,firstId,cfg,input,geometry,row,col,Dim3.zero,Location.add,Moe.selected,gates]
  exact short_domain_missing_byte (hl ▸ hm)

end
end Ptx.MoeExpertsStreamTests
