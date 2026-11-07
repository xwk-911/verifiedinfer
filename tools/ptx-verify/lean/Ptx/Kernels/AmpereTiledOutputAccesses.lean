import Ptx.Kernels.AmpereTiledObservation

/-! Every output element is an actual source store, and a complete admitted
observer sees its f32 accumulator encoding. The equality of that accumulator
with the independent matrix product remains an MMA/fragment proof obligation. -/
namespace Ptx.AmpereTiledOutputAccesses
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledTrace Ptx.AmpereTiledGraph
noncomputable section

theorem output_event {cfg launch candidate} (h : SourceInfo cfg launch candidate) {id : ThreadId}
    (hv : id.Valid launch.geometry) (slot : Fin 4) :
    ∃ t ∈ candidate.traces, t.id = id ∧ candidate.eventAt ⟨id,17*(cfg.k/16)+slot.val⟩ =
      some (.ordinary (.write (AmpereTiledInventory.writeBase cfg (context launch id) slot)
        (AmpereTiledInventory.writeBytes cfg t.oracle slot))) := by
  obtain ⟨t,ht,hid⟩ := h.formed.2.2.2 id hv
  obtain ⟨r,_,_,he⟩ := trace_view h ht
  subst id
  refine ⟨t,ht,rfl,?_⟩
  rw [member_event h ht,he,AmpereTiledEvents.output_event]
  exact AmpereTiledInventory.finish_write _ _ _ slot

theorem output_word {cfg launch candidate rf co o} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co) (ho : ObserverConstraints candidate launch.initial rf co o)
    (hd : o.domain = domain cfg) {id : ThreadId} (hv : id.Valid launch.geometry) (slot : Fin 4) :
    ∃ t ∈ candidate.traces, t.id = id ∧
      Scalar.RepresentsReal .f32 o.output (AmpereTiledInventory.writeBase cfg (context launch id) slot)
        (cValues t.oracle (cfg.k/16) slot) := by
  obtain ⟨t,ht,hid,he⟩ := output_event h hv slot
  have hvalid : (context launch id).id.Valid (geometry cfg) := by simpa only [context,h.geometry] using hv
  have hbase := AmpereTiledOutputLayout.write_base h.layout hvalid h.active slot
  have hcoords := AmpereTiledOutputLayout.coordinates h.layout hvalid h.active slot
  refine ⟨t,ht,hid,?_⟩
  intro offset hoff
  have hb := Scalar.encoded_byte .f32 (cValues t.oracle (cfg.k/16) slot)
    (AmpereTiledInventory.writeBase cfg (context launch id) slot) hoff
  have hw : candidate.writeByte (.thread ⟨id,17*(cfg.k/16)+slot.val⟩)
      ((AmpereTiledInventory.writeBase cfg (context launch id) slot).add offset) =
      some (.realPart .f32 (cValues t.oracle (cfg.k/16) slot) offset) := by
    simpa only [Candidate.writeByte,Candidate.memoryKind,he,Option.bind_some,Ptx.Event.Kind.writeByte,
      AmpereTiledInventory.writeBytes] using hb
  apply AmpereTiledObservation.output_store h hm ho (writer := .thread ⟨id,17*(cfg.k/16)+slot.val⟩) ?_ rfl hw
  rw [hd,hbase]
  exact output_byte_in_domain h.layout hcoords.1 hcoords.2 hoff

theorem every_output_word {cfg launch candidate rf co o} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co) (ho : ObserverConstraints candidate launch.initial rf co o)
    (hd : o.domain = domain cfg) {r c : Nat} (hr : r < cfg.m) (hc : c < cfg.n) :
    ∃ id : ThreadId, id.Valid launch.geometry ∧ ∃ slot : Fin 4, ∃ t ∈ candidate.traces, t.id = id ∧
      AmpereTiledOutputLayout.row id slot = r ∧ AmpereTiledOutputLayout.col id slot = c ∧
      Scalar.RepresentsReal .f32 o.output (cLocation cfg r c) (cValues t.oracle (cfg.k/16) slot) := by
  obtain ⟨id,hv,slot,hrow,hcol⟩ := AmpereTiledOutputLayout.covers_output h.layout hr hc
  have hvl : id.Valid launch.geometry := by simpa only [h.geometry] using hv
  obtain ⟨t,ht,hid,hw⟩ := output_word h hm ho hd hvl slot
  have hb := AmpereTiledOutputLayout.write_base h.layout (ctx := context launch id) hv h.active slot
  rw [hb] at hw
  dsimp only [context] at hw
  rw [hrow,hcol] at hw
  exact ⟨id,hvl,slot,t,ht,hid,hrow,hcol,hw⟩

end
end Ptx.AmpereTiledOutputAccesses
