import Ptx.Kernels.AmpereTiledOutputLayout

/-! Global input reads cannot overlap an output store. Output bytes have one
actual writer across the complete canonical launch, including all CTAs. -/
namespace Ptx.AmpereTiledGlobalAccesses
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledTrace Ptx.AmpereTiledGraph Ptx.AmpereTiledEvents
noncomputable section

theorem global_write_cases {cfg launch candidate node loc value} (h : SourceInfo cfg launch candidate)
    (hs : loc.space = .global) (hw : candidate.writeByte node loc = some value) :
    ∃ t ∈ candidate.traces, ∃ slot : Fin 4,
      node = .thread ⟨t.id,17*(cfg.k/16)+slot.val⟩ ∧
      Ptx.Event.payloadByte (AmpereTiledInventory.writeBase cfg (context launch t.id) slot)
        (AmpereTiledInventory.writeBytes cfg t.oracle slot) loc = some value := by
  rcases AmpereTiledGraph.write_cases h hw with ⟨t,ht,_,slot,hn,hp⟩ | ⟨t,ht,r,phase,_,part,_,hp⟩
  · exact ⟨t,ht,slot,hn,hp⟩
  · have hb := Ptx.Event.payloadByte_bounds hp
    have hv : (context launch t.id).id.Valid (geometry cfg) := by
      simpa only [h.geometry,context] using (h.formed.2.2.1 t ht).1
    rw [operation_destination (cfg := cfg) (context launch t.id) t.oracle r hv phase part] at hb
    have he : AddressSpace.shared t.id.cta = .global := hb.1.trans hs
    cases he

theorem global_write_region {cfg launch candidate node loc value} (h : SourceInfo cfg launch candidate)
    (hs : loc.space = .global) (hw : candidate.writeByte node loc = some value) : InOutput cfg loc := by
  obtain ⟨t,ht,slot,_,hp⟩ := global_write_cases h hs hw
  have hv : (context launch t.id).id.Valid (geometry cfg) := by
    simpa only [h.geometry,context] using (h.formed.2.2.1 t ht).1
  exact AmpereTiledOutputLayout.byte_region h.layout hv h.active slot hp

theorem global_writer_unique {cfg launch candidate a b loc va vb} (h : SourceInfo cfg launch candidate)
    (hs : loc.space = .global) (hwa : candidate.writeByte a loc = some va)
    (hwb : candidate.writeByte b loc = some vb) : a = b := by
  obtain ⟨ta,hta,sa,hna,hpa⟩ := global_write_cases h hs hwa
  obtain ⟨tb,htb,sb,hnb,hpb⟩ := global_write_cases h hs hwb
  have hva : (context launch ta.id).id.Valid (geometry cfg) := by
    simpa only [h.geometry,context] using (h.formed.2.2.1 ta hta).1
  have hvb : (context launch tb.id).id.Valid (geometry cfg) := by
    simpa only [h.geometry,context] using (h.formed.2.2.1 tb htb).1
  have hba := Ptx.Event.payloadByte_bounds hpa
  have hbb := Ptx.Event.payloadByte_bounds hpb
  rw [AmpereTiledOutputLayout.write_base h.layout hva h.active sa] at hba
  rw [AmpereTiledOutputLayout.write_base h.layout hvb h.active sb] at hbb
  have hlen (oracle : Oracle) (slot : Fin 4) : (AmpereTiledInventory.writeBytes cfg oracle slot).length = 4 := by
    simp [AmpereTiledInventory.writeBytes,Symbolic.encode_length,Symbolic.Format.bytes]
  rw [hlen] at hba hbb
  obtain ⟨hid,hslot⟩ := AmpereTiledOutputLayout.byte_owner h.layout hva hvb h.active hba.2.1 hba.2.2 hbb.2.1 hbb.2.2
  change ta.id = tb.id at hid
  rw [hna,hnb,hid,hslot]

theorem global_read_region {cfg launch candidate node loc value} (h : SourceInfo cfg launch candidate)
    (hs : loc.space = .global) (hr : candidate.readByte node loc = some value) : 0 < cfg.k ∧
    ((cfg.a ≤ loc.address ∧ loc.address < cfg.a+2*(cfg.m*cfg.k)) ∨
     (cfg.b ≤ loc.address ∧ loc.address < cfg.b+2*(cfg.n*cfg.k))) := by
  rcases AmpereTiledGraph.read_cases h hr with ⟨t,_,_,phase,_,reg,_,hp⟩ | ⟨t,ht,r,phase,hphase,part,_,hp⟩
  · have hb := Ptx.Event.payloadByte_bounds hp
    have he : AddressSpace.shared t.id.cta = .global := hb.1.trans hs
    cases he
  · have hv : (context launch t.id).id.Valid (geometry cfg) := by
      simpa only [h.geometry,context] using (h.formed.2.2.1 t ht).1
    have hb := Ptx.Event.payloadByte_bounds hp
    rw [operation_source h.layout (context launch t.id) t.oracle r hv h.active phase hphase part,
      operation_size cfg (context launch t.id) t.oracle r phase hphase part] at hb
    have hregion := AmpereTiledBounds.copy_region h.layout hv h.active hphase part
    refine ⟨by omega,?_⟩
    rcases hregion with ha | hb'
    · exact .inl ⟨by dsimp at hb; omega,by dsimp at hb; omega⟩
    · exact .inr ⟨by dsimp at hb; omega,by dsimp at hb; omega⟩

theorem global_read_unwritten {cfg launch candidate read loc value} (h : SourceInfo cfg launch candidate)
    (hs : loc.space = .global) (hr : candidate.readByte read loc = some value) (writer : Node) :
    candidate.writeByte writer loc = none := by
  obtain ⟨hk,hregion⟩ := global_read_region h hs hr
  have hd := h.layout.inputs h.active hk
  cases hw : candidate.writeByte writer loc with
  | none => rfl
  | some written =>
    have ho := global_write_region h hs hw
    rcases hregion with ha | hb
    · rcases hd.2.2.2.2.1 with hl | hh <;> rcases ho with ⟨_,_,_⟩ <;> omega
    · rcases hd.2.2.2.2.2 with hl | hh <;> rcases ho with ⟨_,_,_⟩ <;> omega

end
end Ptx.AmpereTiledGlobalAccesses
