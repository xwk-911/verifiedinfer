import Ptx.Kernels.AmpereTiledPhaseOrder

/-! Actual shared-byte writers are copy nodes. Within one K phase, cooperative
copy ownership makes their byte footprints disjoint. Later phases may reuse
the bytes; no unique-writer assumption is imposed across the complete run. -/
namespace Ptx.AmpereTiledSharedWriters
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledTrace Ptx.AmpereTiledEvents Ptx.AmpereTiledGraph
noncomputable section

def copyBase (id : ThreadId) (part : Fin 3) : Nat := 256*part.val+32*id.tid.y+8*id.tid.x

theorem shared_write_info {cfg launch candidate node loc value cta} (h : SourceInfo cfg launch candidate)
    (hs : loc.space = .shared cta) (hw : candidate.writeByte node loc = some value) :
    ∃ t ∈ candidate.traces, ∃ r : ReplySet cfg (context launch t.id) t.oracle,
      ∃ phase, phase < cfg.k/16 ∧ ∃ part : Fin 3,
        node = .copyWrite ⟨t.id,3*phase+part.val⟩ ∧ loc.space = .shared t.id.cta ∧
          copyBase t.id part ≤ loc.address ∧ loc.address < copyBase t.id part+8 := by
  rcases AmpereTiledGraph.write_cases h hw with ⟨t,ht,r,slot,_,hp⟩ | ⟨t,ht,r,phase,hphase,part,hn,hp⟩
  · have hb := Ptx.Event.payloadByte_bounds hp
    have he : AddressSpace.global = loc.space := hb.1
    rw [hs] at he
    cases he
  · have hb := Ptx.Event.payloadByte_bounds hp
    have hv : (context launch t.id).id.Valid (geometry cfg) := by simpa only [h.geometry,context] using (h.formed.2.2.1 t ht).1
    rw [operation_destination (cfg := cfg) (context launch t.id) t.oracle r hv phase part,
      operation_size cfg (context launch t.id) t.oracle r phase hphase part] at hb
    change AddressSpace.shared t.id.cta = loc.space ∧ copyBase t.id part ≤ loc.address ∧ loc.address < copyBase t.id part+8 at hb
    exact ⟨t,ht,r,phase,hphase,part,hn,hb.1.symm,hb.2⟩

theorem owner_unique {a b : ThreadId} (ha : a.Valid (geometry cfg)) (hb : b.Valid (geometry cfg))
    (hcta : a.cta = b.cta) {part part' : Fin 3} {address : Nat}
    (hal : copyBase a part ≤ address) (hah : address < copyBase a part+8)
    (hbl : copyBase b part' ≤ address) (hbh : address < copyBase b part'+8) : a = b ∧ part = part' := by
  let x : Tiled.X := ⟨a.tid.x,ha.2.1⟩
  let y : Tiled.Y := ⟨a.tid.y,ha.2.2.1⟩
  let x' : Tiled.X := ⟨b.tid.x,hb.2.1⟩
  let y' : Tiled.Y := ⟨b.tid.y,hb.2.2.1⟩
  let offset : Fin 8 := ⟨address-copyBase a part,by omega⟩
  let offset' : Fin 8 := ⟨address-copyBase b part',by omega⟩
  have hbase : Tiled.copyBase x y part+offset.val = Tiled.copyBase x' y' part'+offset'.val := by
    change copyBase a part+(address-copyBase a part) = copyBase b part'+(address-copyBase b part')
    omega
  obtain ⟨hx,hy,hpart,_⟩ := Tiled.copy_byte_owner_unique hbase
  have hax : a.tid.x = b.tid.x := congrArg Fin.val hx
  have hay : a.tid.y = b.tid.y := congrArg Fin.val hy
  have haz : a.tid.z = 0 := by have hz : a.tid.z < 1 := ha.2.2.2; omega
  have hbz : b.tid.z = 0 := by have hz : b.tid.z < 1 := hb.2.2.2; omega
  refine ⟨?_,hpart⟩
  cases a with
  | mk ac atid =>
    cases b with
    | mk bc btid =>
      cases atid
      cases btid
      simp_all

theorem phase_unique {cfg launch candidate} {a b : Node} (h : SourceInfo cfg launch candidate) {cta loc va vb}
    (hs : loc.space = .shared cta) (hwa : candidate.writeByte a loc = some va) (hwb : candidate.writeByte b loc = some vb)
    {phase : Nat} {owner owner' : ThreadId} {part part' : Fin 3} (ha : a = .copyWrite ⟨owner,3*phase+part.val⟩)
    (hb : b = .copyWrite ⟨owner',3*phase+part'.val⟩) : a = b := by
  obtain ⟨ta,hta,ra,pa,hpa,ia,hna,hsa,hla,hha⟩ := shared_write_info h hs hwa
  obtain ⟨tb,htb,rb,pb,hpb,ib,hnb,hsb,hlb,hhb⟩ := shared_write_info h hs hwb
  have hpa' : pa = phase := by
    have he := ha.symm.trans hna
    have ho : 3*phase+part.val = 3*pa+ia.val := by injection he with hid; exact congrArg CopyId.ordinal hid
    have hi := part.isLt
    have hj := ia.isLt
    omega
  have hpb' : pb = phase := by
    have he := hb.symm.trans hnb
    have ho : 3*phase+part'.val = 3*pb+ib.val := by injection he with hid; exact congrArg CopyId.ordinal hid
    have hi := part'.isLt
    have hj := ib.isLt
    omega
  have hcta : ta.id.cta = tb.id.cta := by have he := hsa.symm.trans hsb; exact AddressSpace.shared.inj he
  have hva : ta.id.Valid (geometry cfg) := by simpa only [h.geometry] using (h.formed.2.2.1 ta hta).1
  have hvb : tb.id.Valid (geometry cfg) := by simpa only [h.geometry] using (h.formed.2.2.1 tb htb).1
  obtain ⟨hid,hipart⟩ := owner_unique hva hvb hcta hla hha hlb hhb
  rw [hna,hnb,hid,hipart,hpa',hpb']

end
end Ptx.AmpereTiledSharedWriters
