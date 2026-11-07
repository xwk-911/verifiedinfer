import Ptx.Kernels.AmpereTiledGraph
import Ptx.Scalar.Geometry

/-! Bounds and unique byte ownership for the four final stores of every lane.
All coordinates refer to the source-generated addresses and canonical launch. -/
namespace Ptx.AmpereTiledOutputLayout
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledGraph
noncomputable section

def row (id : ThreadId) (slot : Fin 4) : Nat := 16*id.cta.y+id.tid.y+8*(slot.val/2)
def col (id : ThreadId) (slot : Fin 4) : Nat := 8*id.cta.x+2*id.tid.x+slot.val%2

theorem coordinates {cfg : Config} (h : Layout cfg) {id : ThreadId}
    (hv : id.Valid (geometry cfg)) (ha : Active cfg) (slot : Fin 4) :
    row id slot < cfg.m ∧ col id slot < cfg.n := by
  have he := AmpereTiledGeometry.element_bounds h (ctx := {id := id,params := [],block := (geometry cfg).block}) hv ha
  dsimp only at he
  fin_cases slot <;> simp [row,col] <;> omega

theorem write_base {cfg : Config} (h : Layout cfg) {ctx : Scalar.Context}
    (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg) (slot : Fin 4) :
    AmpereTiledInventory.writeBase cfg ctx slot = cLocation cfg (row ctx.id slot) (col ctx.id slot) := by
  have hp := AmpereTiledAddressRules.global_formulas h hv ha
  have hc := coordinates h hv ha slot
  have hi := output_element_index hc.1 hc.2
  have hb := (h.output ha).1
  have h64 : cfg.c+4*(row ctx.id slot*cfg.n+col ctx.id slot) < 2^64 := by have hh := h.arena; omega
  have he : AmpereTiledInventory.writeBase cfg ctx slot =
      ⟨.global,wrap 64 (cfg.c+4*(row ctx.id slot*cfg.n+col ctx.id slot))⟩ := by
    fin_cases slot <;>
      simp [AmpereTiledInventory.writeBase,row,col,hp.2.2.2.1,hp.2.2.2.2,Scalar.wrap_add_left] <;>
      congr 1 <;> ring
  rw [he,show wrap 64 (cfg.c+4*(row ctx.id slot*cfg.n+col ctx.id slot)) = _ from Nat.mod_eq_of_lt h64]
  rfl

theorem byte_region {cfg : Config} (h : Layout cfg) {ctx : Scalar.Context}
    (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg) (slot : Fin 4) {loc value oracle}
    (hw : Ptx.Event.payloadByte (AmpereTiledInventory.writeBase cfg ctx slot)
      (AmpereTiledInventory.writeBytes cfg oracle slot) loc = some value) : InOutput cfg loc := by
  have hb := Ptx.Event.payloadByte_bounds hw
  rw [write_base h hv ha slot] at hb
  have hc := coordinates h hv ha slot
  have hi := output_element_index hc.1 hc.2
  have hlen : (AmpereTiledInventory.writeBytes cfg oracle slot).length = 4 := by
    simp [AmpereTiledInventory.writeBytes,Symbolic.encode_length,Symbolic.Format.bytes]
  rw [hlen] at hb
  exact ⟨hb.1.symm,by dsimp [cLocation] at hb; omega,by dsimp [cLocation] at hb; omega⟩

theorem coordinate_owner {cfg : Config} {a b : ThreadId} (ha : a.Valid (geometry cfg))
    (hb : b.Valid (geometry cfg)) {sa sb : Fin 4}
    (hr : row a sa = row b sb) (hc : col a sa = col b sb) : a = b ∧ sa = sb := by
  have hs := sa.isLt
  have ht := sb.isLt
  have haz : a.tid.z = 0 := by have hz : a.tid.z < 1 := ha.2.2.2; omega
  have hbz : b.tid.z = 0 := by have hz : b.tid.z < 1 := hb.2.2.2; omega
  have hacz : a.cta.z = 0 := by have hz : a.cta.z < 1 := ha.1.2.2; omega
  have hbcz : b.cta.z = 0 := by have hz : b.cta.z < 1 := hb.1.2.2; omega
  have hax : a.tid.x < 4 := ha.2.1
  have hbx : b.tid.x < 4 := hb.2.1
  have hay : a.tid.y < 8 := ha.2.2.1
  have hby : b.tid.y < 8 := hb.2.2.1
  dsimp only [row,col] at hr hc
  have hcx : a.cta.x = b.cta.x := by omega
  have hcy : a.cta.y = b.cta.y := by omega
  have htx : a.tid.x = b.tid.x := by omega
  have hty : a.tid.y = b.tid.y := by omega
  have hslot : sa = sb := Fin.ext (by omega)
  refine ⟨?_,hslot⟩
  cases a with
  | mk ac atid =>
    cases b with
    | mk bc btid =>
      cases ac; cases bc; cases atid; cases btid
      simp_all

theorem byte_owner {cfg : Config} (h : Layout cfg) {a b : ThreadId}
    (ha : a.Valid (geometry cfg)) (hb : b.Valid (geometry cfg)) (hactive : Active cfg)
    {sa sb : Fin 4} {address : Nat}
    (hal : cfg.c+4*(row a sa*cfg.n+col a sa) ≤ address)
    (hah : address < cfg.c+4*(row a sa*cfg.n+col a sa)+4)
    (hbl : cfg.c+4*(row b sb*cfg.n+col b sb) ≤ address)
    (hbh : address < cfg.c+4*(row b sb*cfg.n+col b sb)+4) : a = b ∧ sa = sb := by
  have hca := coordinates h ha hactive sa
  have hcb := coordinates h hb hactive sb
  have he : row a sa*cfg.n+col a sa = row b sb*cfg.n+col b sb := by omega
  obtain ⟨hr,hc⟩ := Scalar.tile_coordinate_injective hca.2 hcb.2 he
  exact coordinate_owner ha hb hr hc

/-- Every matrix element is covered by a valid canonical CTA/lane/store slot. -/
theorem covers_output {cfg : Config} (h : Layout cfg) {r c : Nat} (hr : r < cfg.m) (hc : c < cfg.n) :
    ∃ id : ThreadId, id.Valid (geometry cfg) ∧ ∃ slot : Fin 4, row id slot = r ∧ col id slot = c := by
  let id : ThreadId := ⟨⟨c/8,r/16,0⟩,⟨c%8/2,r%8,0⟩⟩
  let slot : Fin 4 := ⟨2*(r%16/8)+c%2,by omega⟩
  have hm := h.tiles.1
  have hn := h.tiles.2.1
  refine ⟨id,?_,slot,?_,?_⟩
  · simp only [id,ThreadId.Valid,Dim3.Within,geometry]
    constructor
    · exact ⟨by omega,by omega,by decide⟩
    · exact ⟨by omega,by omega,by decide⟩
  · dsimp only [row,id,slot]; omega
  · dsimp only [col,id,slot]; omega

end
end Ptx.AmpereTiledOutputLayout
