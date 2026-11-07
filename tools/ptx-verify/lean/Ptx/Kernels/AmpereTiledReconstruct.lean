import Ptx.Kernels.AmpereTiledSource
import Ptx.Kernels.AmpereTiledReplies

/-! Reply certificates and counts derived for every complete active PC-zero
source run, without any new caller premise. Values and memory admission remain
separate obligations. The full original kernel Pre is unchanged. -/
namespace Ptx.AmpereTiledReconstruct
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec
noncomputable section
abbrev code := Generated.ampere_tiled_matmul.program

theorem complete_replies {cfg : Config} (h : Layout cfg) (ctx : Scalar.Context) (oracle : Oracle)
    (hp : AmpereTiledInit.Params cfg ctx.params) (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg)
    {count last emitted} (hr : Ampere.run ctx oracle code count {} = .ok (last,emitted))
    (hd : last.scalar.core.thread.status = .done) :
    Nonempty (AmpereTiledLoop.Replies (AmpereTiledEntry.loopConfig cfg ctx) oracle) := by
  have hg := AmpereTiledGeometry.active_guards h hv ha
  have hi := AmpereTiledEntry.invariant cfg ctx h.dimensions.2.2 h.tiles.2.2
  have hpref := AmpereTiledEntry.source_prefix cfg ctx oracle hp hg.1 hg.2
  obtain ⟨n,e,_,ht,_⟩ := completed_tail hr hpref (Nat.le_of_lt (completed_after_running_prefix hr hd hpref hi.running))
  have hb : 16*(AmpereTiledEntry.loopConfig cfg ctx).tiles < 2^32 := by
    change 16*(cfg.k/16) < 2^32
    have hk := h.tiles.2.2
    have h32 := h.dimensions.2.2
    omega
  have hs := AmpereTiledReplies.suffix_shapes ctx oracle (cfg.k/16)
    (by simp [AmpereTiledEntry.loopConfig]) hi hb ht hd
  exact ⟨AmpereTiledReplies.fromShapes _ oracle (fun step hlt => hs step (by omega) hlt)⟩

theorem complete_counts {cfg : Config} (h : Layout cfg) (ctx : Scalar.Context) (oracle : Oracle)
    (hp : AmpereTiledInit.Params cfg ctx.params) (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg)
    {count last emitted} (hr : Ampere.run ctx oracle code count {} = .ok (last,emitted))
    (hd : last.scalar.core.thread.status = .done) :
    count = 64+21*(cfg.k/16) ∧ emitted.length = 17*(cfg.k/16)+4 ∧ last.scalar.core.queries = 10*(cfg.k/16) := by
  obtain ⟨replies⟩ := complete_replies h ctx oracle hp hv ha hr hd
  exact AmpereTiledSource.active_complete_counts h ctx oracle hp hv ha replies hr hd

end
end Ptx.AmpereTiledReconstruct
