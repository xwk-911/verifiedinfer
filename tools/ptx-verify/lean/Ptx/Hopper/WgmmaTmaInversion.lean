import Ptx.Hopper.WgmmaTmaSteps
import Ptx.Hopper.WgmmaTrace

/-! A successfully executed actual TMA instruction forces its payload shape.
No address/value/profile/memory agreement or completed transfer is inferred.
-/
namespace Ptx.Hopper
open Ptx.ISA
noncomputable section

theorem successful_tma_payload_shape {ctx oracle code s next events dst descriptor x y barrier}
    (hr : s.scalar.core.thread.status = .running)
    (hi : code[s.scalar.core.thread.pc]? = some (.tmaLoad2D dst descriptor x y barrier))
    (hs : step ctx oracle code s = .ok (next,events)) :
    (oracle.tmaBytes (s.scalar.core.queries+1)).length = (oracle.descriptor s.scalar.core.queries).bytes := by
  simp only [step,hr,hi,liftInteger,issueTma,bind,Except.bind,pure,Except.pure] at hs
  repeat' first | split at hs | cases hs
  all_goals simp_all

namespace Wgmma

theorem successful_tma_payload_shape {ctx oracle code s next events dst descriptor x y barrier}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some (.tmaLoad2D dst descriptor x y barrier))
    (hs : step ctx oracle code s = .ok (next,events)) :
    (oracle.base.tmaBytes (s.base.scalar.core.queries+1)).length = (oracle.base.descriptor s.base.scalar.core.queries).bytes := by
  cases hbase : Hopper.step ctx oracle.base code s.base with
  | error fault =>
    simp [step,hr,hi,liftBase,hbase,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs
    split at hs <;> simp_all
  | ok result => exact Hopper.successful_tma_payload_shape hr hi hbase

theorem completed_tma_shape_after_prefix {ctx oracle code s count last events k mid head dst descriptor x y barrier}
    (hn : run ctx oracle code count s = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done)
    (hk : run ctx oracle code k s = .ok (mid,head)) (hr : mid.base.scalar.core.thread.status = .running)
    (hi : code[mid.base.scalar.core.thread.pc]? = some (.tmaLoad2D dst descriptor x y barrier)) :
    (oracle.base.tmaBytes (mid.base.scalar.core.queries+1)).length = (oracle.base.descriptor mid.base.scalar.core.queries).bytes := by
  obtain ⟨next,emitted,hs⟩ := step_after_running_prefix hn hd hk hr
  exact successful_tma_payload_shape hr hi hs

end Wgmma
end
end Ptx.Hopper
