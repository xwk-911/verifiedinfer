import Ptx.Hopper.CompletionBridge
import Ptx.Hopper.CompletePrefix

/-! Lift an actual finite access-prefix execution into the coupled protocol
without changing its prepared stream queues or loans. -/
namespace Ptx.Hopper.Progress.Bridge
noncomputable section

theorem steps_trans {block resolve candidate histories cluster plan s mid last}
    (ha : Steps block resolve candidate histories cluster plan s mid)
    (hb : Steps block resolve candidate histories cluster plan mid last) : Steps block resolve candidate histories cluster plan s last := by
  induction ha with
  | refl => exact hb
  | next first rest ih => exact .next first (ih hb)

theorem prefix_execution {block resolve candidate histories cluster plan done}
    (protocol : Ptx.Async.State) (hr : Reached block candidate histories done) :
    Steps block resolve candidate histories cluster plan ⟨protocol,fun _ => False⟩ ⟨protocol,done⟩ := by
  induction hr with
  | empty => exact .refl _
  | next before advance ih => exact steps_trans ih (.next (.access advance) (.refl _))

end
end Ptx.Hopper.Progress.Bridge
