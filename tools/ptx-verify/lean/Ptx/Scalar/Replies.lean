import Ptx.Scalar.Execution

/-! Value projection for reconstructing arbitrary source traces. Projection's
default is NOT evidence of a valid read; each use must establish the exact f32
reply constructor separately from a successful actual load. -/
namespace Ptx.Scalar
noncomputable section

def replyReal (oracle : Oracle) (query : Nat) : ℝ :=
  match oracle query with | .real _ value => value | .integer _ => 0

theorem replyReal_of_typed {oracle : Oracle} {query : Nat} {value : ℝ} (h : oracle query = .real .f32 value) :
    replyReal oracle query = value := by rw [replyReal,h]

theorem typed_reply_projection {oracle : Oracle} {query : Nat} (h : ∃ value, oracle query = .real .f32 value) :
    oracle query = .real .f32 (replyReal oracle query) := by
  obtain ⟨value,hv⟩ := h
  simpa only [replyReal_of_typed hv] using hv

theorem complete_after_prefix {ctx oracle code n k s last mid events headEvents}
    (hn : run ctx oracle code n s = .ok (last,events)) (hd : last.core.thread.status = .done)
    (hk : run ctx oracle code k s = .ok (mid,headEvents)) (hr : mid.core.thread.status = .running) :
    ∃ remaining tailEvents, n = k+remaining ∧
      run ctx oracle code remaining mid = .ok (last,tailEvents) ∧ events = headEvents ++ tailEvents :=
  successful_suffix (Nat.le_of_lt (completed_after_running_prefix hn hd hk hr)) hk hn

end
end Ptx.Scalar
