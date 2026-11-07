import Ptx.Hopper.WgmmaInputs
import Ptx.Hopper.WgmmaRules

/-! Relocatable source MMA step. Operand byte replies and arithmetic replies
are captured at the actual query and emitted by the fetched instruction. -/
namespace Ptx.Hopper.Wgmma
open Ptx.ISA
noncomputable section

theorem mma_execute {ctx oracle code s d a b scaleD pa pb scale input}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some (.wgmma (.mma d a b scaleD)))
    (hf : s.ledger.fenced = true) (hd : d.names.Nodup)
    (hp : d.names.find? (fun name => s.ledger.dirty.contains name) = none)
    (ha : Ptx.eval ctx.id.tid.x s.base.scalar.core.thread (.reg a) = .ok pa)
    (hb : Ptx.eval ctx.id.tid.x s.base.scalar.core.thread (.reg b) = .ok pb)
    (hs : Ptx.eval ctx.id.tid.x s.base.scalar.core.thread scaleD = .ok scale)
    (hc : readScaledAccumulator s d scale = .ok input) :
    step ctx oracle code s = .ok (issueState s (makeCall ctx s oracle d pa pb (scale != 0) input),
      [.mma (mark ctx s) (makeCall ctx s oracle d pa pb (scale != 0) input)]) := by
  simp only [List.contains_eq_mem] at hp
  simp [step,hr,hi,hf,hd,hp,ha,hb,hs,hc,liftInteger,bind,Except.bind,pure,Except.pure]

theorem issued_operand_reply {ctx oracle s d pa pb useD input} (operand : OperandByte) :
    (makeCall ctx s oracle d pa pb useD input).operandBytes operand.index =
      oracle.operands s.base.scalar.core.queries operand.index := rfl
theorem issue_preserves_call_history (s : State) (call : Call) :
    (issueState s call).ledger.calls = s.ledger.calls++[call] := rfl

end
end Ptx.Hopper.Wgmma
