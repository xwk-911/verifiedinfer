import Ptx.Hopper.TmaGraph

/-! Source-derived TMA reply shape, real query indices and actual issue identity.
No descriptor or payload value is assumed to agree with input memory here. -/
namespace Ptx.Hopper
open Ptx.ISA
noncomputable section

theorem tma_step {ctx oracle code s dst descriptor x y barrier dstAddr descriptorAddr px py barrierAddr}
    (hr : s.scalar.core.thread.status = .running)
    (hi : code[s.scalar.core.thread.pc]? = some (.tmaLoad2D dst descriptor x y barrier))
    (hd : evalAddr ctx.id.tid.x s.scalar.core.thread dst = .ok dstAddr)
    (hm : Ptx.eval ctx.id.tid.x s.scalar.core.thread descriptor = .ok descriptorAddr)
    (hx : Ptx.eval ctx.id.tid.x s.scalar.core.thread x = .ok px)
    (hy : Ptx.eval ctx.id.tid.x s.scalar.core.thread y = .ok py)
    (hb : evalAddr ctx.id.tid.x s.scalar.core.thread barrier = .ok barrierAddr)
    (hs : (oracle.tmaBytes (s.scalar.core.queries+1)).length = (oracle.descriptor s.scalar.core.queries).bytes) :
    step ctx oracle code s = .ok (issueTma s
      ⟨wrap 64 descriptorAddr,oracle.descriptor s.scalar.core.queries,⟨Tma.signed32 px,Tma.signed32 py⟩,
        dstAddr,barrierAddr,s.scalar.core.queries,oracle.tmaBytes (s.scalar.core.queries+1)⟩) := by
  simp [step,hr,hi,hd,hm,hx,hy,hb,hs,liftInteger,bind,Except.bind,pure,Except.pure]

theorem step_tma_shape {ctx oracle code s next emitted copy}
    (hs : step ctx oracle code s = .ok (next,emitted)) (hm : Event.tmaIssue copy ∈ emitted) :
    copy.payload.length = copy.descriptor.bytes ∧ copy.queryBase = s.scalar.core.queries ∧
      copy.descriptor = oracle.descriptor s.scalar.core.queries ∧
      copy.payload = oracle.tmaBytes (s.scalar.core.queries+1) ∧ next.scalar.core.queries = s.scalar.core.queries+2 := by
  simp only [step,liftInteger,liftAmpere,issueTma,bind,Except.bind,pure,Except.pure] at hs
  repeat' first | split at hs | (cases hs)
  all_goals simp_all

theorem step_tma_instruction {ctx oracle code s next emitted copy}
    (hs : step ctx oracle code s = .ok (next,emitted)) (hm : Event.tmaIssue copy ∈ emitted) :
    ∃ dst descriptor x y barrier, code[s.scalar.core.thread.pc]? = some (.tmaLoad2D dst descriptor x y barrier) := by
  simp only [step,liftInteger,liftAmpere,issueTma,bind,Except.bind,pure,Except.pure] at hs
  repeat' first | split at hs | (cases hs)
  all_goals simp_all

theorem tma_copy_payload_length {c : Candidate} {code launch id copy}
    (hw : WellFormed code launch c) (he : Tma.copyAt c id = some copy) : copy.payload.length = copy.descriptor.bytes := by
  obtain ⟨_,_,_,oracle,before,after,emitted,hs,hm,_⟩ := Tma.copy_has_source hw he
  exact (step_tma_shape hs hm).1

end
end Ptx.Hopper
