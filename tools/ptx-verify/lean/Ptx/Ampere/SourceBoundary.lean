import Ptx.Ampere.Origins
import Ptx.Ampere.Trace

/-! Lift actual plain prefix/step certificates to source-PC facts in arbitrary
complete candidate traces. Labels come from the real interpreter pre-state. -/
namespace Ptx.Ampere
open Ptx.ISA
noncomputable section

theorem source_pc_of_prefix {code launch candidate t k before after head emitted offset kind}
    (hw : WellFormed code launch candidate) (ht : t ∈ candidate.traces)
    (hp : run {id := t.id,params := launch.params,block := launch.geometry.block} t.oracle code k {} = .ok (before,head))
    (hs : step {id := t.id,params := launch.params,block := launch.geometry.block} t.oracle code before = .ok (after,emitted))
    (hk : k < t.count) (he : emitted[offset]? = some kind) :
    sourcePC candidate code launch.params launch.geometry.block ⟨t.id,head.length+offset⟩ = some before.scalar.core.thread.pc := by
  obtain ⟨located,hlocated,_⟩ := run_located_exists (hw.2.2.1 t ht).2
  have hcount : t.count = k+((t.count-k-1)+1) := by omega
  have hl := hlocated
  rw [hcount] at hl
  rw [run_eq_plain] at hp
  have hb := SourceRun.at_boundary hp hs hl he
  unfold sourcePC
  rw [sourceAt_of_trace hw.2.1 ht rfl]
  simp only [hlocated,Except.toOption,Option.bind_some,hb,Option.map_some]

end
end Ptx.Ampere
