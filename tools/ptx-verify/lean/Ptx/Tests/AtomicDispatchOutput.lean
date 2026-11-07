import Ptx.Tests.AtomicDispatch
import Ptx.Kernels.AtomicDispatchOutput

/-! Concrete universal output/frame regression. These conditional theorems do
not replace the separate two-CTA existence witness in AtomicDispatchWitness. -/
namespace Ptx.AtomicDispatchOutputTests
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.AtomicDispatchTrace Ptx.AtomicDispatchEvent Ptx.AtomicDispatchTests
noncomputable section

def domain : List Location := (List.range 256).map (fun address => ⟨.global,address⟩)

theorem covers : Covers cfg domain := by
  intro base hcell offset ho
  rcases hcell with rfl | rfl | rfl
  · exact List.mem_map.mpr ⟨0+offset,List.mem_range.mpr (by omega),rfl⟩
  · exact List.mem_map.mpr ⟨64+offset,List.mem_range.mpr (by omega),rfl⟩
  · exact List.mem_map.mpr ⟨128+offset,List.mem_range.mpr (by omega),rfl⟩

theorem contract : Scalar.Triple code (Pre cfg) (fun _ => domain)
    (fun launch output => Post cfg launch.initial output domain) := correct cfg domain covers

theorem observed_words {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution) (hm : GenericMemoryConditions execution initial rf co)
    (ho : ObserverConditions execution initial rf co o) (hdom : o.domain = domain) :
    o.output ⟨.global,0⟩ = .bits (byte 2) ∧ o.output ⟨.global,64⟩ = .bits (byte 1) ∧ o.output ⟨.global,128⟩ = .bits (byte 2) := by
  have h := Scalar.triple_apply contract pre hw hm ho hdom
  exact ⟨h.1 0 (by decide),h.2.1 0 (by decide),h.2.2.1 0 (by decide)⟩

theorem observed_frame {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution) (hm : GenericMemoryConditions execution initial rf co)
    (ho : ObserverConditions execution initial rf co o) (hdom : o.domain = domain) :
    o.output ⟨.global,250⟩ = .bits (byte 165) := by
  have h := Scalar.triple_apply contract pre hw hm ho hdom
  have hf := h.2.2.2 ⟨.global,250⟩ (by simp [domain])
    (by simp [InWords,cfg]) (by simp [InWords,cfg]) (by simp [InWords,cfg])
  simpa [launch,initial] using hf

theorem stale_counter_one_rejected {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution) (hm : GenericMemoryConditions execution initial rf co)
    (ho : ObserverConditions execution initial rf co o) (hdom : o.domain = domain) :
    o.output ⟨.global,0⟩ ≠ .bits (byte 1) := by
  rw [(observed_words hw hm ho hdom).1]
  intro he
  exact (show byte 2 ≠ byte 1 by decide) (Symbolic.Byte.bits.inj he)

theorem wrong_job_output_rejected {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution) (hm : GenericMemoryConditions execution initial rf co)
    (ho : ObserverConditions execution initial rf co o) (hdom : o.domain = domain) :
    o.output ⟨.global,128⟩ ≠ .bits (byte 1) := by
  rw [(observed_words hw hm ho hdom).2.2]
  intro he
  exact (show byte 2 ≠ byte 1 by decide) (Symbolic.Byte.bits.inj he)

theorem zeroed_frame_rejected {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution) (hm : GenericMemoryConditions execution initial rf co)
    (ho : ObserverConditions execution initial rf co o) (hdom : o.domain = domain) :
    o.output ⟨.global,250⟩ ≠ .bits (byte 0) := by
  rw [observed_frame hw hm ho hdom]
  intro he
  exact (show byte 165 ≠ byte 0 by decide) (Symbolic.Byte.bits.inj he)

end
end Ptx.AtomicDispatchOutputTests
