import Ptx.Hopper.UnifiedComponents
import Ptx.Hopper.UnifiedVisibility

/-! An admitted TMA-ready operand has an actual source-produced byte writer.
This is byte existence, not read-from/value agreement at the operand read. -/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

theorem tma_ready_writer_byte {resolve descriptor candidate code launch histories cluster copy offset issue operand loc}
    (hw : WellFormed code launch candidate) (hr : TmaReady resolve candidate histories cluster copy offset issue operand loc) :
    ∃ value, writeByte resolve descriptor candidate (.base (.tma (.write copy offset))) loc = some value := by
  obtain ⟨op,hcopy,ho⟩ := tma_ready_has_actual_writer hr
  obtain ⟨value,hv,_⟩ := tensor_byte_present (resolve := resolve) (descriptor := descriptor) hw hcopy ho
  obtain ⟨_,hl,_,_⟩ := hr
  exact ⟨value,Access.tensor_write (descriptor := descriptor) hl hv⟩

end
end Ptx.Hopper.Unified
