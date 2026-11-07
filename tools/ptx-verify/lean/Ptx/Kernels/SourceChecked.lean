import Ptx.Event.Checked
import Ptx.Kernels.BarrierPublishUniversal
import Ptx.Kernels.CopyEventWitness
import Ptx.Kernels.SharedEventWitness

/-! Source-aware contracts and independent nonvacuity for existing kernel
families. Source alignment is derived from emitted source and static certificates;
it is not added to the caller's preconditions. -/
namespace Ptx.SourceChecked
open Ptx.ISA Ptx.Event

theorem publication_sites : uniqueBarrierSites BarrierPublish.code = true := by decide
theorem shared_sites : uniqueBarrierSites SharedEvent.code = true := by decide
theorem copy_sites : uniqueBarrierSites CopyEvent.code = true := by decide

theorem publication_correct (base value : Nat) :
    CheckedTriple BarrierPublish.code (BarrierPublish.Pre base value) (fun _ => BarrierPublish.wordDomain base)
      (fun _ output => BarrierPublish.outputWord output base = wrap 32 value) :=
  triple_checked (BarrierPublish.correct base value)

theorem publication_nonvacuous (base value : Nat) :
    CheckedNonvacuous BarrierPublish.code (BarrierPublish.Pre base value) (fun _ => BarrierPublish.wordDomain base) :=
  nonvacuous_checked_of_unique_sites publication_sites (BarrierPublish.nonvacuous base value)

theorem copy_correct (cfg : CopyContract.Config) :
    CheckedTriple CopyEvent.code (CopyEvent.Pre cfg) (fun _ => CopyEvent.domain cfg)
      (fun launch output => CopyEvent.BytePost cfg launch.initial output) :=
  triple_checked (CopyEvent.correct cfg)

theorem copy_nonvacuous (cfg : CopyContract.Config) :
    CheckedNonvacuous CopyEvent.code (CopyEvent.Pre cfg) (fun _ => CopyEvent.domain cfg) :=
  nonvacuous_checked_of_unique_sites copy_sites (CopyEvent.nonvacuous cfg)

theorem shared_correct (cfg : SharedContract.Config) :
    CheckedTriple SharedEvent.code (SharedEvent.Pre cfg) (fun _ => SharedEvent.domain cfg)
      (fun launch output => SharedEvent.BytePost cfg launch.initial output) :=
  triple_checked (SharedEvent.correct cfg)

theorem shared_nonvacuous (cfg : SharedContract.Config) :
    CheckedNonvacuous SharedEvent.code (SharedEvent.Pre cfg) (fun _ => SharedEvent.domain cfg) :=
  nonvacuous_checked_of_unique_sites shared_sites (SharedEvent.nonvacuous cfg)

end Ptx.SourceChecked
