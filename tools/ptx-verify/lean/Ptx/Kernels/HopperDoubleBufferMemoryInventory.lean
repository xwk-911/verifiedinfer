import Ptx.Kernels.HopperDoubleBufferNativeControl
import Ptx.Hopper.AccessInversion

/-! Exhaustive shared-writer source inventory. Ordinary accesses in the actual
rich source are global output stores or CTA events; there is no non-bulk copy.
This inventory does not choose RF/co or admit a complete memory execution. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def memoryShape : Hopper.Event → Bool
  | .ampere (.ordinary kind) => match kind with
    | .write loc _ => loc.space == .global
    | .barrierArrival _ _ | .barrierReturn _ _ => true
    | _ => false
  | .ampere (.issue _ _) => false
  | _ => true
def sourceMemoryShape (event : Wgmma.Event) : Bool := memoryShape (Unified.eventView event)

theorem initialization_memory_shape (leader : Bool) : (initializationEvents leader).all sourceMemoryShape = true := by
  cases leader <;> rfl
theorem data_initial_memory_shape (a b tiles lane) : (dataInitialEvents a b tiles lane).all sourceMemoryShape = true := by
  cases hl : HopperStage.leader lane <;> simp only [dataInitialEvents,hl] <;> rfl
theorem prelude_memory_shape (context oracle s tile tiles leader mapA mapB) :
    (preludeEvents context oracle s tile tiles leader mapA mapB).all sourceMemoryShape = true := by
  unfold preludeEvents
  split_ifs <;> rfl
theorem data_iteration_memory_shape (a b tiles tile lane) : (dataIterationEvents a b tiles tile lane).all sourceMemoryShape = true := by
  simp only [dataIterationEvents,iterationEvents,List.replicate_zero,List.nil_append,List.all_append,prelude_memory_shape]
  rfl
theorem output_memory_shape (context s lane leader values) : (outputEvents context s lane leader values).all sourceMemoryShape = true := by
  cases leader <;> rfl
theorem data_loop_memory_shape (a b tiles lane n) : (dataLoopEvents a b tiles lane n).all sourceMemoryShape = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs : dataLoopEvents a b tiles lane (n+1) = dataLoopEvents a b tiles lane n++dataIterationEvents a b tiles n lane := by
      simp only [dataLoopEvents,loopEvents,dataIterationEvents,dataCheckpoint,Nat.zero_add,zeroRetries]
    rw [hs,List.all_append,ih,data_iteration_memory_shape]
    rfl
theorem data_complete_memory_shape (a b tiles lane) : (dataCompleteEvents a b tiles lane).all sourceMemoryShape = true := by
  simp only [dataCompleteEvents,List.all_append,output_memory_shape,Bool.and_true]
  by_cases hz : tiles = 0
  · simp only [dataPreOutputEvents,hz,ite_true,initialization_memory_shape]
  · simp only [dataPreOutputEvents,hz,ite_false,dataKernelLoopEvents]
    change (dataInitialEvents a b tiles lane++dataLoopEvents a b tiles lane tiles).all sourceMemoryShape = true
    rw [List.all_append,data_initial_memory_shape,data_loop_memory_shape]
    rfl

theorem data_candidate_memory_shape {a b tiles id event}
    (he : (dataCompleteCandidate a b tiles).eventAt id = some event) : sourceMemoryShape event = true := by
  obtain ⟨trace,ht,_,hget⟩ := Unified.eventAt_trace he
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
  exact List.all_eq_true.mp (data_complete_memory_shape a b tiles lane) event (List.mem_of_getElem? hget)

theorem data_view_memory_shape {a b tiles id event}
    (he : (dataCompleteCandidate a b tiles).view.eventAt id = some event) : memoryShape event = true := by
  rw [Unified.view_eventAt] at he
  obtain ⟨rich,hr,rfl⟩ := Option.map_eq_some_iff.mp he
  exact data_candidate_memory_shape hr

theorem data_no_nonbulk (a b tiles) (id : Ptx.Event.EventId) :
    Access.copyAt (dataCompleteCandidate a b tiles).view id = none := by
  cases hc : Access.copyAt (dataCompleteCandidate a b tiles).view id with
  | none => rfl
  | some op =>
    obtain ⟨ordinal,he⟩ := Access.nonbulk_has_actual_issue hc
    have hs := data_view_memory_shape he
    cases hs

theorem data_ordinary_shared_write_none (a b tiles) (id : Ptx.Event.EventId) (loc : Location)
    (hl : loc.space = .shared .zero) :
    Access.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles).view (.tma (.source id)) loc = none := by
  cases he : (dataCompleteCandidate a b tiles).view.eventAt id with
  | none => simp only [Access.writeByte,Access.kind,he,Option.bind_none]
  | some event =>
    have hs := data_view_memory_shape he
    simp only [Access.writeByte,Access.kind,he,Option.bind_some]
    cases event with
    | ampere event =>
      cases event with
      | ordinary kind =>
        cases kind <;> try cases hs
        case write base bytes =>
          have hg : base.space = .global := by simpa only [memoryShape,beq_iff_eq] using hs
          simp [Ptx.Event.Kind.writeByte,Ptx.Event.payloadByte,hg,hl]
        all_goals rfl
      | issue _ _ | commit _ | wait _ _ | mmaEntry _ | mmaReturn _ => rfl
    | tmaIssue _ | proxyFenceAsyncShared _ | barrier _ | wgmma _ => rfl

theorem data_shared_writer_is_tensor {a b tiles writer loc value} (hl : loc.space = .shared .zero)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) writer loc = some value) :
    ∃ id offset, writer = .base (.tma (.write id offset)) ∧
      Tma.writeLocation Tma.localShared (dataCompleteCandidate a b tiles).view id offset = some loc := by
  cases writer with
  | wgmmaRead issue operand => rw [Unified.native_write_none] at hw; cases hw
  | base node =>
    cases node with
    | copyRead issue | copyWrite issue => simp [Unified.writeByte,Unified.kind,Access.kind,data_no_nonbulk] at hw
    | tma node =>
      cases node with
      | source id => rw [Unified.base_write_preserved,data_ordinary_shared_write_none a b tiles id loc hl] at hw; cases hw
      | descriptor id => rw [Unified.base_write_preserved,Access.descriptor_no_write] at hw; cases hw
      | read id offset => rw [Unified.base_write_preserved,Access.tensor_read_no_write] at hw; cases hw
      | notify id => cases hw
      | write id offset =>
        exact ⟨id,offset,rfl,Access.tensor_write_access (.inr (by rw [← Unified.base_write_preserved,hw]; rfl))⟩

end
end Ptx.Kernels.HopperDoubleBuffer
