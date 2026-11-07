import Ptx.Kernels.ByteValuePipelineMemoryLink

/-! Full memory-admitted source and native heap execution coexist. Counter-
examples separate source/value agreement from legal RF/co: even equal zero
bytes cannot justify choosing initial memory after this ordered store.
-/
namespace Ptx.ByteValuePipelineMemoryTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels.ByteValuePipeline
open Iris Iris.BI Iris.ProgramLogic
noncomputable section

def initialRF : Unified.ReadsFrom := fun _ _ => none
def selfRF : Unified.ReadsFrom := fun _ _ => some readerMemory
def absentMemory : Unified.Node := .base (.tma (.source ⟨thread,2⟩))
def absentRF : Unified.ReadsFrom := fun _ _ => some absentMemory

theorem actual_joint_memory_and_native_witness (value : Nat) :
    Unified.TmaComponents program (launch value) (candidate value value) Tma.localShared (fun _ => none) (fun _ => []) ∧
    Unified.ControlAdmitted .one (candidate value value) (fun _ => []) ∧
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate value value) proxyInitial readWitness (coherence value value) (fun _ => []) cluster ∧
    adequate .NotStuck (ByteContentsHeap.script (context value value) actions) initialState (fun result _ => result = .ok (afterReader value value)) :=
  ⟨ordinary_tma_components value value,control_admitted value value,full_memory_witness value proxyInitial cluster,
    admitted_memory_native_adequate (full_memory_witness value proxyInitial cluster).toCausalConstraints⟩

theorem full_word_reply_has_admitted_memory :
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate 305419896 305419896) proxyInitial readWitness (coherence 305419896 305419896) (fun _ => []) cluster :=
  full_memory_witness _ _ _

theorem wrapped_reply_has_admitted_memory :
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate 4294967303 4294967303) proxyInitial readWitness (coherence 4294967303 4294967303) (fun _ => []) cluster :=
  full_memory_witness _ _ _

theorem all_admitted_sources_are_forced {value reply initialProxy rf co}
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate value reply) initialProxy rf co (fun _ => []) cluster) (offset : Fin 4) :
    rf readerMemory (base.add offset.val) = some writerMemory :=
  admitted_rf_is_actual_writer hm.toCausalConstraints (reader_byte_at value reply offset)

theorem every_admitted_reply_has_actual_native_run {value reply initialProxy rf co}
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate value reply) initialProxy rf co (fun _ => []) cluster) :
    IrisExecution.run (ByteContentsHeap.transition (context value reply)) actions initialState = .ok (afterReader value reply) :=
  admitted_memory_script_run hm.toCausalConstraints

theorem every_admitted_reply_has_correct_register {value reply initialProxy rf co}
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate value reply) initialProxy rf co (fun _ => []) cluster) :
    declarationLookup "%r" (trace value reply).final.base.scalar.core.thread.regs = some (wrap 32 value) :=
  admitted_memory_source_register hm.toCausalConstraints

theorem every_admitted_reply_has_closed_heap_adequacy {value reply initialProxy rf co}
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate value reply) initialProxy rf co (fun _ => []) cluster) :
    adequate .NotStuck (ByteContentsHeap.script (context value reply) actions) initialState (fun result _ => result = .ok (afterReader value reply)) :=
  admitted_memory_native_adequate hm.toCausalConstraints

theorem zero_initial_rf_agrees_on_values :
    Unified.ReadAgreement Tma.localShared Access.globalDescriptor (candidate 0 0) proxyInitial
      (Unified.Eligible Tma.localShared Access.globalDescriptor (candidate 0 0) (fun _ => []) cluster initialRF) initialRF := by
  intro read loc byteValue _ hr
  have he := reader_only hr
  subst read
  have hm : byteValue ∈ payload 0 := Ptx.Event.payloadByte_mem hr
  change byteValue ∈ [.bits (byte 0),.bits (byte 0),.bits (byte 0),.bits (byte 0)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at hm
  subst byteValue
  rfl

theorem zero_initial_rf_still_rejected (co : Location → Option Unified.Node → Option Unified.Node → Prop) :
    ¬Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate 0 0) proxyInitial initialRF co (fun _ => []) cluster := by
  intro hm
  have he := admitted_rf_is_actual_writer hm.toCausalConstraints (reader_byte_at 0 0 (0 : Fin 4))
  change none = some writerMemory at he
  cases he

theorem read_cannot_be_its_own_source (value : Nat) (co : Location → Option Unified.Node → Option Unified.Node → Prop) :
    ¬Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate value value) proxyInitial selfRF co (fun _ => []) cluster := by
  intro hm
  have he := admitted_rf_is_actual_writer hm.toCausalConstraints (reader_byte_at value value (0 : Fin 4))
  have hn : (some readerMemory : Option Unified.Node) ≠ some writerMemory := by decide
  exact hn he

theorem nonexistent_writer_source_rejected (value : Nat) (co : Location → Option Unified.Node → Option Unified.Node → Prop) :
    ¬Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate value value) proxyInitial absentRF co (fun _ => []) cluster := by
  intro hm
  have he := admitted_rf_is_actual_writer hm.toCausalConstraints (reader_byte_at value value (0 : Fin 4))
  have hn : (some absentMemory : Option Unified.Node) ≠ some writerMemory := by decide
  exact hn he

theorem missing_initialization_coherence_rejected (value : Nat) :
    ¬Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate value value) proxyInitial readWitness (fun _ _ _ => False) (fun _ => []) cluster := by
  intro hm
  exact hm.initialization (every_read_is_eligible value value cluster readWitness readerMemory base).1 _ _ _ (writer_byte_at value value (0 : Fin 4))

theorem reflexive_coherence_rejected (value : Nat) :
    ¬Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate value value) proxyInitial readWitness (fun _ _ _ => True) (fun _ => []) cluster := by
  intro hm
  exact (hm.coherence (every_read_is_eligible value value cluster readWitness readerMemory base).1).irrefl base none trivial

theorem wrong_reply_has_no_admitted_rf_or_co {value reply initialProxy rf co}
    (hn : wrap 32 reply ≠ wrap 32 value) :
    ¬Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate value reply) initialProxy rf co (fun _ => []) cluster :=
  fun hm => hn (admitted_memory_forces_full_word hm.toCausalConstraints)

theorem wrong_upper_word_bytes_have_no_memory_witness (rf : Unified.ReadsFrom) (co : Location → Option Unified.Node → Option Unified.Node → Prop) :
    ¬Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate 305419896 22136) proxyInitial rf co (fun _ => []) cluster :=
  wrong_reply_has_no_admitted_rf_or_co (by decide)

theorem reader_cannot_causally_precede_writer (value reply : Nat) (rf : Unified.ReadsFrom) (loc : Location) :
    ¬Unified.CausalityAt Tma.localShared Access.globalDescriptor (candidate value reply) (fun _ => []) cluster rf loc readerMemory writerMemory :=
  no_causality_to_writer

end
end Ptx.ByteValuePipelineMemoryTests
