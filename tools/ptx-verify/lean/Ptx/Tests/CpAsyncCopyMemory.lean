import Ptx.Kernels.CpAsyncCopyCorrect

/-! Actual source-positive but memory-negative cases: wrong scalar replies and
wrong copy payloads are rejected for all rf/co, using derived race freedom. -/
namespace Ptx.CpAsyncCopyMemoryTests
open Ptx.ISA Ptx.Ampere Ptx.CpAsyncCopyTrace Ptx.CpAsyncCopyGraph
noncomputable section

def answers : Answers := ![7,4294967295,42,99]
def bytes : List Symbolic.Byte := payload answers
def initial (loc : Location) : Symbolic.Byte :=
  (Ptx.Event.payloadByte ⟨.global,64⟩ bytes loc).getD (.bits (byte 165))
def cfg : CpAsyncCopySpec.Config := ⟨64,128,160⟩
def badAnswers : Answers := fun _ => 99
def badBytes : List Symbolic.Byte := bytes.set 0 (.bits (byte 8))

theorem sample_size : bytes.length = 16 := payload_size answers
theorem sample_input : ∀ i : Fin 4, answers i < 2^32 ∧
    Scalar.RepresentsU32 initial ⟨.global,64+4*i.val⟩ (answers i) := by
  intro i
  fin_cases i <;> constructor
  all_goals try norm_num [answers]
  all_goals intro offset ho; interval_cases offset <;> rfl

theorem sample_pre : Pre cfg (launch 64 128 initial) :=
  ⟨by norm_num [CpAsyncCopySpec.Layout,cfg],⟨answers,sample_input⟩,rfl⟩

theorem sample_source : WellFormed code (launch 64 128 initial) (graph 64 128 bytes answers) :=
  wellFormed _ _ _ _ _ (by decide) (by decide) sample_size
theorem sample_complete : Complete (graph 64 128 bytes answers) := complete _ _ _ _
theorem bad_load_source : WellFormed code (launch 64 128 initial) (graph 64 128 bytes badAnswers) :=
  wellFormed _ _ _ _ _ (by decide) (by decide) sample_size
theorem bad_load_complete : Complete (graph 64 128 bytes badAnswers) := complete _ _ _ _

theorem bad_load_rejected (rf : ReadsFrom) (co : Coherence) :
    ¬ MemoryConstraints (graph 64 128 bytes badAnswers) initial rf co := by
  intro hm
  have hv := load_byte_from_input hm sample_size (.inl (by decide)) (0 : Fin 4) 0 (by decide)
  norm_num [badAnswers,word,Scalar.u32Byte,Ptx.Event.Cells.wordByte,initial,
    Ptx.Event.payloadByte,bytes,payload,answers,Scalar.u32Bytes,encodeU32,wrap,byte] at hv

theorem bad_payload_size : badBytes.length = 16 := by simp [badBytes,sample_size]
theorem bad_payload_source : WellFormed code (launch 64 128 initial) (graph 64 128 badBytes answers) :=
  wellFormed _ _ _ _ _ (by decide) (by decide) bad_payload_size
theorem bad_payload_complete : Complete (graph 64 128 badBytes answers) := complete _ _ _ _
theorem bad_payload_rejected (rf : ReadsFrom) (co : Coherence) :
    ¬ MemoryConstraints (graph 64 128 badBytes answers) initial rf co := by
  intro hm
  have hfree := race_free (src := 64) (dst := 128) (answers := answers) bad_payload_size (.inl (by decide)) rf
  have hv := copy_input_bytes hm bad_payload_size (.inl (by decide))
    (fun _ _ => MemoryGraph.race_free_eligible hfree _ _) 0 (by decide)
  norm_num [badBytes,initial,Ptx.Event.payloadByte,bytes,payload,answers,
    Scalar.u32Bytes,word,encodeU32,wrap,byte] at hv

theorem all_allowed_output {rf co o}
    (hm : CheckedConditions code (launch 64 128 initial) (graph 64 128 bytes answers) rf co)
    (ho : ObserverConstraints (graph 64 128 bytes answers) initial rf co o)
    (hd : o.domain = CpAsyncCopySpec.domain cfg) :
    CpAsyncCopySpec.Post cfg initial o.output := correct cfg _ _ _ _ _ sample_pre hm ho hd

end
end Ptx.CpAsyncCopyMemoryTests
