import Ptx.Kernels.AmpereTiledPhaseVisibility
import Ptx.Kernels.AmpereTiledSourceCandidate
import Ptx.Kernels.AmpereTiledAccesses
import Ptx.Tests.AmpereTiledSource

/-! Full enumerated launch source instances and cross-thread phase order.
These deliberately inconsistent value oracles are not memory-admitted witnesses.
The conditional visibility theorem's eligibility premise remains explicit. -/
namespace Ptx.AmpereTiledPhaseTests
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledTrace Ptx.AmpereTiledGraph
noncomputable section
abbrev input := AmpereTiledSourceTests.cfg
def launch : Scalar.Launch := ⟨geometry input,params input,fun _ => .bits (byte 165)⟩
def oracle (_ : ThreadId) : Oracle := AmpereTiledSourceTests.oracle
def replies (id : ThreadId) : ReplySet input (context launch id) (oracle id) := {
  payload := fun phase i => (oracle id).bytes (10*phase+i.val)
  a := fun _ _ => ⟨1,1⟩
  b := fun _ _ => ⟨1,1⟩
  size := by intro phase _ i; simp [oracle,AmpereTiledSourceTests.oracle]
  bytes := by intro phase _ i; simp [AmpereTiledEntry.loopConfig]
  wordA := by intro phase _ i; rfl
  wordB := by intro phase _ i; rfl
}
def execution := AmpereTiledSourceCandidate.candidate input launch oracle replies
theorem source : SourceInfo input launch execution :=
  AmpereTiledSourceCandidate.source_info AmpereTiledSourceTests.layout launch oracle replies
    (AmpereTiledInit.canonical_params input) rfl (by constructor <;> decide)
theorem launch_slots : launch.geometry.grid.volume*launch.geometry.block.volume = 128 := rfl

def reader : ThreadId := ⟨⟨1,1,0⟩,⟨3,7,0⟩⟩
def writer : ThreadId := ⟨⟨1,1,0⟩,⟨1,7,0⟩⟩
theorem reader_valid : reader.Valid launch.geometry := by simp [reader,launch,geometry,input,AmpereTiledSourceTests.cfg,ThreadId.Valid,Dim3.Within]
theorem writer_valid : writer.Valid launch.geometry := by simp [writer,launch,geometry,input,AmpereTiledSourceTests.cfg,ThreadId.Valid,Dim3.Within]
theorem distinct_lanes : reader ≠ writer := by decide
theorem actual_writer_trace : ∃ t ∈ execution.traces, t.id = writer := source.formed.2.2.2 writer writer_valid
theorem actual_reader_trace : ∃ t ∈ execution.traces, t.id = reader := source.formed.2.2.2 reader reader_valid

theorem waited_copy_before_peer_read : BaseOrder execution (.copyWrite ⟨writer,3⟩) (.thread ⟨reader,24⟩) :=
  AmpereTiledPhaseOrder.copy_before_read source writer_valid reader_valid rfl (by decide : 1 < input.k/16) 0 0
theorem peer_read_before_reuse : BaseOrder execution (.thread ⟨reader,24⟩) (.copyWrite ⟨writer,6⟩) :=
  AmpereTiledPhaseOrder.read_before_later_copy source reader_valid writer_valid rfl (by decide : 1 < 2) (by decide : 2 < input.k/16) 0 0
theorem old_write_before_current : BaseOrder execution (.copyWrite ⟨writer,0⟩) (.copyWrite ⟨writer,3⟩) :=
  AmpereTiledPhaseOrder.copy_before_later_copy source writer_valid writer_valid rfl (by decide : 0 < 1) (by decide : 1 < input.k/16) 0 0
theorem third_wait : execution.eventAt ⟨writer,38⟩ = some (.wait 3 0) := wait_event source writer_valid (by decide : 2 < input.k/16)
theorem third_reuse_return : execution.eventAt ⟨reader,50⟩ = some (.ordinary (.barrierReturn 0 5)) :=
  return_event source reader_valid (by decide : 2 < input.k/16) 1
theorem actual_no_rmw (node : Node) : ¬ execution.memoryGraph.IsRMW node := AmpereTiledGraph.no_rmw source node
theorem copy_agent_distinct_from_reader : Node.agent (.copyWrite ⟨writer,3⟩) ≠ Node.agent (.thread ⟨reader,24⟩) := by decide
theorem phases_have_distinct_agents : Node.agent (.copyWrite ⟨writer,3⟩) ≠ Node.agent (.copyWrite ⟨writer,6⟩) := by decide
theorem overlapping_phases_same_address : AmpereTiledSharedWriters.copyBase writer 0 = 232 := rfl
theorem reader_uses_second_word : AmpereTiledInventory.readBase (context launch reader) 0 = ⟨.shared reader.cta,236⟩ := rfl

theorem current_byte_accesses : ∃ written observed,
    execution.writeByte (.copyWrite ⟨writer,3⟩) ⟨.shared reader.cta,236⟩ = some written ∧
    execution.readByte (.thread ⟨reader,24⟩) ⟨.shared reader.cta,236⟩ = some observed := by
  obtain ⟨written,hw⟩ := AmpereTiledAccesses.copy_write_byte_exists source writer_valid (by decide : 1 < input.k/16) 0 4
  obtain ⟨observed,hr⟩ := AmpereTiledAccesses.read_byte_exists source reader_valid (by decide : 1 < input.k/16) 0 0
  exact ⟨written,observed,hw,hr⟩

theorem source_is_current {rf co written observed}
    (hm : MemoryConstraints execution launch.initial rf co)
    (he : MemoryGraph.Eligible execution.memoryGraph rf (.thread ⟨reader,24⟩) ⟨.shared reader.cta,236⟩)
    (hw : execution.writeByte (.copyWrite ⟨writer,3⟩) ⟨.shared reader.cta,236⟩ = some written)
    (hr : execution.readByte (.thread ⟨reader,24⟩) ⟨.shared reader.cta,236⟩ = some observed) :
    rf (.thread ⟨reader,24⟩) ⟨.shared reader.cta,236⟩ = some (.copyWrite ⟨writer,3⟩) :=
  AmpereTiledPhaseVisibility.current_copy_source source hm writer_valid reader_valid rfl (by decide : 1 < input.k/16) 0 0 rfl he hw hr

theorem future_source_rejected {rf co written observed}
    (hm : MemoryConstraints execution launch.initial rf co)
    (he : MemoryGraph.Eligible execution.memoryGraph rf (.thread ⟨reader,24⟩) ⟨.shared reader.cta,236⟩)
    (hw : execution.writeByte (.copyWrite ⟨writer,3⟩) ⟨.shared reader.cta,236⟩ = some written)
    (hr : execution.readByte (.thread ⟨reader,24⟩) ⟨.shared reader.cta,236⟩ = some observed) :
    rf (.thread ⟨reader,24⟩) ⟨.shared reader.cta,236⟩ ≠ some (.copyWrite ⟨writer,6⟩) := by
  rw [source_is_current hm he hw hr]
  decide

theorem current_source_from_actual_accesses {rf co}
    (hm : MemoryConstraints execution launch.initial rf co)
    (he : MemoryGraph.Eligible execution.memoryGraph rf (.thread ⟨reader,24⟩) ⟨.shared reader.cta,236⟩) :
    rf (.thread ⟨reader,24⟩) ⟨.shared reader.cta,236⟩ = some (.copyWrite ⟨writer,3⟩) := by
  obtain ⟨written,observed,hw,hr⟩ := current_byte_accesses
  exact source_is_current hm he hw hr

end
end Ptx.AmpereTiledPhaseTests
