import Ptx.Kernels.AmpereTiledOutputAccesses
import Ptx.Tests.AmpereTiledPhase

/-! Four-CTA, three-phase graph tests, source-only rejection, and global output
coverage/ownership boundaries. The old inconsistent oracle is rejected by the
memory model; it is never reported as a legal source/rf/co/observer witness. -/
namespace Ptx.AmpereTiledMemoryTests
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledGraph Ptx.AmpereTiledEvents Ptx.AmpereTiledPhaseTests
noncomputable section

theorem all_nodes_race_free (rf : Ampere.ReadsFrom) (a b : Node) :
    ¬ MemoryGraph.DataRace execution.memoryGraph rf a b := AmpereTiledRace.race_free source rf a b
theorem peer_read_eligible (rf : Ampere.ReadsFrom) :
    MemoryGraph.Eligible execution.memoryGraph rf (.thread ⟨reader,24⟩) ⟨.shared reader.cta,236⟩ :=
  AmpereTiledRace.eligible source rf _ _
theorem current_source_no_eligibility_premise {rf co} (hm : MemoryConstraints execution launch.initial rf co) :
    rf (.thread ⟨reader,24⟩) ⟨.shared reader.cta,236⟩ = some (.copyWrite ⟨writer,3⟩) := by
  obtain ⟨written,observed,hw,hr⟩ := current_byte_accesses
  exact AmpereTiledMemory.current_copy_source source hm writer_valid reader_valid rfl (by decide : 1 < input.k/16) 0 0 rfl hw hr
theorem future_source_forbidden {rf co} (hm : MemoryConstraints execution launch.initial rf co) :
    rf (.thread ⟨reader,24⟩) ⟨.shared reader.cta,236⟩ ≠ some (.copyWrite ⟨writer,6⟩) := by
  rw [current_source_no_eligibility_premise hm]
  decide

theorem reader_last_coordinates : AmpereTiledOutputLayout.row reader 3 = 31 ∧ AmpereTiledOutputLayout.col reader 3 = 15 := by decide
theorem last_output_base : AmpereTiledInventory.writeBase input (context launch reader) 3 = ⟨.global,18428⟩ := rfl
theorem last_output_byte : InOutput input ⟨.global,18431⟩ := by constructor; rfl; constructor <;> decide
theorem first_padding_not_output : ¬ InOutput input ⟨.global,18432⟩ := by simp [InOutput,input,AmpereTiledSourceTests.cfg]
theorem first_padding_in_domain : (⟨.global,18432⟩ : Location) ∈ domain input :=
  List.mem_map.mpr ⟨18432,List.mem_range.mpr (by decide),rfl⟩
theorem all_output_elements_covered {r c} (hr : r < input.m) (hc : c < input.n) :
    ∃ id : ThreadId, id.Valid (geometry input) ∧ ∃ slot : Fin 4,
      AmpereTiledOutputLayout.row id slot = r ∧ AmpereTiledOutputLayout.col id slot = c :=
  AmpereTiledOutputLayout.covers_output source.layout hr hc
theorem actual_global_writers_unique {a b loc va vb} (hs : loc.space = .global)
    (ha : execution.writeByte a loc = some va) (hb : execution.writeByte b loc = some vb) : a = b :=
  AmpereTiledGlobalAccesses.global_writer_unique source hs ha hb
theorem input_last_copy_region :
    input.a ≤ AmpereTiledBounds.copyStart input (context launch reader) 2 1 ∧
    AmpereTiledBounds.copyStart input (context launch reader) 2 1+8 = input.a+2*(input.m*input.k) := by decide
theorem zero_k_alias_output_base : AmpereTiledInventory.writeBase AmpereTiledSourceTests.zeroK
    (AmpereTiledSourceTests.ctx AmpereTiledSourceTests.zeroK AmpereTiledSourceTests.zeroId) 3 =
    cLocation AmpereTiledSourceTests.zeroK 15 7 :=
  AmpereTiledOutputLayout.write_base AmpereTiledSourceTests.zero_k_layout AmpereTiledSourceTests.zero_valid
    AmpereTiledSourceTests.zero_active 3

def firstCopy : Copy := operationAt input (context launch writer) (oracle writer) (replies writer) 0 0
theorem first_copy_recorded : execution.copyAt ⟨writer,0⟩ = some firstCopy := by
  let t := AmpereTiledSourceCandidate.trace input launch oracle replies writer
  have ht : t ∈ execution.traces := List.mem_map.mpr ⟨writer,Geometry.mem_threads.mpr writer_valid,rfl⟩
  have he := member_event source ht (serial := 0)
  change execution.eventAt ⟨writer,0⟩ = (AmpereTiledTrace.events input (context launch writer) (oracle writer) (replies writer))[0]? at he
  rw [show (0 : Nat) = 17*0+0 from rfl,phase_event _ _ _ _ 0 0 (by decide) (by decide),phase_events] at he
  exact event_issue_has_copy source.formed he

theorem inconsistent_oracle_rejected (rf : Ampere.ReadsFrom) (co : Ampere.Coherence) :
    ¬ MemoryConstraints execution launch.initial rf co := by
  intro hm
  have hv := AmpereTiledMemory.copy_payload_initial source hm first_copy_recorded (offset := 0) (by decide)
  change Symbolic.Byte.bits (byte 0) = Symbolic.Byte.bits (byte 165) at hv
  have he := congrArg Fin.val (Symbolic.Byte.bits.inj hv)
  norm_num [byte] at he

theorem padding_preserved {rf co o} (ho : ObserverConstraints execution launch.initial rf co o)
    (hd : o.domain = domain input) : o.output ⟨.global,18432⟩ = launch.initial ⟨.global,18432⟩ :=
  AmpereTiledObservation.frame source ho hd first_padding_in_domain first_padding_not_output

theorem every_output_has_actual_encoding {rf co o} (hm : MemoryConstraints execution launch.initial rf co)
    (ho : ObserverConstraints execution launch.initial rf co o) (hd : o.domain = domain input)
    {r c : Nat} (hr : r < input.m) (hc : c < input.n) :
    ∃ id : ThreadId, id.Valid launch.geometry ∧ ∃ slot : Fin 4, ∃ t ∈ execution.traces, t.id = id ∧
      AmpereTiledOutputLayout.row id slot = r ∧ AmpereTiledOutputLayout.col id slot = c ∧
      Scalar.RepresentsReal .f32 o.output (cLocation input r c) (AmpereTiledTrace.cValues t.oracle (input.k/16) slot) :=
  AmpereTiledOutputAccesses.every_output_word source hm ho hd hr hc

end
end Ptx.AmpereTiledMemoryTests
