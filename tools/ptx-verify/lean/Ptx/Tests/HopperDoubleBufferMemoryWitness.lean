import Ptx.Kernels.HopperDoubleBufferMemoryWitness
import Ptx.Kernels.HopperStageNativeControl
import Ptx.Tests.HopperDoubleBufferData

/-! Independent repeated RF/co memory conditions, compatible source/control
components and actual byte/rank boundaries. Observer and full-Pre refinement
are not asserted here. Finite rejection checks use only metadata. -/
namespace Ptx.HopperDoubleBufferMemoryWitnessTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev a := HopperDoubleBufferDataTests.a
abbrev b := HopperDoubleBufferDataTests.b
def firstA (tile : Nat) : Unified.Node := dataNativeProducer a b 3 tile (.a (0,0) 0)
def readA (tile : Nat) : Unified.Node := dataNativeRead a b 3 tile (.a (0,0) 0)
def sharedA : Location := ⟨.shared .zero,16⟩
def coCheck (loc : Location) (left right : Option Unified.Node) : Bool :=
  @decide (dataCoherenceWitness a b 3 loc left right) (by
    unfold dataCoherenceWitness Unified.RankedCo
    cases left <;> cases right <;> simp only [Unified.sourcePresent,Unified.WritesAt] <;> infer_instance)
theorem co_check_iff (loc : Location) (left right : Option Unified.Node) :
    coCheck loc left right = true ↔ dataCoherenceWitness a b 3 loc left right := by
  unfold coCheck
  simp only [decide_eq_true_eq]

theorem actual_memory_ranks : dataMemoryRank 3 (firstA 0) = 13056 ∧ dataMemoryRank 3 (readA 0) = 26880 ∧
    dataMemoryRank 3 (firstA 2) = 41728 ∧ dataMemoryRank 3 (readA 2) = 67840 := by decide
theorem initialization_precedes_actual_writer : coCheck sharedA none (some (firstA 0)) = true := by decide
theorem reused_writer_order : coCheck sharedA (some (firstA 0)) (some (firstA 2)) = true := by decide
theorem reversed_writer_order_rejected : coCheck sharedA (some (firstA 2)) (some (firstA 0)) = false := by decide
theorem writer_self_order_rejected : coCheck sharedA (some (firstA 2)) (some (firstA 2)) = false := by decide
theorem initialization_self_order_rejected : coCheck sharedA none none = false := by decide
theorem writer_before_initialization_rejected : coCheck sharedA (some (firstA 2)) none = false := by decide
theorem other_slot_writer_absent : coCheck sharedA none (some (firstA 1)) = false := by decide
theorem read_is_not_co_writer : coCheck sharedA (some (readA 0)) (some (firstA 2)) = false := by decide
theorem wrong_byte_has_no_writer : coCheck ⟨.shared .zero,0⟩ none (some (firstA 0)) = false := by decide

theorem generic_control_refinement (x : TileA) (y : TileB) (tiles : Nat) (loc : Location) (left right : Unified.Node)
    (ho : Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate x y tiles) (dataHistories x y tiles) dataCluster loc left right) :
    Ptx.Event.Path (Unified.ControlEdge HopperStage.block (dataCompleteCandidate x y tiles) (dataHistories x y tiles))
      (Unified.memoryControlNode left) (Unified.memoryControlNode right) :=
  Unified.byte_order_control_path (data_no_nonbulk x y tiles) ho

theorem same_rule_checks_one_stage (x : Wgmma.ACoord → ℝ) (y : Wgmma.BCoord → ℝ) :
    ∀ loc node, ¬Unified.ByteOrder Tma.localShared Access.globalDescriptor (HopperStage.candidate x y)
      HopperStage.histories HopperStage.cluster loc node node :=
  Unified.byte_order_acyclic_of_control (HopperStage.no_nonbulk x y) (HopperStage.stage_native_control_acyclic x y)

theorem actual_reuse_control_path :
    Ptx.Event.Path (Unified.ControlEdge HopperStage.block (dataCompleteCandidate a b 3) (dataHistories a b 3))
      (Unified.memoryControlNode (readA 0)) (Unified.memoryControlNode (firstA 2)) :=
  Unified.byte_order_control_path (data_no_nonbulk a b 3)
    (data_native_reuse_byte_order a b 3 0 2 (by decide) (by decide) (by decide) (by decide) (.a (0,0) 0))

theorem reverse_byte_order_rejected :
    ¬Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 3) (dataHistories a b 3) dataCluster
      sharedA (firstA 2) (readA 0) := by
  intro ho
  have hh := data_memory_byte_order_rank (by decide) ho
  have hr := actual_memory_ranks
  omega

theorem arbitrary_real_causal_exists (x : TileA) (y : TileB) (tiles : Nat) (hb : tiles ≤ 2^28) (frame : Location → Symbolic.Byte) :
    ∃ rf co, Unified.CausalConstraints Tma.localShared Access.globalDescriptor (dataCompleteCandidate x y tiles)
      (dataInitialProxyMemory x y tiles frame) rf co (dataHistories x y tiles) dataCluster := by
  obtain ⟨rf,co,hc,_,_⟩ := data_causal_exists x y tiles frame hb
  exact ⟨rf,co,hc⟩

theorem arbitrary_real_memory_exists (x : TileA) (y : TileB) (tiles : Nat) (hb : tiles ≤ 2^28) (frame : Location → Symbolic.Byte) :
    ∃ rf co, Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate x y tiles)
      (dataInitialProxyMemory x y tiles frame) rf co (dataHistories x y tiles) dataCluster :=
  data_memory_exists x y tiles frame hb

theorem zero_round_memory (frame : Location → Symbolic.Byte) :
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 0) (dataInitialProxyMemory a b 0 frame)
      (dataReadWitness a b 0) (dataCoherenceWitness a b 0) (dataHistories a b 0) dataCluster :=
  data_memory_witness a b 0 frame (by decide)
theorem repeated_memory (frame : Location → Symbolic.Byte) :
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 5) (dataInitialProxyMemory a b 5 frame)
      (dataReadWitness a b 5) (dataCoherenceWitness a b 5) (dataHistories a b 5) dataCluster :=
  data_memory_witness a b 5 frame (by decide)

theorem compatible_source_control_memory (x : TileA) (y : TileB) (tiles : Nat) (hb : tiles ≤ 2^28) (frame : Location → Symbolic.Byte) :
    Unified.TmaComponents code (completeLaunch tiles (dataRepresentedInitial x y tiles frame))
      (dataCompleteCandidate x y tiles) Tma.localShared (dataMaps tiles) (dataHistories x y tiles) ∧
    Unified.ControlAdmitted HopperStage.block (dataCompleteCandidate x y tiles) (dataHistories x y tiles) ∧
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate x y tiles) (dataInitialProxyMemory x y tiles frame)
      (dataReadWitness x y tiles) (dataCoherenceWitness x y tiles) (dataHistories x y tiles) dataCluster :=
  ⟨data_tma_components x y tiles frame hb,data_native_control_admitted x y tiles hb,data_memory_witness x y tiles frame hb⟩

end
end Ptx.HopperDoubleBufferMemoryWitnessTests
