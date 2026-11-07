import Ptx.Kernels.HopperStageWriterUniqueness

/-! Independent full memory-component witness for the one-phase source. This
does not include global observation, native collective control, allocations or
runtime correspondence, and does not establish double-buffered GEMM. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem native_tensor_not_strong (resolve descriptor candidate id offset issue operand) :
    ¬Unified.MorallyStrong resolve descriptor candidate (.wgmmaRead issue operand) (.base (.tma (.write id offset))) := by
  intro h
  rcases h.2.1 with hagent | ⟨sa,sb,ha,_⟩
  · have hh := congrArg (fun agent => match agent with | MemoryGraph.Agent.operation _ family _ => family | _ => 0) hagent
    change 4 = 2 at hh
    omega
  · cases he : candidate.representativeAt issue <;>
      simp [Unified.kind,he,Wgmma.operandKind,Ptx.Event.Kind.strongScope] at ha
theorem read_write_not_strong {a b read writer loc vr vw}
    (hr : Unified.readByte Tma.localShared Access.globalDescriptor (candidate a b) read loc = some vr)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (candidate a b) writer loc = some vw) :
    ¬Unified.MorallyStrong Tma.localShared Access.globalDescriptor (candidate a b) read writer := by
  obtain ⟨issue,operand,rfl,_,rfl⟩ := read_write_pair hr hw
  cases operand <;> exact native_tensor_not_strong _ _ _ _ _ _ _
theorem stage_single_copy_atomicity (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (rf : Unified.ReadsFrom) :
    Unified.SingleCopyAtomicity Tma.localShared Access.globalDescriptor (candidate a b) rf (coherenceWitness a b) := by
  intro read writer hs loc vr vw hr hw
  exact (read_write_not_strong hr hw hs).elim
theorem stage_rmw_atomicity (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (rf : Unified.ReadsFrom) :
    Unified.RMWAtomicity Tma.localShared Access.globalDescriptor (candidate a b) rf (coherenceWitness a b) := by
  intro read writer _ hs loc vr vw hr hw
  exact (read_write_not_strong hr hw hs).elim
theorem memory_program_order_rank {a b left right}
    (hp : Unified.ProgramOrder (candidate a b) left right) : memoryRank left < memoryRank right := by
  cases left <;> cases right <;> try exact False.elim hp
  rename_i left right
  cases left <;> cases right <;> try exact False.elim hp
  exact actual_control_edge_rank (.inl hp)
theorem strong_communication_absent {a b rf left right}
    (hl : Unified.MorallyStrong Tma.localShared Access.globalDescriptor (candidate a b) left right)
    (hr : Unified.MorallyStrong Tma.localShared Access.globalDescriptor (candidate a b) right left) :
    ¬Unified.Communication Tma.localShared Access.globalDescriptor (candidate a b) rf (coherenceWitness a b) left right := by
  rintro (⟨loc,value,hread,_,hwrite⟩ | ⟨loc,hco⟩ | ⟨_,loc,value,hread,hco⟩)
  · obtain ⟨vw,hw⟩ := Option.isSome_iff_exists.mp hwrite
    exact read_write_not_strong hread hw hr
  · cases hco.1
  · obtain ⟨writer,he,hw⟩ := hco.2
    have hid := Option.some.inj he
    subst writer
    obtain ⟨vw,hw⟩ := Option.isSome_iff_exists.mp hw
    exact read_write_not_strong hread hw hl
theorem stage_sc_per_location (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (rf : Unified.ReadsFrom) :
    Unified.SCPerLocation Tma.localShared Access.globalDescriptor (candidate a b) rf (coherenceWitness a b) := by
  intro members _ hs node _ ho
  have hh := ho.rank_lt memoryRank (fun x y he => by
    rcases he with ⟨hx,hy,hp | hc⟩
    · exact memory_program_order_rank hp
    · exact (strong_communication_absent (hs x y hx hy).1 (hs y x hy hx).1 hc).elim)
  omega

theorem stage_memory_witness (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame : Location → Symbolic.Byte) :
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate a b)
      (initialProxyMemory a b frame) readWitness (coherenceWitness a b) histories cluster := {
  toCausalConstraints := stage_causal_witness a b frame
  baseAcyclic := memory_base_acyclic a b
  coherence := fun _ => stage_coherence a b readWitness
  atomicity := fun _ => stage_single_copy_atomicity a b readWitness
  rmwAtomicity := fun _ => stage_rmw_atomicity a b readWitness
  scPerLocation := fun _ => stage_sc_per_location a b readWitness
}
theorem stage_memory_exists (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame : Location → Symbolic.Byte) :
    ∃ rf co, Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate a b)
      (initialProxyMemory a b frame) rf co histories cluster ∧
      ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (candidate a b) histories cluster rf :=
  ⟨readWitness,coherenceWitness a b,stage_memory_witness a b frame,stage_no_mixed_size_race a b readWitness⟩

end
end Ptx.Kernels.HopperStage
