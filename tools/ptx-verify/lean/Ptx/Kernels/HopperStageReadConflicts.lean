import Ptx.Kernels.HopperStageReadWitness

namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem base_read_region {a b node loc value}
    (hr : Access.readByte Tma.localShared Access.globalDescriptor (candidate a b).view node loc = some value) :
    loc.space = .global ∧ (loc.address < 4352 ∨ 65536 ≤ loc.address) := by
  cases node with
  | copyRead issue | copyWrite issue => simp [Access.readByte,Access.kind,no_nonbulk] at hr
  | tma node =>
    cases node with
    | source event => rw [ordinary_read_none] at hr; cases hr
    | notify id => cases hr
    | write id offset =>
      cases hl : Tma.writeLocation Tma.localShared (candidate a b).view id offset <;>
        cases hv : Tma.transferByte (candidate a b).view id offset <;>
        simp [Access.readByte,Access.kind,hl,hv,Ptx.Event.Kind.readByte] at hr
    | descriptor id =>
      cases hc : Tma.copyAt (candidate a b).view id with
      | none => simp [Access.readByte,Access.kind,hc] at hr
      | some op =>
        have hp : Ptx.Event.payloadByte (Access.globalDescriptor id.issue.thread op.descriptorAddress) (TensorMap.encode op.descriptor) loc = some value := by
          simpa only [Access.readByte,Access.kind,hc,Option.map_some,Option.bind_some,Ptx.Event.Kind.readByte] using hr
        have hb := Ptx.Event.payloadByte_bounds hp
        rw [TensorMap.encode_length] at hb
        refine ⟨hb.1.symm,.inl ?_⟩
        rcases all_source_copies hc with rfl | rfl <;> dsimp [Access.globalDescriptor,copyA,copyB] at hb <;> omega
    | read id offset =>
      have hl := Access.tensor_read_access (.inl (by rw [hr]; rfl))
      cases hc : Tma.copyAt (candidate a b).view id with
      | none => simp [Tma.readLocation,hc] at hl
      | some op =>
        have hs : Tma.sourceByte op.descriptor op.coordinates offset = some loc := by simpa only [Tma.readLocation,hc,Option.bind_some] using hl
        obtain ⟨_,_,hg,ha⟩ := Tma.source_byte_some hs
        refine ⟨hg,.inr ?_⟩
        rcases all_source_copies hc with rfl | rfl <;> dsimp [copyA,copyB,aView,bView] at ha <;> omega

theorem base_read_immutable {a b node loc value}
    (hr : Access.readByte Tma.localShared Access.globalDescriptor (candidate a b).view node loc = some value) :
    ∀ writer, Unified.writeByte Tma.localShared Access.globalDescriptor (candidate a b) writer loc = none := by
  obtain ⟨hg,ho⟩ := base_read_region hr
  intro writer
  cases hw : Unified.writeByte Tma.localShared Access.globalDescriptor (candidate a b) writer loc with
  | none => rfl
  | some observed =>
    obtain ⟨base,size,hf,hs | hout⟩ := write_footprint_regions hw
    all_goals have hb := Unified.access_footprint_bounds (.inr (by rw [hw]; rfl)) hf
    · obtain ⟨hshared,_⟩ := hs
      have he := hshared.symm.trans (hb.1.trans hg)
      cases he
    · obtain ⟨_,rfl,hlo,hhi,_⟩ := hout
      rcases ho with ho | ho <;> omega

theorem read_write_pair {a b read writer loc vr vw}
    (hr : Unified.readByte Tma.localShared Access.globalDescriptor (candidate a b) read loc = some vr)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (candidate a b) writer loc = some vw) :
    ∃ issue operand, read = .wgmmaRead issue operand ∧ loc = nativeLocation a b operand ∧ writer = nativeProducer operand := by
  cases read with
  | base node => rw [base_read_immutable hr writer] at hw; cases hw
  | wgmmaRead issue operand =>
    obtain ⟨mark,call,he,hl,_⟩ := Unified.native_read_location hr
    obtain ⟨hcta,rfl⟩ := actual_representative_call he
    have hloc : loc = nativeLocation a b operand := by rw [hl,hcta]; rfl
    refine ⟨issue,operand,rfl,hloc,?_⟩
    rw [hloc] at hw
    exact native_producer_unique hw

theorem tensor_native_not_strong (resolve descriptor candidate id offset issue operand) :
    ¬Unified.MorallyStrong resolve descriptor candidate (.base (.tma (.write id offset))) (.wgmmaRead issue operand) := by
  intro h
  rcases h.2.1 with hagent | ⟨sa,sb,ha,_⟩
  · have hh := congrArg (fun agent => match agent with | MemoryGraph.Agent.operation _ family _ => family | _ => 0) hagent
    change 2 = 4 at hh
    omega
  · cases hl : Tma.writeLocation resolve candidate.view id offset <;>
      cases hv : Tma.transferByte candidate.view id offset <;>
      simp [Unified.kind,Access.kind,hl,hv,Ptx.Event.Kind.strongScope] at ha

theorem read_witness_no_observed (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (rf : Unified.ReadsFrom) :
    ∀ writer read, ¬Unified.Observed Tma.localShared Access.globalDescriptor (candidate a b) rf writer read := by
  rintro writer read ⟨hs,loc,value,hr,_,hw⟩
  obtain ⟨vw,hvw⟩ := Option.isSome_iff_exists.mp hw
  obtain ⟨issue,operand,rfl,_,rfl⟩ := read_write_pair hr hvw
  cases operand <;> exact tensor_native_not_strong _ _ _ _ _ _ _ hs
theorem read_witness_no_observation (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (rf : Unified.ReadsFrom) :
    ∀ left right, ¬Unified.ObservationOrder Tma.localShared Access.globalDescriptor (candidate a b) rf left right := by
  intro left right ho
  induction ho with
  | direct h => exact read_witness_no_observed a b rf _ _ h
  | viaRMW _ _ _ ih _ => exact ih
theorem memory_causality_rank {a b rf loc left right}
    (hc : Unified.CausalityAt Tma.localShared Access.globalDescriptor (candidate a b) histories cluster rf loc left right) :
    memoryRank left < memoryRank right := by
  rcases hc with ⟨_,_,ho⟩ | ⟨middle,ho,_⟩
  · exact memory_byte_order_rank ho
  · exact (read_witness_no_observation a b rf _ _ ho).elim

end
end Ptx.Kernels.HopperStage
