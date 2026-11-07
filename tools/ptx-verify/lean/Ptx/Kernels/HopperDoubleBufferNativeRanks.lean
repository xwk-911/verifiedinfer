import Ptx.Kernels.HopperDoubleBufferNativeInventory

/-! Actual native issue/return ticks and source-matched MMA/wait metadata.
The rank is a control proof device; it adds no memory-publication rule. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def nativeTick (tiles : Nat) (id : Ptx.Event.EventId) : Nat := sourceTick tiles (resourceLane id.thread) id.serial

theorem data_native_id_tick (a b tiles tile lane) (ht : tile < tiles) (index : Fin 4) :
    nativeTick tiles (dataNativeId a b tiles tile lane index) = 12+10*tile+index.val := by
  have hi := index.isLt
  change sourceTick tiles (resourceLane (ctx tiles lane).id)
    (dataTileStart a b tiles tile lane+(dataPreludeLength tiles tile lane+1+index.val)) = _
  rw [resource_lane_value,data_tile_start_value a b tiles tile lane ht]
  by_cases hz : lane.val = 0
  · have hl : HopperStage.leader lane = true := by simp [HopperStage.leader,hz]
    simp only [sourceTick,hz,ite_true,hl,dataPreludeLength,needsPrefetch,and_true]
    by_cases hn : tile+1 < tiles
    · rw [ite_eq_left hn,producer_tick_before tiles _ (by simp only [producerThreshold]; split_ifs <;> omega)]
      omega
    · rw [ite_eq_right hn,producer_tick_after tiles _ (by simp only [producerThreshold]; split_ifs <;> omega)]
      omega
  · have hl : HopperStage.leader lane = false := by simp [HopperStage.leader,hz]
    simp only [sourceTick,hz,ite_false,hl,dataPreludeLength,needsPrefetch,Bool.false_eq_true,and_false,ite_false]
    have hp := peer_native_tick tiles tile (1+index.val) ht (by omega)
    convert hp using 1; omega

theorem data_native_id_control_rank (a b tiles tile lane) (ht : tile < tiles) (index : Fin 4) :
    sourceControlRank tiles (dataNativeId a b tiles tile lane index) = 1024*(12+10*tile+index.val)+lane.val := by
  change 1024*nativeTick tiles (dataNativeId a b tiles tile lane index)+resourceLane (ctx tiles lane).id = _
  rw [data_native_id_tick a b tiles tile lane ht index,resource_lane_value]

theorem data_native_tick_positive {a b tiles id signature}
    (he : (dataCompleteCandidate a b tiles).nativeSignatureAt id = some signature) : 0 < nativeTick tiles id := by
  obtain ⟨tile,lane,index,ht,rfl,_⟩ := data_native_signature_shape he
  rw [data_native_id_tick a b tiles tile lane ht index]
  omega

theorem data_native_sync_equal_ticks {a b tiles left right}
    (hs : Unified.NativeSync HopperStage.block (dataCompleteCandidate a b tiles) left right) : nativeTick tiles left = nativeTick tiles right := by
  obtain ⟨_,signature,hl,hr⟩ := hs
  obtain ⟨lt,ll,li,hlt,rfl,hls⟩ := data_native_signature_shape hl
  obtain ⟨rt,rl,ri,hrt,rfl,hrs⟩ := data_native_signature_shape hr
  obtain ⟨rfl,rfl⟩ := data_native_signature_identity lt rt li ri (hls.symm.trans hrs)
  rw [data_native_id_tick a b tiles lt ll hlt li,data_native_id_tick a b tiles lt rl hrt li]

theorem data_native_mma_case {a b tiles id mark call}
    (he : (dataCompleteCandidate a b tiles).eventAt id = some (.mma mark call)) :
    ∃ tile lane, tile < tiles ∧ id = dataNativeId a b tiles tile lane 1 ∧ call.group = tile := by
  have hs : (dataCompleteCandidate a b tiles).nativeSignatureAt id =
      some (Wgmma.alignedSignature ⟨mark.pc,mark,.mma call.ordinal call.group call.d.names call.a call.b call.scaleD⟩) := by
    rw [Unified.Candidate.nativeSignatureAt,he]
    rfl
  obtain ⟨tile,lane,index,ht,hid,hshape⟩ := data_native_signature_shape hs
  have hk := congrArg Wgmma.SourceSignature.kind hshape
  fin_cases index <;> simp [dataNativeSignature,dataTileSchedule,Wgmma.alignedSignature] at hk
  exact ⟨tile,lane,ht,hid,hk.2.1⟩

theorem data_native_wait_case {a b tiles id mark groups keep before after query}
    (hb : tiles ≤ 2^28)
    (he : (dataCompleteCandidate a b tiles).eventAt id = some (.wait mark groups keep before after query)) :
    ∃ tile lane, tile < tiles ∧ id = dataNativeId a b tiles tile lane 3 ∧ after = tile+1 := by
  have hs : (dataCompleteCandidate a b tiles).nativeSignatureAt id =
      some (Wgmma.alignedSignature ⟨mark.pc,mark,.wait groups keep⟩) := by
    rw [Unified.Candidate.nativeSignatureAt,he]
    rfl
  obtain ⟨tile,lane,index,ht,hid,hshape⟩ := data_native_signature_shape hs
  have hk := congrArg Wgmma.SourceSignature.kind hshape
  fin_cases index <;> simp [dataNativeSignature,dataTileSchedule,Wgmma.alignedSignature] at hk
  refine ⟨tile,lane,ht,hid,?_⟩
  have hw := data_source_native_wait a b tiles tile lane ht hb
  have hi : dataNativeId a b tiles tile lane 3 = dataNativeWaitId a b tiles tile lane := by
    simp only [dataNativeId,dataNativeWaitId]
    congr 1
  have hx : id = dataNativeWaitId a b tiles tile lane := hid.trans hi
  rw [← hx] at hw
  have hh := Wgmma.Event.wait.inj (Option.some.inj (he.symm.trans hw))
  exact hh.2.2.2.2.1

end
end Ptx.Kernels.HopperDoubleBuffer
