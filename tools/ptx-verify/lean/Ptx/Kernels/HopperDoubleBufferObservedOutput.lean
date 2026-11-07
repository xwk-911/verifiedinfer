import Ptx.Kernels.HopperDoubleBufferObserverWitness

/-! Observed specification bytes and adjacent frame for the actual repeated
source family. RF/co/observers may vary compatibly with that fixed candidate;
this is not reconstruction of every full-Pre admitted source execution, IEEE
equivalence, allocation/runtime admission or a physical GPU observer theorem. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem data_actual_output_byte (a b tiles) (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (.base (.tma (.source (dataStoreId a b tiles lane slot))))
      ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      some (.realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val) := by
  have he : Access.kind Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles).view
      (.tma (.source (dataStoreId a b tiles lane slot))) =
      some (.write ⟨.global,outputWordAddress (lane,slot)⟩
        (Symbolic.encode .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))))) := by
    simp only [Access.kind,Unified.view_eventAt,data_complete_store_event,Option.map_some,
      outputWriteEvent,Unified.eventView,Option.bind_some,output_write_address,result_matches_specification]
    rfl
  rw [Unified.base_write_preserved,Access.writeByte,he,Option.bind_some,Ptx.Event.Kind.writeByte,Ptx.Event.payloadByte_offset]
  simp only [Symbolic.encode,Symbolic.Format.bytes,List.getElem?_map,List.getElem?_range index.isLt,Option.map_some]

theorem data_observed_matrix_byte {a b tiles initial rf co obs} (hb : tiles ≤ 2^28)
    (hc : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      initial rf co (dataHistories a b tiles) dataCluster)
    (ho : Unified.ObserverConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      initial rf co (dataHistories a b tiles) dataCluster obs)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    obs.output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      .realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val := by
  have hw := data_actual_output_byte a b tiles lane slot index
  exact Unified.observer_unique_writer hc ho (ho.coverage _ _ _ rfl hw)
    (data_global_observer_eligible a b tiles hb rf _ rfl) hw
    (fun _ _ hother => data_global_unique_writers hb rfl hother hw)

theorem data_observed_frame {a b tiles initial rf co obs loc} (hb : tiles ≤ 2^28)
    (ho : Unified.ObserverConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      initial rf co (dataHistories a b tiles) dataCluster obs)
    (hd : loc ∈ obs.domain) (hg : loc.space = .global) (hf : ¬(8192 ≤ loc.address ∧ loc.address < 10240)) :
    obs.output loc = initial .generic loc := by
  apply Unified.observer_unwritten ho hd (data_global_observer_eligible a b tiles hb rf loc hg)
  intro writer
  cases hw : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) writer loc with
  | none => rfl
  | some value =>
    obtain ⟨lane,slot,_,hl⟩ := data_global_writer_metadata hb hg hw
    have hr := data_output_word_bounds lane slot
    exact (hf ⟨by omega,by omega⟩).elim

theorem data_independent_observed_matrix (a b tiles frame) (hb : tiles ≤ 2^28)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    (dataObservation a b tiles frame).output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      .realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val :=
  data_observed_matrix_byte hb (data_causal_witness a b tiles frame hb) (data_observer_witness a b tiles frame hb) lane slot index

theorem data_independent_observed_matmul (a b tiles frame) (hb : tiles ≤ 2^28)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    (dataObservation (tileA a) (tileB b) tiles frame).output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      .realPart .f32 (matmul a b tiles (Wgmma.cCoord (lane,slot))) index.val := by
  rw [data_independent_observed_matrix _ _ _ _ hb,specification_is_matmul]

theorem data_initial_output_frame (a b tiles frame) (loc : Location)
    (hd : loc ∈ dataOutputDomain) : dataRepresentedInitial a b tiles frame loc = frame loc := by
  obtain ⟨hg,hlo,hhi⟩ := mem_data_output_domain.mp hd
  have hd : ¬(4096 ≤ loc.address ∧ loc.address < 4224) := by omega
  have he : ¬(4224 ≤ loc.address ∧ loc.address < 4352) := by omega
  have ha : ¬(65536 ≤ loc.address ∧ loc.address < 65536+2048*tiles) := by omega
  have hbase : 65536 ≤ dataBBase tiles := by dsimp [dataBBase]; omega
  have hb : ¬(dataBBase tiles ≤ loc.address ∧ loc.address < dataBBase tiles+256*tiles) := by omega
  simp only [dataRepresentedInitial,hg,ite_true,ite_eq_right hd,ite_eq_right he,ite_eq_right ha,ite_eq_right hb]

theorem data_independent_observed_frame (a b tiles frame) (hb : tiles ≤ 2^28) (loc : Location)
    (hd : loc ∈ dataOutputDomain) (hf : ¬(8192 ≤ loc.address ∧ loc.address < 10240)) :
    (dataObservation a b tiles frame).output loc = frame loc := by
  have he := data_observed_frame hb (data_observer_witness a b tiles frame hb) hd (mem_data_output_domain.mp hd).1 hf
  exact he.trans (data_initial_output_frame a b tiles frame loc hd)

theorem data_independent_observed_components (a b tiles frame) (hb : tiles ≤ 2^28) :
    Unified.TmaComponents code (completeLaunch tiles (dataRepresentedInitial a b tiles frame))
        (dataCompleteCandidate a b tiles) Tma.localShared (dataMaps tiles) (dataHistories a b tiles) ∧
    Unified.ControlAdmitted HopperStage.block (dataCompleteCandidate a b tiles) (dataHistories a b tiles) ∧
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataInitialProxyMemory a b tiles frame) (dataReadWitness a b tiles) (dataCoherenceWitness a b tiles) (dataHistories a b tiles) dataCluster ∧
    Unified.ObserverConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataInitialProxyMemory a b tiles frame) (dataReadWitness a b tiles) (dataCoherenceWitness a b tiles)
      (dataHistories a b tiles) dataCluster (dataObservation a b tiles frame) :=
  ⟨data_tma_components a b tiles frame hb,data_native_control_admitted a b tiles hb,
    data_memory_witness a b tiles frame hb,data_observer_witness a b tiles frame hb⟩

def dataOmittedObservation (a : TileA) (b : TileB) (tiles : Nat) (frame : Location → Symbolic.Byte) : Unified.Observation :=
  {dataObservation a b tiles frame with domain := []}
def dataStaleObservation (a : TileA) (b : TileB) (tiles : Nat) (frame : Location → Symbolic.Byte) : Unified.Observation :=
  {dataObservation a b tiles frame with source := fun _ => none, output := dataRepresentedInitial a b tiles frame}

theorem data_omitted_output_rejected (a b tiles frame) :
    ¬Unified.ObserverConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataInitialProxyMemory a b tiles frame) (dataReadWitness a b tiles) (dataCoherenceWitness a b tiles)
      (dataHistories a b tiles) dataCluster (dataOmittedObservation a b tiles frame) := by
  intro ho
  have hh := ho.coverage _ _ _ rfl (data_actual_output_byte a b tiles 0 0 0)
  cases hh

theorem data_stale_output_rejected (a b tiles frame) (hb : tiles ≤ 2^28) :
    ¬Unified.ObserverConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataInitialProxyMemory a b tiles frame) (dataReadWitness a b tiles) (dataCoherenceWitness a b tiles)
      (dataHistories a b tiles) dataCluster (dataStaleObservation a b tiles frame) := by
  intro ho
  have hw := data_actual_output_byte a b tiles 0 0 0
  have hd : ((⟨.global,outputWordAddress (0,0)⟩ : Location).add 0) ∈ dataOutputDomain := by
    apply mem_data_output_domain.mpr
    have hr := data_output_word_bounds 0 0
    exact ⟨rfl,by dsimp [Location.add]; omega,by dsimp [Location.add]; omega⟩
  have hh := ho.noStale _ hd (data_no_mixed_size_race a b tiles hb _) _ _ hw
  exact hh (by simpa only [dataStaleObservation,Fin.val_zero] using
    (data_causal_witness a b tiles frame hb).initialization (data_no_mixed_size_race a b tiles hb _) _ _ _ hw)

end
end Ptx.Kernels.HopperDoubleBuffer
