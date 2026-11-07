import Ptx.Kernels.HopperDoubleBufferStoreInventory
import Ptx.Hopper.UnifiedObservation

/-! A completed generic-proxy observer compatible with the independently
constructed RF/co and repeated source. Only global output/frame bytes are
observed; reused shared bytes keep their separate multi-writer semantics. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def dataOutputDomain : List Location := (List.range 2056).map (fun offset => ⟨.global,8188+offset⟩)
def dataOutputOwner (address : Nat) : Wgmma.Lane × Wgmma.Slot := Wgmma.cOwner
  (⟨(address-8192)/32%64,Nat.mod_lt _ (by decide)⟩,⟨(address-8192)/4%8,Nat.mod_lt _ (by decide)⟩)
def dataOutputSelect (a : TileA) (b : TileB) (tiles : Nat) (loc : Location) : Option Unified.Node :=
  if loc.space = .global ∧ 8192 ≤ loc.address ∧ loc.address < 10240 then
    some (.base (.tma (.source (dataStoreId a b tiles (dataOutputOwner loc.address).1 (dataOutputOwner loc.address).2))))
  else none
def dataObservation (a : TileA) (b : TileB) (tiles : Nat) (frame : Location → Symbolic.Byte) : Unified.Observation :=
  Unified.selectedObservation Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
    (dataInitialProxyMemory a b tiles frame) (dataOutputSelect a b tiles) dataOutputDomain

theorem mem_data_output_domain {loc} : loc ∈ dataOutputDomain ↔ loc.space = .global ∧ 8188 ≤ loc.address ∧ loc.address < 10244 := by
  constructor
  · intro hm
    obtain ⟨offset,ho,rfl⟩ := List.mem_map.mp hm
    have hb := List.mem_range.mp ho
    exact ⟨rfl,by change 8188 ≤ 8188+offset; omega,by change 8188+offset < 10244; omega⟩
  · rintro ⟨hs,hlo,hhi⟩
    refine List.mem_map.mpr ⟨loc.address-8188,List.mem_range.mpr (by omega),?_⟩
    rcases loc with ⟨space,address⟩
    simp only at hs hlo hhi
    simp only [Location.mk.injEq]
    exact ⟨hs.symm,by omega⟩

theorem data_output_word_bounds (lane : Wgmma.Lane) (slot : Wgmma.Slot) :
    8192 ≤ outputWordAddress (lane,slot) ∧ outputWordAddress (lane,slot)+4 ≤ 10240 := by
  have hr := (Wgmma.cCoord (lane,slot)).1.isLt
  have hc := (Wgmma.cCoord (lane,slot)).2.isLt
  dsimp only [outputWordAddress]
  omega

theorem data_output_owner_byte {lane slot address}
    (hb : outputWordAddress (lane,slot) ≤ address ∧ address < outputWordAddress (lane,slot)+4) :
    dataOutputOwner address = (lane,slot) := by
  have hrow := (Wgmma.cCoord (lane,slot)).1.isLt
  have hcol := (Wgmma.cCoord (lane,slot)).2.isLt
  dsimp only [outputWordAddress] at hb
  have he : (⟨(address-8192)/32%64,Nat.mod_lt _ (by decide)⟩,⟨(address-8192)/4%8,Nat.mod_lt _ (by decide)⟩) = Wgmma.cCoord (lane,slot) := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega
  rw [dataOutputOwner,he,Wgmma.c_owner_coord]

theorem data_output_selection {a b tiles writer loc value} (hb : tiles ≤ 2^28) (hg : loc.space = .global)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) writer loc = some value) :
    dataOutputSelect a b tiles loc = some writer := by
  obtain ⟨lane,slot,rfl,hbounds⟩ := data_global_writer_metadata hb hg hw
  have hr := data_output_word_bounds lane slot
  have hloc : loc.space = .global ∧ 8192 ≤ loc.address ∧ loc.address < 10240 := ⟨hg,by omega,by omega⟩
  simp only [dataOutputSelect,ite_eq_left hloc,data_output_owner_byte hbounds]

theorem data_observer_witness (a b tiles frame) (hb : tiles ≤ 2^28) :
    Unified.ObserverConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataInitialProxyMemory a b tiles frame) (dataReadWitness a b tiles) (dataCoherenceWitness a b tiles)
      (dataHistories a b tiles) dataCluster (dataObservation a b tiles frame) := by
  apply Unified.selected_observer (data_candidate_local a b tiles hb)
  · intro loc hl; exact (mem_data_output_domain.mp hl).1
  · intro writer loc value hg hw
    obtain ⟨lane,slot,_,hl⟩ := data_global_writer_metadata hb hg hw
    have hr := data_output_word_bounds lane slot
    exact mem_data_output_domain.mpr ⟨hg,by omega,by omega⟩
  · intro loc hl writer value hw
    exact data_output_selection hb (mem_data_output_domain.mp hl).1 hw
  · exact (data_coherent_witness a b tiles hb).irrefl

theorem data_global_observer_eligible (a b tiles) (hb : tiles ≤ 2^28) (rf : Unified.ReadsFrom) (loc : Location)
    (hg : loc.space = .global) :
    Unified.ObserverEligible Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster rf loc := by
  refine ⟨data_no_mixed_size_race a b tiles hb rf,?_⟩
  rintro ⟨left,right,hl,hr,hrace⟩
  obtain ⟨vl,hvl⟩ := Option.isSome_iff_exists.mp hl
  obtain ⟨vr,hvr⟩ := Option.isSome_iff_exists.mp hr
  have he := data_global_unique_writers hb hg hvl hvr
  subst right
  exact hrace.notStrong (Unified.write_self_strong hvl)

end
end Ptx.Kernels.HopperDoubleBuffer
