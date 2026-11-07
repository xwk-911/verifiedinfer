import Ptx.Kernels.HopperStageMemoryWitness
import Ptx.Hopper.UnifiedObservation

namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def outputDomain : List Location := (List.range 2056).map (fun offset => ⟨.global,8188+offset⟩)
def outputOwner (address : Nat) : Wgmma.Lane × Wgmma.Slot := Wgmma.cOwner
  (⟨(address-8192)/32%64,Nat.mod_lt _ (by decide)⟩,⟨(address-8192)/4%8,Nat.mod_lt _ (by decide)⟩)
def outputSelect (loc : Location) : Option Unified.Node :=
  if loc.space = .global ∧ 8192 ≤ loc.address ∧ loc.address < 10240 then
    some (.base (.tma (.source (storeId (outputOwner loc.address).1 (outputOwner loc.address).2))))
  else none
def observation (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame : Location → Symbolic.Byte) : Unified.Observation :=
  Unified.selectedObservation Tma.localShared Access.globalDescriptor (candidate a b) (initialProxyMemory a b frame) outputSelect outputDomain

theorem mem_output_domain {loc} : loc ∈ outputDomain ↔ loc.space = .global ∧ 8188 ≤ loc.address ∧ loc.address < 10244 := by
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
theorem output_owner_byte {lane slot address}
    (hb : wordAddress lane slot ≤ address ∧ address < wordAddress lane slot+4) :
    outputOwner address = (lane,slot) := by
  rw [wordAddress,actual_output_address] at hb
  have hrow := (Wgmma.cCoord (lane,slot)).1.isLt
  have hcol := (Wgmma.cCoord (lane,slot)).2.isLt
  have he : (⟨(address-8192)/32%64,Nat.mod_lt _ (by decide)⟩,⟨(address-8192)/4%8,Nat.mod_lt _ (by decide)⟩) = Wgmma.cCoord (lane,slot) := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega
  rw [outputOwner,he,Wgmma.c_owner_coord]
theorem output_selection {a b writer loc value} (hg : loc.space = .global)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (candidate a b) writer loc = some value) : outputSelect loc = some writer := by
  obtain ⟨lane,slot,rfl,hb⟩ := global_writer_metadata hg hw
  have hbounds := word_address_bounds lane slot
  have hloc : loc.space = .global ∧ 8192 ≤ loc.address ∧ loc.address < 10240 := ⟨hg,by omega,by omega⟩
  simp only [outputSelect,if_pos hloc,output_owner_byte hb]
theorem stage_observer_witness (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame : Location → Symbolic.Byte) :
    Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate a b)
      (initialProxyMemory a b frame) readWitness (coherenceWitness a b) histories cluster (observation a b frame) := by
  apply Unified.selected_observer (source_complete a b)
  · intro loc hl; exact (mem_output_domain.mp hl).1
  · intro writer loc value hg hw
    obtain ⟨lane,slot,_,hb⟩ := global_writer_metadata hg hw
    have hw := word_address_bounds lane slot
    exact mem_output_domain.mpr ⟨hg,by omega,by omega⟩
  · intro loc hl writer value hw
    exact output_selection (mem_output_domain.mp hl).1 hw
  · exact (stage_coherence a b readWitness).irrefl
theorem stage_observer_eligible (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (rf : Unified.ReadsFrom) (loc : Location) :
    Unified.ObserverEligible Tma.localShared Access.globalDescriptor (candidate a b) histories cluster rf loc := by
  refine ⟨stage_no_mixed_size_race a b rf,?_⟩
  rintro ⟨left,right,hl,hr,hrace⟩
  obtain ⟨vl,hvl⟩ := Option.isSome_iff_exists.mp hl
  obtain ⟨vr,hvr⟩ := Option.isSome_iff_exists.mp hr
  have he := stage_unique_writers hvl hvr
  subst right
  exact hrace.notStrong (Unified.write_self_strong hvl)

end
end Ptx.Kernels.HopperStage
