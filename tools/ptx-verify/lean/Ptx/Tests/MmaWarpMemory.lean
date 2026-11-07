import Ptx.Tests.MmaWarpGraph
import Ptx.Event.Publication

/-! A represented input map and actual byte ownership for the generated warp
probe. Fixed numerical smoke evidence, not parameterized tiled correctness. -/
namespace Ptx.MmaWarpTests
open Ptx.ISA Ptx.Ampere
noncomputable section

def representedInitial (loc : Location) : Symbolic.Byte :=
  if loc.space = .global ∧ loc.address < 768 then
    inputPair.encode[loc.address%4]?.getD (.bits (byte 165))
  else .bits (byte 165)
def representedLaunch : Scalar.Launch := {launch with initial := representedInitial}

theorem read_bounds (lane : Mma.Lane) (i : Fin 6) :
    (readBase lane i).space = .global ∧ (readBase lane i).address+4 ≤ 768 ∧ (readBase lane i).address%4 = 0 := by
  have hl := lane.isLt
  have hi := i.isLt
  fin_cases i <;> simp [readBase,Nat.add_mod,Nat.mul_mod] <;> omega

theorem write_bounds (lane : Mma.Lane) (i : Fin 4) :
    (writeBase lane i).space = .global ∧ 768 ≤ (writeBase lane i).address ∧ (writeBase lane i).address+4 ≤ 1280 := by
  have hl := lane.isLt
  have hi := i.isLt
  dsimp [writeBase]
  exact ⟨rfl,by omega,by omega⟩

theorem initial_read {lane i loc value}
    (hp : Ptx.Event.payloadByte (readBase lane i) inputPair.encode loc = some value) : representedInitial loc = value := by
  obtain ⟨offset,ho,rfl⟩ := Ptx.Event.payload_location hp
  have hoff : offset < 4 := by simpa only [PackedF16.encode_size] using ho
  rw [Ptx.Event.payloadByte_offset] at hp
  have hb := read_bounds lane i
  have hrange : ((readBase lane i).add offset).address < 768 := by
    simp only [Location.add]
    omega
  have hmod : ((readBase lane i).add offset).address%4 = offset := by
    simp only [Location.add,Nat.add_mod,hb.2.2,Nat.zero_add,Nat.mod_eq_of_lt hoff]
  dsimp only [Location.add] at hrange hmod
  simp only [representedInitial,Location.add,hb.1,hrange,true_and,ite_true,hmod,hp,Option.getD_some]

theorem input_output_disjoint {read writer loc vr vw}
    (hr : candidate.readByte read loc = some vr) (hw : candidate.writeByte writer loc = some vw) : False := by
  obtain ⟨lane,i,_,hp⟩ := read_cases hr
  obtain ⟨other,j,_,hq⟩ := write_cases hw
  have ha := Ptx.Event.payloadByte_bounds hp
  have hb := Ptx.Event.payloadByte_bounds hq
  rw [PackedF16.encode_size] at ha
  have hrange := (read_bounds lane i).2.1
  have hwrite := (write_bounds other j).2.1
  omega

theorem unique_writes {loc a b va vb}
    (ha : candidate.writeByte a loc = some va) (hb : candidate.writeByte b loc = some vb) : a = b := by
  obtain ⟨lane,i,rfl,hp⟩ := write_cases ha
  obtain ⟨other,j,rfl,hq⟩ := write_cases hb
  have ha := Ptx.Event.payloadByte_bounds hp
  have hb := Ptx.Event.payloadByte_bounds hq
  have hsize : outputBytes.length = 4 := by rfl
  rw [hsize] at ha hb
  dsimp only [writeBase] at ha hb
  have hi := i.isLt
  have hj := j.isLt
  have hl : lane.val = other.val := by omega
  have hs : i.val = j.val := by omega
  have hl' := Fin.ext hl
  have hs' := Fin.ext hs
  subst other
  subst j
  rfl

theorem no_race_of_write {a b loc value} {rf : ReadsFrom}
    (hw : candidate.writeByte a loc = some value) : ¬ MemoryGraph.DataRace candidate.memoryGraph rf a b := by
  intro hrace
  obtain ⟨lane,i,rfl,_⟩ := write_cases hw
  obtain ⟨overlap,ha,hb⟩ := hrace.overlap
  have ha' : (candidate.writeByte (writeNode lane i) overlap).isSome = true := by
    rcases ha with ha | ha
    · simp [MemoryGraph.Graph.readByte,Candidate.memoryGraph,write_kind,
        Ptx.Event.Kind.readByte] at ha
    · exact ha
  obtain ⟨written,hwrite⟩ := Option.isSome_iff_exists.mp ha'
  rcases hb with hr | hw'
  · obtain ⟨readValue,hread⟩ := Option.isSome_iff_exists.mp hr
    exact input_output_disjoint hread hwrite
  · obtain ⟨otherValue,hother⟩ := Option.isSome_iff_exists.mp hw'
    have he : writeNode lane i = b := unique_writes hwrite hother
    subst b
    exact hrace.notStrong (MemoryGraph.write_self_strong (c := candidate.memoryGraph) hwrite)

theorem race_free (rf : ReadsFrom) (a b : Node) : ¬ MemoryGraph.DataRace candidate.memoryGraph rf a b := by
  intro hr
  rcases hr.conflict with ⟨loc,value,hw⟩ | ⟨loc,value,hw⟩
  · exact no_race_of_write hw hr
  · exact no_race_of_write hw (MemoryGraph.data_race_symm hr)

theorem placeholder_initial_rejected (rf : ReadsFrom) (co : Coherence) :
    ¬ MemoryConstraints candidate launch.initial rf co := by
  intro hc
  have hr : candidate.readByte (readNode 0 0) ⟨.global,0⟩ = some (.realPart .f16 1 0) := by rfl
  have he := MemoryGraph.race_free_eligible (race_free rf) (readNode 0 0) (⟨.global,0⟩ : Location)
  have hn : ∀ writer, candidate.memoryGraph.writeByte writer ⟨.global,0⟩ = none := by
    intro writer
    cases hw : candidate.memoryGraph.writeByte writer ⟨.global,0⟩ with
    | none => rfl
    | some v => exact (input_output_disjoint hr hw).elim
  have hv := MemoryGraph.unwritten_read_initial hc.agreement he hr hn
  change Symbolic.Byte.realPart .f16 1 0 = .bits (byte 165) at hv
  cases hv

end
end Ptx.MmaWarpTests
