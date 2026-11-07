import Ptx.Kernels.AmpereTiledWitnessOracle

/-! Independent mandatory full-warp MMA admission for the input-determined
source witness. Every participant is an actual source event, with checked PCs
and exact-real packed matrix arithmetic. This does not claim memory admission. -/
namespace Ptx.AmpereTiledWitnessMma
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledGraph Ptx.AmpereTiledTrace Ptx.AmpereTiledEvents
open Ptx.AmpereTiledWitnessOracle
noncomputable section

def peer (id : ThreadId) (lane : Mma.Lane) : ThreadId := ⟨id.cta,⟨lane.val%4,lane.val/4,0⟩⟩
def call (cfg : Config) (launch : Scalar.Launch) (a b : Matrix) (id : ThreadId) (phase : Nat) : MmaCall :=
  callAt cfg (context launch id) (oracle cfg launch a b id) (replies cfg launch a b id) phase
def members (cfg : Config) (launch : Scalar.Launch) (a b : Matrix) (id : ThreadId) (phase : Nat) (lane : Mma.Lane) : MmaParticipant :=
  ⟨⟨peer id lane,17*phase+13⟩,⟨peer id lane,17*phase+14⟩,call cfg launch a b (peer id lane) phase⟩

theorem peer_valid {cfg : Config} {id : ThreadId} (hv : id.Valid (geometry cfg)) (lane : Mma.Lane) :
    (peer id lane).Valid (geometry cfg) := by
  refine ⟨hv.1,?_,?_,by change (0 : Nat) < 1; decide⟩
  · change lane.val%4 < 4
    omega
  · change lane.val/4 < 8
    have hl := lane.isLt
    omega
theorem peer_lane (id : ThreadId) (l : Mma.Lane) : AmpereTiledWitnessOracle.lane (peer id l) = l := by
  apply Fin.ext
  have hl := l.isLt
  simp only [AmpereTiledWitnessOracle.lane,peer]
  omega
theorem peer_self {cfg : Config} {id : ThreadId} (hv : id.Valid (geometry cfg)) :
    peer id (AmpereTiledWitnessOracle.lane id) = id := by
  have hx : id.tid.x < 4 := hv.2.1
  have hy : id.tid.y < 8 := hv.2.2.1
  have hz : id.tid.z = 0 := by have hh : id.tid.z < 1 := hv.2.2.2; omega
  cases id with
  | mk cta tid =>
    cases tid
    simp only [peer,AmpereTiledWitnessOracle.lane,ThreadId.mk.injEq,Dim3.mk.injEq,true_and]
    simp only at hx hy hz
    omega

theorem call_lane {cfg launch a b id phase} (hp : Pre cfg a b launch) (hv : id.Valid launch.geometry) :
    (call cfg launch a b id phase).lane = AmpereTiledWitnessOracle.lane id := by
  have hv' : (context launch id).id.Valid (geometry cfg) := by simpa only [context,hp.2.2.1] using hv
  exact (AmpereTiledFragmentInputs.call_lane _ _ _ hv' (congrArg Geometry.block hp.2.2.1) phase).trans (lane_eq hv').symm
theorem call_warp {cfg launch a b id phase} (hp : Pre cfg a b launch) (hv : id.Valid launch.geometry) :
    (call cfg launch a b id phase).warp = 0 := by
  have hv' : id.Valid (geometry cfg) := by simpa only [hp.2.2.1] using hv
  have hx : id.tid.x < 4 := hv'.2.1
  have hy : id.tid.y < 8 := hv'.2.2.1
  have hz : id.tid.z = 0 := by have hh : id.tid.z < 1 := hv'.2.2.2; omega
  change linearThread (context launch id)/32 = 0
  simp only [linearThread,context,hp.2.2.1,geometry,hz,Nat.mul_zero,Nat.add_zero]
  omega

theorem participant_valid {cfg launch a b id phase} (hp : Pre cfg a b launch) (ha : Active cfg)
    (hv : id.Valid launch.geometry) (hphase : phase < cfg.k/16) (l : Mma.Lane) :
    (members cfg launch a b id phase l).Valid AmpereTiledGraph.code launch (execution cfg launch a b) := by
  have hpeer : (peer id l).Valid launch.geometry := by
    rw [hp.2.2.1] at hv ⊢
    exact peer_valid hv l
  have hentry : (execution cfg launch a b).eventAt ⟨peer id l,17*phase+13⟩ = some (.mmaEntry (call cfg launch a b (peer id l) phase)) := by
    rw [AmpereTiledWitnessOracle.phase_event hp ha hpeer hphase (by decide : 13 < 17),phase_events]
    rfl
  have hreturn : (execution cfg launch a b).eventAt ⟨peer id l,17*phase+14⟩ = some (.mmaReturn (call cfg launch a b (peer id l) phase)) := by
    rw [AmpereTiledWitnessOracle.phase_event hp ha hpeer hphase (by decide : 14 < 17),phase_events]
    rfl
  exact ⟨rfl,by simp [members],hentry,hreturn,mma_source_pc (source hp ha).formed (.inl hentry),
    mma_source_pc (source hp ha).formed (.inr hreturn),rfl,rfl⟩

theorem arithmetic (cfg : Config) (launch : Scalar.Launch) (a b : Matrix) (id : ThreadId) (phase : Nat) (l : Mma.Lane) (slot : Fin 4) :
    (members cfg launch a b id phase l).call.output slot =
      Mma.packedResults (fun p => (members cfg launch a b id phase p.1).call.inputs.a p.2)
        (fun p => (members cfg launch a b id phase p.1).call.inputs.b p.2)
        (fun p => (members cfg launch a b id phase p.1).call.inputs.c p.2) (l,slot) := by
  have hA : (fun p => (members cfg launch a b id phase p.1).call.inputs.a p.2) =
      Mma.packA (Mma.gatherA (tileA a id.cta.y phase)) := by
    funext ⟨lane,reg⟩
    change (callAt _ _ _ _ _).inputs.a reg = _
    rw [AmpereTiledFragmentInputs.call_a]
    simp only [replies,aPair]
    rw [peer_lane]
    rfl
  have hB : (fun p => (members cfg launch a b id phase p.1).call.inputs.b p.2) =
      Mma.packB (Mma.gatherB (tileB b id.cta.x phase)) := by
    funext ⟨lane,reg⟩
    change (callAt _ _ _ _ _).inputs.b reg = _
    rw [AmpereTiledFragmentInputs.call_b]
    simp only [replies,bPair]
    rw [peer_lane]
    rfl
  have hC : (fun p => (members cfg launch a b id phase p.1).call.inputs.c p.2) =
      Mma.gatherC (tileC a b id.cta.y id.cta.x phase) := by
    funext ⟨lane,reg⟩
    change (callAt _ _ _ _ _).inputs.c reg = _
    rw [call_old_c,c_values]
    simp only [accumulator]
    rw [peer_lane]
    rfl
  rw [hA,hB,hC,Mma.packed_results_gather,mma_accumulation_step]
  change (callAt _ _ _ _ _).output slot = _
  rw [call_output,matrix_query]
  simp only [accumulator]
  rw [peer_lane]
  rfl

theorem mma {cfg launch a b} (hp : Pre cfg a b launch) (ha : Active cfg) :
    MmaConditions AmpereTiledGraph.code launch (execution cfg launch a b) := by
  intro event returned he
  obtain ⟨id,hv,phase,hphase,rfl,rfl⟩ := return_shape he
  have hv' : id.Valid (geometry cfg) := by simpa only [hp.2.2.1] using hv
  refine ⟨members cfg launch a b id phase,?_,?_,?_,arithmetic cfg launch a b id phase⟩
  · change (⟨peer id ((call cfg launch a b id phase).lane),17*phase+14⟩ : Ptx.Event.EventId) = _
    rw [call_lane hp hv,peer_self hv']
  · change call cfg launch a b (peer id ((call cfg launch a b id phase).lane)) phase = call cfg launch a b id phase
    rw [call_lane hp hv,peer_self hv']
  · intro lane
    have hpeer : (peer id lane).Valid launch.geometry := by rw [hp.2.2.1]; exact peer_valid hv' lane
    refine ⟨participant_valid hp ha hv hphase lane,?_,rfl,?_,?_,?_⟩
    · exact (call_lane hp hpeer).trans (peer_lane id lane)
    · change (call cfg launch a b (peer id lane) phase).warp = (call cfg launch a b id phase).warp
      rw [call_warp hp hpeer,call_warp hp hv]
    · change (callAt _ _ _ _ _).ordinal = (callAt _ _ _ _ _).ordinal
      rw [call_ordinal,call_ordinal]
    · change (callAt _ _ _ _ _).pc = (callAt _ _ _ _ _).pc
      rw [call_pc,call_pc]

end
end Ptx.AmpereTiledWitnessMma
