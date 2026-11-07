import Ptx.Kernels.AmpereTiledFragmentInputs
import Ptx.Kernels.AmpereTiledControl
import Ptx.Kernels.AmpereTiledSourceCandidate

/-! Independent source witness answers from the fixed initial memory and
matrix tiles. They do not invoke the universal correctness theorem. Constructing
these complete traces alone is not memory/warp/observer admission. -/
namespace Ptx.AmpereTiledWitnessOracle
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledGraph Ptx.AmpereTiledTrace Ptx.AmpereTiledEvents
noncomputable section

def lane (id : ThreadId) : Mma.Lane := ⟨(id.tid.x+4*id.tid.y)%32,by omega⟩
def aPair (a : Matrix) (id : ThreadId) (phase : Nat) (reg : Fin 4) : PackedF16 :=
  Mma.packA (Mma.gatherA (tileA a id.cta.y phase)) (lane id,reg)
def bPair (b : Matrix) (id : ThreadId) (phase : Nat) (reg : Fin 2) : PackedF16 :=
  Mma.packB (Mma.gatherB (tileB b id.cta.x phase)) (lane id,reg)
def accumulator (a b : Matrix) (id : ThreadId) (phase : Nat) (slot : Fin 4) : ℝ :=
  Mma.gatherC (tileC a b id.cta.y id.cta.x phase) (lane id,slot)
def payload (cfg : Config) (launch : Scalar.Launch) (id : ThreadId) (phase : Nat) (part : Fin 3) : List Symbolic.Byte :=
  List.ofFn (fun offset : Fin 8 => launch.initial ⟨.global,AmpereTiledBounds.copyStart cfg (context launch id) phase part+offset.val⟩)
def oracle (cfg : Config) (launch : Scalar.Launch) (a b : Matrix) (id : ThreadId) : Oracle := {
  scalar := fun _ => .integer 0
  bytes := fun q => payload cfg launch id (q/10) ⟨q%10%3,by omega⟩
  word32 := fun q =>
    if h : 3 ≤ q%10 ∧ q%10 < 7 then .packed (aPair a id (q/10) ⟨q%10-3,by omega⟩)
    else if h : 7 ≤ q%10 ∧ q%10 < 9 then .packed (bPair b id (q/10) ⟨q%10-7,by omega⟩)
    else .integer 0
  matrix := fun q => accumulator a b id (q/10+1)
}

theorem bytes_query (cfg : Config) (launch : Scalar.Launch) (a b : Matrix) (id : ThreadId)
    (phase : Nat) (part : Fin 3) :
    (oracle cfg launch a b id).bytes (10*phase+part.val) = payload cfg launch id phase part := by
  have hi := part.isLt
  have hd : (10*phase+part.val)/10 = phase := by omega
  have hm : (10*phase+part.val)%10%3 = part.val := by omega
  simp only [oracle,hd]
  congr 1
  exact Fin.ext hm

theorem a_query (cfg : Config) (launch : Scalar.Launch) (a b : Matrix) (id : ThreadId)
    (phase : Nat) (reg : Fin 4) : (oracle cfg launch a b id).word32 (10*phase+3+reg.val) = .packed (aPair a id phase reg) := by
  have hi := reg.isLt
  have hd : (10*phase+3+reg.val)/10 = phase := by omega
  have hm : (10*phase+3+reg.val)%10 = 3+reg.val := by omega
  simp only [oracle,hm,hd]
  rw [dite_eq_left (by omega)]
  congr 2
  exact Fin.ext (by simp)
theorem b_query (cfg : Config) (launch : Scalar.Launch) (a b : Matrix) (id : ThreadId)
    (phase : Nat) (reg : Fin 2) : (oracle cfg launch a b id).word32 (10*phase+7+reg.val) = .packed (bPair b id phase reg) := by
  have hi := reg.isLt
  have hd : (10*phase+7+reg.val)/10 = phase := by omega
  have hm : (10*phase+7+reg.val)%10 = 7+reg.val := by omega
  simp only [oracle,hm,hd]
  rw [dite_eq_right (by omega),dite_eq_left (by omega)]
  congr 2
  exact Fin.ext (by simp)

def replies (cfg : Config) (launch : Scalar.Launch) (a b : Matrix) (id : ThreadId) :
    ReplySet cfg (context launch id) (oracle cfg launch a b id) := {
  payload := payload cfg launch id
  a := aPair a id
  b := bPair b id
  size := by intro _ _ _; simp [payload]
  bytes := by intro phase _ part; simpa [AmpereTiledEntry.loopConfig] using bytes_query cfg launch a b id phase part
  wordA := by intro phase _ reg; simpa [AmpereTiledEntry.loopConfig] using a_query cfg launch a b id phase reg
  wordB := by intro phase _ reg; simpa [AmpereTiledEntry.loopConfig] using b_query cfg launch a b id phase reg
}
def execution (cfg : Config) (launch : Scalar.Launch) (a b : Matrix) : Candidate :=
  AmpereTiledSourceCandidate.candidate cfg launch (oracle cfg launch a b) (replies cfg launch a b)

theorem source {cfg launch a b} (hp : Pre cfg a b launch) (ha : Active cfg) :
    SourceInfo cfg launch (execution cfg launch a b) := by
  apply AmpereTiledSourceCandidate.source_info hp.1 launch (oracle cfg launch a b) (replies cfg launch a b) _ hp.2.2.1 ha
  rw [hp.2.2.2]
  exact AmpereTiledInit.canonical_params cfg

theorem lane_eq {cfg : Config} {id : ThreadId} (hv : id.Valid (geometry cfg)) :
    lane id = AmpereTiledFragmentInputs.lane id hv := by
  apply Fin.ext
  have hx : id.tid.x < 4 := hv.2.1
  have hy : id.tid.y < 8 := hv.2.2.1
  simp only [lane,AmpereTiledFragmentInputs.lane,Tiled.lane]
  omega

theorem c_values (cfg : Config) (launch : Scalar.Launch) (a b : Matrix) (id : ThreadId) (phase : Nat) :
    cValues (oracle cfg launch a b id) phase = accumulator a b id phase := by
  funext slot
  cases phase with
  | zero => simp [cValues,accumulator,Mma.gatherC,tileC,partialProduct,product]
  | succ phase =>
    have hd : (10*(phase+1)-1)/10+1 = phase+1 := by omega
    simp [cValues,oracle,hd]

theorem matrix_query (cfg : Config) (launch : Scalar.Launch) (a b : Matrix) (id : ThreadId) (phase : Nat) :
    (oracle cfg launch a b id).matrix (10*phase+9) = accumulator a b id (phase+1) := by
  have hd : (10*phase+9)/10 = phase := by omega
  simp only [oracle,hd]

theorem payload_byte (cfg : Config) (launch : Scalar.Launch) (id : ThreadId) (phase : Nat) (part : Fin 3)
    (offset : Fin 8) : (payload cfg launch id phase part)[offset.val]? =
      some (launch.initial ⟨.global,AmpereTiledBounds.copyStart cfg (context launch id) phase part+offset.val⟩) := by
  fin_cases offset <;> rfl

theorem trace_oracle {cfg launch a b t} (ht : t ∈ (execution cfg launch a b).traces) : t.oracle = oracle cfg launch a b t.id := by
  obtain ⟨id,_,rfl⟩ := List.mem_map.mp ht
  rfl

theorem phase_event {cfg launch a b} (hp : Pre cfg a b launch) (ha : Active cfg) {id : ThreadId}
    (hv : id.Valid launch.geometry) {phase slot : Nat} (hphase : phase < cfg.k/16) (hslot : slot < 17) :
    (execution cfg launch a b).eventAt ⟨id,17*phase+slot⟩ =
      (stepEvents cfg (context launch id) (oracle cfg launch a b id) (replies cfg launch a b id) phase)[slot]? := by
  let t := AmpereTiledSourceCandidate.trace cfg launch (oracle cfg launch a b) (replies cfg launch a b) id
  have ht : t ∈ (execution cfg launch a b).traces := List.mem_map.mpr ⟨id,Geometry.mem_threads.mpr hv,rfl⟩
  rw [show (⟨id,17*phase+slot⟩ : Ptx.Event.EventId) = ⟨t.id,17*phase+slot⟩ from rfl,member_event (source hp ha) ht]
  exact AmpereTiledEvents.phase_event _ _ _ _ phase slot hphase hslot

theorem return_shape {cfg launch a b event call}
    (he : (execution cfg launch a b).eventAt event = some (.mmaReturn call)) :
    ∃ id, id.Valid launch.geometry ∧ ∃ phase, phase < cfg.k/16 ∧
      event = ⟨id,17*phase+14⟩ ∧ call = callAt cfg (context launch id) (oracle cfg launch a b id) (replies cfg launch a b id) phase := by
  obtain ⟨t,ht,hid,hget⟩ := eventAt_trace he
  obtain ⟨id,hmem,rfl⟩ := List.mem_map.mp ht
  obtain ⟨phase,hphase,hserial,hcall⟩ := AmpereTiledInventory.mma_return_cases hget
  refine ⟨id,Geometry.mem_threads.mp hmem,phase,hphase,?_,hcall⟩
  cases event
  simp_all [AmpereTiledSourceCandidate.trace]

theorem barriers {cfg launch a b} (hp : Pre cfg a b launch) (ha : Active cfg) : BarrierParticipation (execution cfg launch a b) :=
  AmpereTiledControl.barriers (source hp ha)
theorem control {cfg launch a b} (hp : Pre cfg a b launch) (ha : Active cfg) : ControlAcyclic (execution cfg launch a b) :=
  AmpereTiledControl.control (source hp ha)

end
end Ptx.AmpereTiledWitnessOracle
