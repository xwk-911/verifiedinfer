import Ptx.Generated.MmaProbe
import Ptx.Ampere.Checked
import Ptx.Ampere.MmaLocalRules
import Ptx.Kernels.CpAsyncCopyGraph

/-! Actual generated source completion deliberately permits unrelated matrix
answers locally. A one-lane launch is then rejected by full-warp matching.
These tests make no claim of universal probe/tiled-kernel correctness. -/
namespace Ptx.MmaLocalTests
open Ptx.ISA Ptx.Ampere
noncomputable section
def id : ThreadId := ⟨.zero,.zero⟩
def params : Bindings := [("A",0),("B",512),("C",768)]
def ctx : Scalar.Context := {id := id,params := params,block := .one}
def oracle : Oracle := {
  scalar := fun _ => .integer 0
  bytes := fun _ => []
  word32 := fun _ => .packed ⟨1,2⟩
  matrix := fun _ _ => 100
}
def result : State × List Event := ((Ampere.run ctx oracle Generated.mma_probe.program 25 {}).toOption).getD ({},[])
def trace : ThreadTrace := ⟨id,oracle,25,result.1,result.2⟩
def candidate : Candidate := ⟨[trace]⟩
def launch : Scalar.Launch := ⟨⟨.one,.one⟩,params,fun _ => .bits (byte 165)⟩

theorem source_produced : Ampere.Produced Generated.mma_probe.program params .one trace := by rfl
theorem source_done : trace.final.scalar.core.thread.status = .done := by rfl
theorem source_queries : trace.final.scalar.core.queries = 7 := by rfl
theorem source_mma_count : trace.final.mmaCalls = 1 := by rfl
theorem source_wellFormed : WellFormed Generated.mma_probe.program launch candidate := by
  refine ⟨by norm_num [launch,Geometry.Valid,Dim3.Positive,Dim3.one],by simp [candidate],?_,?_⟩
  · intro t ht
    have he : t = trace := List.mem_singleton.mp ht
    subst t
    exact ⟨by norm_num [trace,id,launch,ThreadId.Valid,Dim3.Within,Dim3.one,Dim3.zero],source_produced⟩
  · intro thread hv
    have hi := CpAsyncCopyGraph.valid_thread_unique hv
    exact ⟨trace,List.mem_singleton_self _,hi.symm⟩

def fallback : MmaCall := ⟨0,0,0,0,⟨fun _ => ⟨0,0⟩,fun _ => ⟨0,0⟩,fun _ => 0⟩,fun _ => 0⟩
def call : MmaCall := match (trace.events[7]? : Option Ampere.Event) with | some (Ampere.Event.mmaReturn mc) => mc | _ => fallback
theorem emitted_return : candidate.eventAt ⟨id,7⟩ = some (.mmaReturn call) := by rfl
theorem actual_mma_pc : call.pc = 19 := by rfl
theorem oracle_output_retained : call.output 0 = 100 := by rfl
theorem actual_store : candidate.eventAt ⟨id,8⟩ = some (.ordinary (.write ⟨.global,768⟩ (Symbolic.encode .f32 100))) := by rfl

theorem only_owner {event kind} (he : candidate.eventAt event = some kind) : event.thread = id := by
  obtain ⟨t,ht,hid,_⟩ := eventAt_trace he
  have ht' : t = trace := List.mem_singleton.mp ht
  subst t
  exact hid.symm
theorem missing_warp_rejected : ¬ MmaConditions Generated.mma_probe.program launch candidate := by
  intro hm
  obtain ⟨members,_,_,hvalid,_⟩ := hm _ _ emitted_return
  have hp := (hvalid (1 : Mma.Lane)).1
  have hl := (hvalid (1 : Mma.Lane)).2.1
  have hid := only_owner hp.2.2.2.1
  have htag := hp.2.2.2.2.2.2.2
  rw [hid] at htag
  change (members (1 : Mma.Lane)).call.lane.val = 0 at htag
  have hh := congrArg Fin.val hl
  omega
theorem checked_missing_warp_rejected (rf : ReadsFrom) (co : Coherence) :
    ¬ CheckedConditions Generated.mma_probe.program launch candidate rf co := fun h => missing_warp_rejected h.mma

def aRegs : Registers4 := ⟨"a0","a1","a2","a3"⟩
def bRegs : Registers2 := ⟨"b0","b1"⟩
def cRegs : Registers4 := ⟨"c0","c1","c2","c3"⟩
def prepared : State := {
  scalar := {floats := [("c0",(.f32,7)),("c1",(.f32,8)),("c2",(.f32,9)),("c3",(.f32,10))]}
  packed := [("a0",⟨1,2⟩),("a1",⟨3,4⟩),("a2",⟨5,6⟩),("a3",⟨7,8⟩),("b0",⟨9,10⟩),("b1",⟨11,12⟩)]}
def preparedInputs : MmaInputs := ⟨fun i => if i.val = 0 then ⟨1,2⟩ else if i.val = 1 then ⟨3,4⟩ else if i.val = 2 then ⟨5,6⟩ else ⟨7,8⟩,
  fun i => if i.val = 0 then ⟨9,10⟩ else ⟨11,12⟩,fun i => if i.val = 0 then 7 else if i.val = 1 then 8 else if i.val = 2 then 9 else 10⟩
theorem input_capture : readMmaInputs prepared aRegs bRegs cRegs = .ok preparedInputs := by rfl
theorem accumulator_alias_step : Ampere.step ctx oracle [.mma cRegs aRegs bRegs cRegs] prepared =
    .ok (mmaAction prepared cRegs (fun _ => 100),
      [.mmaEntry (makeMmaCall ctx prepared preparedInputs (fun _ => 100)),.mmaReturn (makeMmaCall ctx prepared preparedInputs (fun _ => 100))]) :=
  mma_step (d := cRegs) (a := aRegs) (b := bRegs) (c := cRegs) rfl rfl (by decide) input_capture
theorem old_c_captured : preparedInputs.c 0 = 7 := by rfl
theorem new_c_written : Scalar.eval .f32 (mmaAction prepared cRegs (fun _ => 100)).scalar (.reg "c0") = .ok 100 := by rfl
theorem packed_alias_removed : ("a0",PackedF16.mk 1 2) ∉ (mmaAction prepared aRegs (fun _ => 100)).packed :=
  mma_clears_packed prepared aRegs _ (by simp [Registers4.names,aRegs]) _

theorem integer_bits_are_not_mma_pairs :
    readMmaInputs (wordAction prepared "a0" (.integer 42)) aRegs bRegs cRegs = .error (.packedRegister "a0") := by rfl

theorem integer_scalar_overwrite_invalidates_pair :
    readMmaInputs (finishScalar prepared (.integer (.mov 32 "a0" (.imm 42))) prepared.scalar) aRegs bRegs cRegs =
      .error (.packedRegister "a0") := by rfl

theorem float_scalar_overwrite_invalidates_pair :
    readMmaInputs (finishScalar prepared (.mov .f32 "a0" (.reg "c0")) prepared.scalar) aRegs bRegs cRegs =
      .error (.packedRegister "a0") := by rfl

theorem repeated_destinations_rejected :
    Ampere.step ctx oracle [.mma ⟨"c0","c0","c2","c3"⟩ aRegs bRegs cRegs] prepared = .error .mmaDestinations := by rfl

theorem source_call_lane_derived : call.lane = 0 := by rfl
theorem source_call_warp_derived : call.warp = 0 := by rfl
theorem source_call_ordinal_derived : call.ordinal = 0 := by rfl

end
end Ptx.MmaLocalTests
