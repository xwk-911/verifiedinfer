import Ptx.Event.Execution
import Ptx.Generated.Copy

/-! Trace-generation tests, deliberately separate from memory-model litmus tests.
Arbitrary oracle answers are candidate values, not evidence they are PTX-allowed.
-/
namespace Ptx.EventTests
open Ptx Ptx.ISA Ptx.Event

def id0 : ThreadId := ⟨.zero, .zero⟩
def context : Context := ⟨id0, []⟩
def g (address : Nat) : Location := ⟨.global, address⟩

theorem byte_roundtrip (value : Nat) :
    decodeLE (encodeU32 value) = value % 2^32 := decode_encodeU32 value

example : (encodeU32 0x12345678).map Fin.val = [0x78, 0x56, 0x34, 0x12] := by decide

theorem shared_isolation (a b : ThreadId) (h : a.cta ≠ b.cta) (x y : Nat) :
    Location.resolve .shared a x ≠ Location.resolve .shared b y := shared_separate_ctas h x y

def copyContext : Context := ⟨id0, [("src", 0), ("dst", 4), ("n", 1)]⟩

/-- The actual generated AST is used. This proves trace provenance for arbitrary
data, not consistency or functional correctness of the new memory model. -/
theorem generated_copy_trace (value : Nat) :
    (Event.run copyContext (fun _ => value) Generated.copy.program 12 {}).map Prod.snd =
      .ok [.read (g 0) (encodeU32 (wrap 32 value)),
           .write (g 4) (encodeU32 (wrap 32 value))] := by rfl

def branchCode : List Instr := [
  .load .global "%r" ⟨.imm 0, 0⟩,
  .setp .eq "%p" (.reg "%r") (.imm 0),
  .branch "%p" true 5,
  .store .global ⟨.imm 4, 0⟩ (.imm 1),
  .ret,
  .store .global ⟨.imm 4, 0⟩ (.imm 2),
  .ret]

theorem load_controls_branch_zero :
    (Event.run context (fun _ => 0) branchCode 5 {}).map Prod.snd =
      .ok [.read (g 0) (encodeU32 0), .write (g 4) (encodeU32 2)] := by rfl

theorem load_controls_branch_one :
    (Event.run context (fun _ => 1) branchCode 5 {}).map Prod.snd =
      .ok [.read (g 0) (encodeU32 1), .write (g 4) (encodeU32 1)] := by rfl

theorem independent_oracle_queries :
    (Event.run context (fun i => if i = 0 then 7 else 9)
      [.load .global "%a" ⟨.imm 0, 0⟩, .load .global "%b" ⟨.imm 4, 0⟩] 2 {}).map Prod.snd =
      .ok [.read (g 0) (encodeU32 7), .read (g 4) (encodeU32 9)] := by rfl

theorem oracle_u32_truncation :
    (Event.run context (fun _ => 2^32 + 7)
      [.load .global "%r" ⟨.imm 0, 0⟩] 1 {}).map Prod.snd =
      .ok [.read (g 0) (encodeU32 7)] := by decide

theorem per_barrier_generations :
    (Event.run context (fun _ => 0) [.barrier 0, .barrier 1, .barrier 0] 3 {}).map Prod.snd =
      .ok [.barrierArrival 0 0, .barrierReturn 0 0,
           .barrierArrival 1 0, .barrierReturn 1 0,
           .barrierArrival 0 1, .barrierReturn 0 1] := by rfl

theorem no_steps_after_exit :
    Event.run context (fun _ => 0) [.ret] 2 {} = .error .blocked := by rfl

theorem bad_pc_rejected :
    Event.run context (fun _ => 0) [] 1 {} = .error (.invalidPC 0) := by rfl

theorem missing_register_rejected :
    Event.run context (fun _ => 0) [.store .global ⟨.imm 0, 0⟩ (.reg "%absent")] 1 {} =
      .error (.register "%absent") := by rfl

def exited : State := { thread := { status := .done } }
def returnTrace : ThreadTrace := ⟨id0, fun _ => 0, 1, exited, []⟩
def launch : Launch := ⟨⟨.one, .one⟩, [], fun _ => byte 0⟩

theorem return_candidate_wellFormed :
    Candidate.WellFormed [.ret] launch ⟨[returnTrace]⟩ := by
  refine ⟨by simp [Geometry.Valid, Dim3.Positive, launch, Dim3.one],
    by simp [returnTrace], ?_, ?_⟩
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    exact ⟨by simp [ThreadId.Valid, Dim3.Within, returnTrace, id0, Dim3.zero, launch, Dim3.one], rfl⟩
  · intro id hid
    obtain ⟨hc, ht⟩ := hid
    rcases id with ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩
    simp only [Dim3.Within, launch, Dim3.one] at hc ht
    have hcx : cx = 0 := by omega
    have hcy : cy = 0 := by omega
    have hcz : cz = 0 := by omega
    have htx : tx = 0 := by omega
    have hty : ty = 0 := by omega
    have htz : tz = 0 := by omega
    subst cx cy cz tx ty tz
    exact ⟨returnTrace, by simp, rfl⟩

theorem return_candidate_complete : Candidate.Complete ⟨[returnTrace]⟩ := by
  intro t ht
  simp only [List.mem_singleton] at ht
  subst t
  rfl

/-- Completeness alone must not hide a missing launched thread. -/
theorem missing_thread_rejected : ¬ Candidate.WellFormed [.ret] launch ⟨[]⟩ := by
  intro h
  obtain ⟨t, ht, _⟩ := h.2.2.2 id0
    (by simp [ThreadId.Valid, Dim3.Within, id0, Dim3.zero, launch, Dim3.one])
  simp at ht

theorem duplicate_thread_rejected :
    ¬ Candidate.WellFormed [.ret] launch ⟨[returnTrace, returnTrace]⟩ := by
  intro h
  simpa using h.2.1

end Ptx.EventTests
