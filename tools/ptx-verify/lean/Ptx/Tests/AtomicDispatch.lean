import Ptx.Kernels.AtomicDispatchCandidate

/-! Locally complete two-CTA candidates and model rejection for every equal
ticket assignment. Output and global witnesses are checked in separate modules. -/
namespace Ptx.AtomicDispatchTests
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.AtomicDispatchTrace Ptx.AtomicDispatchEvent
noncomputable section

def cfg : Config := {
  counter := 0,x := 64,y := 128
  counterEnd := by decide,xEnd := by decide,yEnd := by decide
  counterAligned := by decide,xAligned := by decide,yAligned := by decide
  counterX := by unfold WordsDisjoint; decide
  counterY := by unfold WordsDisjoint; decide
  xy := by unfold WordsDisjoint; decide
}
def initial (loc : Location) : Symbolic.Byte :=
  if loc.space = .global ∧ loc.address < 4 then .bits (byte 0) else .bits (byte 165)
def launch : Scalar.Launch := ⟨geometry,[("junk",42),("Y",128),("Counter",0),("X",64)],initial⟩

theorem pre : Pre cfg launch := by
  refine ⟨rfl,⟨rfl,rfl,rfl⟩,?_⟩
  intro offset ho
  have hoff : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by omega
  rcases hoff with rfl | rfl | rfl | rfl <;> rfl

theorem arbitrary_replies_locally_wellFormed (values : Nat → Nat) :
    Scalar.WellFormed code launch (canonical cfg values) ∧ (canonical cfg values).Complete :=
  ⟨canonical_wellFormed cfg values pre.1 pre.2.1,canonical_complete cfg values⟩

/-- Even though every constant reply assignment gives a well-formed completed
local launch, NO reads-from/coherence choice can make equal tickets consistent. -/
theorem equal_replies_not_consistent (value : Nat) (rf : ReadsFrom) (co : Coherence) :
    ¬ GenericMemoryConditions (canonical cfg (fun _ => value)) initial rf co := by
  intro hm
  have h := tickets cfg (canonical_wellFormed cfg (fun _ => value) pre.1 pre.2.1)
    (canonical_complete cfg (fun _ => value)) pre.1 pre.2.1 pre.2.2 hm
    (canonical_member cfg (fun _ => value) (cta := 0) (by decide))
    (canonical_member cfg (fun _ => value) (cta := 1) (by decide)) rfl rfl
  change (wrap 32 value = 0 ∧ wrap 32 value = 1) ∨ (wrap 32 value = 1 ∧ wrap 32 value = 0) at h
  rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> omega

theorem one_ticket_requires_eleven_steps (thread : ThreadId) (oracle : Scalar.Oracle)
    (ho : oracle 0 = .integer 1) {count final emitted}
    (hr : Scalar.run {id := thread,params := launch.params} oracle code count {} = .ok (final,emitted))
    (hd : final.core.thread.status = .done) : count = 11 := by
  obtain ⟨value,hv,hcount,_,_⟩ := completed_source_shape {id := thread,params := launch.params} oracle
    cfg.counter cfg.x cfg.y pre.2.1 (by decide) (by decide) (by decide) hr hd
  have he : value = 1 := Reply.integer.inj (ho.symm.trans hv).symm
  subst value
  exact hcount

theorem noninteger_reply_cannot_complete (thread : ThreadId) (oracle : Scalar.Oracle)
    {format : Symbolic.Format} {value : ℝ} (ho : oracle 0 = .real format value) {count final emitted}
    (hr : Scalar.run {id := thread,params := launch.params} oracle code count {} = .ok (final,emitted)) :
    final.core.thread.status ≠ .done :=
  completed_bad_reply_impossible {id := thread,params := launch.params} oracle cfg.counter cfg.x cfg.y pre.2.1
    (by decide) (by decide) (by decide) ho hr

end
end Ptx.AtomicDispatchTests
