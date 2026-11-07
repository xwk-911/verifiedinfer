import Ptx.Ampere.Inversion
import Ptx.Ampere.CopyStage

/-! Successful complete execution forces all three eight-byte copy replies.
The proof advances through actual issue slots, retaining arbitrary old ledgers. -/
namespace Ptx.Ampere.CopyStage
open Ptx.ISA
noncomputable section

theorem copy_slot {code : List Instr} {base : Nat} (hf : Fragment code base) (i : Fin 3) :
    code[base+i.val]? = some (.copy .ca {base := .reg (destinationName i)} {base := .reg (sourceName i)} 8) := by
  fin_cases i
  · exact hf.copy0
  · exact hf.copy1
  · exact hf.copy2

theorem issue_one {code : List Instr} {base : Nat} (hf : Fragment code base)
    (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (i : Fin 3)
    (hr : s.scalar.core.thread.status = .running) (hp : s.scalar.core.thread.pc = base+i.val)
    (hs : lookup (sourceName i) s.scalar.core.thread.regs = some (source p i))
    (hd : lookup (destinationName i) s.scalar.core.thread.regs = some (destination p i))
    (hb : (payload i).length = 8) (hq : oracle.bytes s.scalar.core.queries = payload i) :
    step ctx oracle code s = .ok (issued s (operation ctx s p payload i),[.issue s.copies.length (operation ctx s p payload i)]) := by
  have hc := copy_step (ctx := ctx) (oracle := oracle) (code := code) (s := s)
    hr (hp ▸ copy_slot hf i) (by decide)
    (show evalAddr ctx.id.tid.x s.scalar.core.thread {base := .reg (sourceName i)} = .ok (wrap 64 (source p i)) by
      simp [evalAddr,Ptx.eval,hs,bind,Except.bind,pure,Except.pure])
    (show evalAddr ctx.id.tid.x s.scalar.core.thread {base := .reg (destinationName i)} = .ok (wrap 64 (destination p i)) by
      simp [evalAddr,Ptx.eval,hd,bind,Except.bind,pure,Except.pure])
    (hq ▸ hb)
  simpa [issued,operation,issue,hq] using hc

theorem completed_sizes {code : List Instr} {base : Nat} (hf : Fragment code base)
    {ctx oracle s p count last emitted}
    (hr : s.scalar.core.thread.status = .running) (hp : s.scalar.core.thread.pc = base)
    (hs : ∀ i, lookup (sourceName i) s.scalar.core.thread.regs = some (source p i))
    (hd : ∀ i, lookup (destinationName i) s.scalar.core.thread.regs = some (destination p i))
    (hc : run ctx oracle code count s = .ok (last,emitted)) (hl : last.scalar.core.thread.status = .done) :
    ∀ i : Fin 3, (oracle.bytes (s.scalar.core.queries+i.val)).length = 8 := by
  let payload (i : Fin 3) := oracle.bytes (s.scalar.core.queries+i.val)
  let s1 := issued s (operation ctx s p payload 0)
  let s2 := issued s1 (operation ctx s1 p payload 1)
  have hzero : run ctx oracle code 0 s = .ok (s,[]) := rfl
  obtain ⟨_,_,hstep0⟩ := step_after_running_prefix hc hl hzero hr
  have hsize0 : (payload 0).length = 8 := copy_size_of_step hr (hp ▸ hf.copy0) hstep0
  have h0 := issue_one hf ctx oracle s p payload 0 hr (by simpa using hp) (hs 0) (hd 0) hsize0 rfl
  have hone : run ctx oracle code 1 s = .ok (s1,[.issue s.copies.length (operation ctx s p payload 0)]) := by
    simpa only [List.nil_append] using run_extend_step hzero h0
  obtain ⟨_,_,hstep1⟩ := step_after_running_prefix hc hl hone (by simpa [s1,issued,issue,advance,Ptx.advance] using hr)
  have hslot1 : code[s1.scalar.core.thread.pc]? = some (.copy .ca {base := .reg "%sah"} {base := .reg "%ah"} 8) := by
    simpa [s1,issued,issue,advance,Ptx.advance,hp] using hf.copy1
  have hsize1 : (payload 1).length = 8 := by
    simpa [payload,s1,issued,issue,advance,Ptx.advance] using copy_size_of_step (by simpa [s1,issued,issue,advance,Ptx.advance] using hr) hslot1 hstep1
  have h1 := issue_one hf ctx oracle s1 p payload 1
    (by simpa [s1,issued,issue,advance,Ptx.advance] using hr)
    (by simpa [s1,issued,issue,advance,Ptx.advance] using hp)
    (hs 1) (hd 1) hsize1 (by simp [payload,s1,issued,issue,advance,Ptx.advance])
  have htwo := run_extend_step hone h1
  obtain ⟨_,_,hstep2⟩ := step_after_running_prefix hc hl htwo (by simpa [s2,s1,issued,issue,advance,Ptx.advance] using hr)
  have hslot2 : code[s2.scalar.core.thread.pc]? = some (.copy .ca {base := .reg "%sb"} {base := .reg "%b"} 8) := by
    simpa [s2,s1,issued,issue,advance,Ptx.advance,hp,Nat.add_assoc] using hf.copy2
  have hsize2 : (payload 2).length = 8 := by
    simpa [payload,s2,s1,issued,issue,advance,Nat.add_assoc] using copy_size_of_step
      (by simpa [s2,s1,issued,issue,advance,Ptx.advance] using hr) hslot2 hstep2
  intro i
  fin_cases i
  · exact hsize0
  · exact hsize1
  · exact hsize2

end
end Ptx.Ampere.CopyStage
