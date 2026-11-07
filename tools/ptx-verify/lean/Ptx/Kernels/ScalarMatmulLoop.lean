import Ptx.Kernels.ScalarMatmulSpec
import Ptx.Scalar.Updates
import Ptx.Scalar.FmaLoop

/-! Parametric execution of the ACTUAL generated inner loop (PCs 32--42).
Load answers remain arbitrary real functions. Initialization, edge masking and
global memory consistency are separate from this thread-local loop theorem.
-/
namespace Ptx.ScalarMatmulLoop
open Ptx.ISA Ptx.Scalar Ptx.ScalarMatmul
noncomputable section

abbrev Layout := Scalar.FmaLoop.Layout

theorem fragment : Scalar.FmaLoop.Fragment code 32 := by
  constructor <;> rfl

structure Inv (l : Layout) (k : Nat) (acc : ℝ) (s : Scalar.State) : Prop where
  running : s.core.thread.status = .running
  pc : s.core.thread.pc = 32
  queries : s.core.queries = 2*k
  index : lookup "%k" s.core.thread.regs = some k
  bound : lookup "%kmax" s.core.thread.regs = some l.count
  aPointer : lookup "%ap" s.core.thread.regs = some (wrap 64 (l.aBase+4*k))
  bPointer : lookup "%bp" s.core.thread.regs = some (wrap 64 (l.bBase+l.stride*k))
  stride : lookup "%stride" s.core.thread.regs = some l.stride
  output : lookup "%cp" s.core.thread.regs = some l.output
  accumulator : declarationLookup "%acc" s.floats = some (.f32,acc)
  banks : BanksDisjoint s

theorem Inv.to_fragment {l k acc s} (h : Inv l k acc s) : Scalar.FmaLoop.Inv 32 0 l k acc s :=
  ⟨h.running,h.pc,by simpa using h.queries,h.index,h.bound,h.aPointer,h.bPointer,h.stride,h.output,h.accumulator,h.banks⟩
theorem Inv.of_fragment {l k acc s} (h : Scalar.FmaLoop.Inv 32 0 l k acc s) : Inv l k acc s :=
  ⟨h.running,h.pc,by simpa using h.queries,h.index,h.bound,h.aPointer,h.bPointer,h.stride,h.output,h.accumulator,h.banks⟩

def reads (l : Layout) (k : Nat) (a b : ℝ) : List Scalar.Kind := [
  .read ⟨.global,l.aBase+4*k⟩ (Symbolic.encode .f32 a),
  .read ⟨.global,l.bBase+l.stride*k⟩ (Symbolic.encode .f32 b)]

theorem iteration (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {k : Nat} {acc a b : ℝ} {s : Scalar.State} (hi : Inv l k acc s) (hk : k < l.count)
    (ha : oracle (2*k) = .real .f32 a) (hb : oracle (2*k+1) = .real .f32 b) :
    ∃ next, Scalar.run ctx oracle code 9 s = .ok (next,reads l k a b) ∧ Inv l (k+1) (a*b+acc) next := by
  obtain ⟨next,hr,hn⟩ := Scalar.FmaLoop.iteration fragment l ctx oracle hi.to_fragment hk
    (by simpa using ha) (by simpa using hb)
  exact ⟨next,by simpa only [reads,Scalar.FmaLoop.reads] using hr,Inv.of_fragment hn⟩

structure Finished (l : Layout) (acc : ℝ) (s : Scalar.State) : Prop where
  done : s.core.thread.status = .done
  pc : s.core.thread.pc = 42
  queries : s.core.queries = 2*l.count
  accumulator : declarationLookup "%acc" s.floats = some (.f32,acc)
  output : lookup "%cp" s.core.thread.regs = some l.output
  banks : BanksDisjoint s

theorem finish (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {acc : ℝ} {s : Scalar.State} (hi : Inv l l.count acc s) :
    ∃ final, Scalar.run ctx oracle code 4 s =
      .ok (final,[.write ⟨.global,l.output⟩ (Symbolic.encode .f32 acc)]) ∧ Finished l acc final := by
  obtain ⟨last,hr,hn⟩ := Scalar.FmaLoop.finish fragment l ctx oracle hi.to_fragment
  exact ⟨last,hr,hn.done,hn.pc,by simpa using hn.queries,hn.accumulator,hn.output,hn.banks⟩

def loopReads (l : Layout) (a b : Matrix) (r c start : Nat) : Nat → List Scalar.Kind
  | 0 => []
  | n+1 => reads l start (a r start) (b start c) ++ loopReads l a b r c (start+1) n

@[simp] theorem loopReads_length (l : Layout) (a b : Matrix) (r c start count : Nat) :
    (loopReads l a b r c start count).length = 2*count := by
  induction count generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [loopReads,reads,List.length_append,List.length_cons,List.length_nil,ih]
    omega

theorem loopReads_a {l : Layout} {a b : Matrix} {r c start count i : Nat} (hi : i < count) :
    (loopReads l a b r c start count)[2*i]? =
      some (.read ⟨.global,l.aBase+4*(start+i)⟩ (Symbolic.encode .f32 (a r (start+i)))) := by
  induction count generalizing start i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [loopReads,reads]
    | succ i =>
      have h := ih (start := start+1) (i := i) (by omega)
      have hsum : start+1+i = start+(i+1) := by omega
      simpa only [loopReads,reads,List.cons_append,List.nil_append,Nat.mul_succ,
        Nat.mul_one,List.getElem?_cons_succ,hsum] using h

theorem loopReads_b {l : Layout} {a b : Matrix} {r c start count i : Nat} (hi : i < count) :
    (loopReads l a b r c start count)[2*i+1]? =
      some (.read ⟨.global,l.bBase+l.stride*(start+i)⟩ (Symbolic.encode .f32 (b (start+i) c))) := by
  induction count generalizing start i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [loopReads,reads]
    | succ i =>
      have h := ih (start := start+1) (i := i) (by omega)
      have hsum : start+1+i = start+(i+1) := by omega
      simpa only [loopReads,reads,List.cons_append,List.nil_append,Nat.mul_succ,
        Nat.mul_one,List.getElem?_cons_succ,hsum] using h

theorem loopReads_event {l : Layout} {a b : Matrix} {r c start count serial : Nat} {kind : Scalar.Kind}
    (he : (loopReads l a b r c start count)[serial]? = some kind) :
    ∃ i, i < count ∧
      ((serial = 2*i ∧ kind = .read ⟨.global,l.aBase+4*(start+i)⟩ (Symbolic.encode .f32 (a r (start+i)))) ∨
       (serial = 2*i+1 ∧ kind = .read ⟨.global,l.bBase+l.stride*(start+i)⟩ (Symbolic.encode .f32 (b (start+i) c)))) := by
  have hs := (List.getElem?_eq_some_iff.mp he).1
  rw [loopReads_length] at hs
  have hi : serial/2 < count := by omega
  have hp : serial = 2*(serial/2) ∨ serial = 2*(serial/2)+1 := by omega
  refine ⟨serial/2,hi,?_⟩
  rcases hp with hp | hp
  · left
    refine ⟨hp,?_⟩
    rw [hp,loopReads_a hi] at he
    exact (Option.some.inj he).symm
  · right
    refine ⟨hp,?_⟩
    rw [hp,loopReads_b hi] at he
    exact (Option.some.inj he).symm

/-- The count is derived by induction from remaining iterations. It is not a
chosen fuel cutoff. Replies describe local trace generation only; global memory
reasoning must separately establish that these values are the represented inputs. -/
theorem complete_suffix (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (a b : Matrix) (r c : Nat)
    (ha : ∀ k, k < l.count → oracle (2*k) = .real .f32 (a r k))
    (hb : ∀ k, k < l.count → oracle (2*k+1) = .real .f32 (b k c))
    (remaining : Nat) :
    ∀ {start s}, l.count = start+remaining → Inv l start (prefixProduct a b r c start) s →
      ∃ final, Scalar.run ctx oracle code (9*remaining+4) s =
        .ok (final,loopReads l a b r c start remaining ++
          [.write ⟨.global,l.output⟩ (Symbolic.encode .f32 (prefixProduct a b r c l.count))]) ∧
        Finished l (prefixProduct a b r c l.count) final := by
  induction remaining with
  | zero =>
    intro start s he hi
    have hstart : start = l.count := by omega
    subst start
    simpa [loopReads] using finish l ctx oracle hi
  | succ n ih =>
    intro start s he hi
    have hk : start < l.count := by omega
    obtain ⟨mid,hr,hm⟩ := iteration l ctx oracle hi hk (ha start hk) (hb start hk)
    change Inv l (start+1) (prefixProduct a b r c (start+1)) mid at hm
    obtain ⟨final,ht,hf⟩ := ih (by omega : l.count = (start+1)+n) hm
    refine ⟨final,?_,hf⟩
    rw [show 9*(n+1)+4 = 9+(9*n+4) by omega,Scalar.run_add,hr]
    simp only [Except.bind,ht,List.append_assoc,loopReads]

theorem complete_from_entry (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (a b : Matrix) (r c : Nat)
    (ha : ∀ k, k < l.count → oracle (2*k) = .real .f32 (a r k))
    (hb : ∀ k, k < l.count → oracle (2*k+1) = .real .f32 (b k c))
    {s : Scalar.State} (hi : Inv l 0 0 s) :
    ∃ final, Scalar.run ctx oracle code (9*l.count+4) s =
      .ok (final,loopReads l a b r c 0 l.count ++
        [.write ⟨.global,l.output⟩ (Symbolic.encode .f32 (prefixProduct a b r c l.count))]) ∧
      Finished l (prefixProduct a b r c l.count) final :=
  complete_suffix l ctx oracle a b r c ha hb l.count (by omega) hi

end
end Ptx.ScalarMatmulLoop
