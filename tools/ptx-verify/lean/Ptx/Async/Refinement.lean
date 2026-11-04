import Ptx.Kernels.Copy
import Ptx.Async.Invariant

/-! A precise, scalar-buffer data refinement for completed copy commands.
Each async buffer occupies one u32 cell, dead buffers encode uninitialized cells.
Live source data must be a real u32 word; addresses and non-aliasing are explicit.
This connects completed executions of the ACTUAL generated PTX copy to execute,
not a microstep simulation of CPU/GPU overlap or a GPU runtime correctness proof.
-/
namespace Ptx.AsyncPtxRefinement

def encode (b : Async.Buffer) : Option Nat := if b.alive then some b.value else none
def cells (s : Async.State) : List (Option Nat) := s.buffers.map encode

def copyConfig (s : Async.State) (src dst : Nat) (a b : Async.Buffer)
    (ha : Async.getBuffer s src = .ok a) (hb : Async.getBuffer s dst = .ok b)
    (hne : src ≠ dst) (hw : a.value < 2^32)
    (hs64 : 4*(src+1) < 2^64) (hd64 : 4*(dst+1) < 2^64) : CopyContract.Config where
  src := src
  dst := dst
  n := 1
  count := 1
  input _ := a.value
  before := cells s
  coverage := by decide
  count32 := by decide
  src64 := hs64
  dst64 := hd64
  srcBound := by
    obtain ⟨hget,_⟩ := Async.getBuffer_iff.mp ha
    have hlt := (List.getElem?_eq_some_iff.mp hget).1
    simpa [cells] using Nat.add_one_le_of_lt hlt
  dstBound := by
    obtain ⟨hget,_⟩ := Async.getBuffer_iff.mp hb
    have hlt := (List.getElem?_eq_some_iff.mp hget).1
    simpa [cells] using Nat.add_one_le_of_lt hlt
  disjoint := by omega
  initialized := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    obtain ⟨hget,halive⟩ := Async.getBuffer_iff.mp ha
    simp [cells, List.getElem?_map,hget,encode,halive,CopyContract.word,
      CopyContract.wrap_small hw]

/-- Abstract copy changes exactly the corresponding destination cell. -/
theorem copy_cells {s : Async.State} {src dst : Nat} {a b : Async.Buffer}
    (ha : Async.getBuffer s src = .ok a) (hb : Async.getBuffer s dst = .ok b) :
    ∃ next, Async.execute s (.copy src dst) = .ok next ∧
      cells next = (cells s).set dst (some a.value) := by
  let next := { s with buffers := s.buffers.set dst { b with value := a.value } }
  refine ⟨next,?_,?_⟩
  · simp [Async.execute,ha,hb,next,bind,Except.bind,pure,Except.pure]
  · obtain ⟨_,halive⟩ := Async.getBuffer_iff.mp hb
    simp [cells,next,List.map_set,encode,halive]

/-- Every completed finite execution satisfying the generated copy contract has
exactly the abstract copy's data. No finite input or schedule enumeration is used. -/
theorem copy_refines {s : Async.State} {src dst : Nat} {a b : Async.Buffer}
    (ha : Async.getBuffer s src = .ok a) (hb : Async.getBuffer s dst = .ok b)
    (hne : src ≠ dst) (hw : a.value < 2^32)
    (hs64 : 4*(src+1) < 2^64) (hd64 : 4*(dst+1) < 2^64)
    {m m' : Machine}
    (hp : CopyContract.Pre (copyConfig s src dst a b ha hb hne hw hs64 hd64) m)
    (he : Steps CopyContract.code m m')
    (hdone : m'.threads.all (fun t => t.status == .done) = true) :
    ∃ next, Async.execute s (.copy src dst) = .ok next ∧ m'.globalMem = cells next := by
  let c := copyConfig s src dst a b ha hb hne hw hs64 hd64
  have hpost := CopyContract.correct c m m' hp he hdone
  obtain ⟨next,hexec,hcells⟩ := copy_cells ha hb
  refine ⟨next,hexec,?_⟩
  rw [hcells]
  apply List.ext_getElem?
  intro i
  by_cases hi : dst = i
  · subst i
    have hbnd : dst < (cells s).length := by have := c.dstBound; change dst+1 ≤ (cells s).length at this; omega
    rw [List.getElem?_set_self hbnd]
    have hout := hpost.2.2.1 0 (by change 0 < 1; decide)
    simpa [c,copyConfig,CopyContract.word,CopyContract.wrap_small hw] using hout
  · rw [List.getElem?_set_ne hi]
    apply hpost.2.2.2
    change i < dst ∨ dst+1 ≤ i
    omega

/-- Identity use commands preserve cells and require an actually live buffer. -/
theorem use_refines {s : Async.State} {bid : Nat} {b : Async.Buffer}
    (hb : Async.getBuffer s bid = .ok b) :
    Async.execute s (.use bid) = .ok s ∧ cells s = cells s := by
  simp [Async.execute,hb,bind,Except.bind,pure,Except.pure]

end Ptx.AsyncPtxRefinement
