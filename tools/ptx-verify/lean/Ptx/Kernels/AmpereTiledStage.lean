import Ptx.Kernels.AmpereTiledMma
import Ptx.Ampere.CopyStage

/-! Parameterized execution of the actual 14-slot copy/load/MMA/reuse-barrier
body. Arbitrary prior history, payloads, packed replies and MMA output answers
are retained. Entry/loop invariants, phase visibility and arithmetic agreement
must still be derived in the full kernel proof. -/
namespace Ptx.AmpereTiledStage
open Ptx.ISA Ptx.Ampere
noncomputable section
abbrev code := Generated.ampere_tiled_matmul.program

theorem copy_fragment : CopyStage.Fragment code 59 := by constructor <;> rfl
theorem mma_fragment : MmaBlock.Fragment code 65 := AmpereTiledMma.fragment

def loaded (ctx : Scalar.Context) (s : State) (p : CopyStage.Pointers) (payload : Fin 3 → List Symbolic.Byte)
    (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) : State := MmaBlock.loaded (CopyStage.prepared ctx s p payload) a b
def answer (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers) (payload : Fin 3 → List Symbolic.Byte) : Fin 4 → ℝ :=
  oracle.matrix ((CopyStage.prepared ctx s p payload).scalar.core.queries+6)
def afterMma (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers) (payload : Fin 3 → List Symbolic.Byte)
    (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) : State := mmaAction (loaded ctx s p payload a b) MmaBlock.accumulators (answer ctx oracle s p payload)
def finalState (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers) (payload : Fin 3 → List Symbolic.Byte)
    (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) : State := barrierState (afterMma ctx oracle s p payload a b) 0
def call (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers) (payload : Fin 3 → List Symbolic.Byte)
    (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (acc : Fin 4 → ℝ) : MmaCall :=
  makeMmaCall ctx (loaded ctx s p payload a b) (MmaBlock.inputs a b acc) (answer ctx oracle s p payload)
def events (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers) (payload : Fin 3 → List Symbolic.Byte)
    (pa pb : Nat) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (acc : Fin 4 → ℝ) : List Event :=
  CopyStage.events ctx s p payload ++ MmaBlock.readEvents ctx pa pb a b ++
    [.mmaEntry (call ctx oracle s p payload a b acc),.mmaReturn (call ctx oracle s p payload a b acc)] ++
    [.ordinary (.barrierArrival 0 (Ptx.Event.generation (afterMma ctx oracle s p payload a b).scalar.core 0)),
     .ordinary (.barrierReturn 0 (Ptx.Event.generation (afterMma ctx oracle s p payload a b).scalar.core 0))]

theorem execute_prefix (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (pa pb : Nat)
    (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (acc : Fin 4 → ℝ)
    (hr : s.scalar.core.thread.status = .running) (hp : s.scalar.core.thread.pc = 59)
    (hs : ∀ i, lookup (CopyStage.sourceName i) s.scalar.core.thread.regs = some (CopyStage.source p i))
    (hd : ∀ i, lookup (CopyStage.destinationName i) s.scalar.core.thread.regs = some (CopyStage.destination p i))
    (ha : lookup "%la" s.scalar.core.thread.regs = some pa)
    (hb : lookup "%lb" s.scalar.core.thread.regs = some pb)
    (hc : ∀ i, declarationLookup (MmaBlock.accumulators.get i) s.scalar.floats = some (.f32,acc i))
    (hn : ∀ i, lookup (MmaBlock.accumulators.get i) s.scalar.core.thread.regs = none)
    (hsize : ∀ i, (payload i).length = 8)
    (hq : ∀ i, oracle.bytes (s.scalar.core.queries+i.val) = payload i)
    (hqa : ∀ i, oracle.word32 (s.scalar.core.queries+3+i.val) = .packed (a i))
    (hqb : ∀ i, oracle.word32 (s.scalar.core.queries+7+i.val) = .packed (b i)) :
    Ampere.run ctx oracle code 13 s = .ok (afterMma ctx oracle s p payload a b,(events ctx oracle s p payload pa pb a b acc).take 15) := by
  let prepared := CopyStage.prepared ctx s p payload
  have hcopy := CopyStage.execute copy_fragment ctx oracle s p payload hr hp hs hd hsize hq
  have hmma := MmaBlock.execute mma_fragment ctx oracle prepared pa pb a b acc
    (by simpa [prepared] using hr) (by simp [prepared,hp])
    (by simpa [prepared] using ha) (by simpa [prepared] using hb)
    (fun i => (CopyStage.prepared_float ctx s p payload _ (hn i)).trans (hc i))
    (fun i => by simpa [prepared,Nat.add_assoc] using hqa i)
    (fun i => by
      have he : prepared.scalar.core.queries+4+i.val = s.scalar.core.queries+7+i.val := by
        simp only [prepared,CopyStage.prepared_queries]
      rw [he]
      exact hqb i)
  rw [show 13 = 6+7 from rfl,Ampere.run_add,hcopy]
  simp only [Except.bind]
  rw [hmma]
  rfl

theorem execute (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (pa pb : Nat)
    (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (acc : Fin 4 → ℝ)
    (hr : s.scalar.core.thread.status = .running) (hp : s.scalar.core.thread.pc = 59)
    (hs : ∀ i, lookup (CopyStage.sourceName i) s.scalar.core.thread.regs = some (CopyStage.source p i))
    (hd : ∀ i, lookup (CopyStage.destinationName i) s.scalar.core.thread.regs = some (CopyStage.destination p i))
    (ha : lookup "%la" s.scalar.core.thread.regs = some pa)
    (hb : lookup "%lb" s.scalar.core.thread.regs = some pb)
    (hc : ∀ i, declarationLookup (MmaBlock.accumulators.get i) s.scalar.floats = some (.f32,acc i))
    (hn : ∀ i, lookup (MmaBlock.accumulators.get i) s.scalar.core.thread.regs = none)
    (hsize : ∀ i, (payload i).length = 8)
    (hq : ∀ i, oracle.bytes (s.scalar.core.queries+i.val) = payload i)
    (hqa : ∀ i, oracle.word32 (s.scalar.core.queries+3+i.val) = .packed (a i))
    (hqb : ∀ i, oracle.word32 (s.scalar.core.queries+7+i.val) = .packed (b i)) :
    Ampere.run ctx oracle code 14 s = .ok (finalState ctx oracle s p payload a b,events ctx oracle s p payload pa pb a b acc) := by
  have hprefix := execute_prefix ctx oracle s p payload pa pb a b acc hr hp hs hd ha hb hc hn hsize hq hqa hqb
  have hpost := Ampere.barrier_step (bid := 0) (ctx := ctx) (oracle := oracle) (code := code) (s := afterMma ctx oracle s p payload a b)
    (by simpa [afterMma,loaded,mmaAction,Ampere.advance,Ptx.advance] using hr)
    (by simp only [afterMma,loaded,mma_pc_once,MmaBlock.loaded_pc,CopyStage.prepared_pc,hp]; rfl)
  rw [show 14 = 13+1 from rfl,Ampere.run_add,hprefix]
  simp only [Except.bind,Ampere.run,hpost,List.append_nil]
  rfl

theorem after_mma_pc (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) :
    (afterMma ctx oracle s p payload a b).scalar.core.thread.pc = s.scalar.core.thread.pc+13 := by
  simp [afterMma,loaded,mma_pc_once,Nat.add_assoc]
theorem after_mma_status (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) :
    (afterMma ctx oracle s p payload a b).scalar.core.thread.status = s.scalar.core.thread.status := rfl
theorem after_mma_generation (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) :
    Ptx.Event.generation (afterMma ctx oracle s p payload a b).scalar.core 0 = Ptx.Event.generation s.scalar.core 0+1 :=
  CopyStage.prepared_generation ctx s p payload

theorem final_accumulator (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (i : Fin 4) :
    declarationLookup (MmaBlock.accumulators.get i) (finalState ctx oracle s p payload a b).scalar.floats =
      some (.f32,answer ctx oracle s p payload i) := by
  rw [finalState,barrier_float]
  · exact MmaBlock.final_float _ a b _ i
  · exact MmaBlock.final_nat _ a b _ i

theorem final_register_frame (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (name : String)
    (ha : ∀ i, name ≠ MmaBlock.aRegisters.get i) (hb : ∀ i, name ≠ MmaBlock.bRegisters.get i)
    (hd : name ∉ MmaBlock.accumulators.names) :
    lookup name (finalState ctx oracle s p payload a b).scalar.core.thread.regs = lookup name s.scalar.core.thread.regs := by
  have hcontains : MmaBlock.accumulators.names.contains name = false := by simp [hd]
  simp only [finalState,barrier_nat,afterMma,mma_nat,hcontains,Bool.false_eq_true,ite_false,loaded]
  rw [MmaBlock.loaded_nat_frame _ a b name ha hb]
  rfl

theorem final_nat (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (i : Fin 4) :
    lookup (MmaBlock.accumulators.get i) (finalState ctx oracle s p payload a b).scalar.core.thread.regs = none := by
  rw [finalState,barrier_nat]
  exact MmaBlock.final_nat _ a b _ i

@[simp] theorem final_pc (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) :
    (finalState ctx oracle s p payload a b).scalar.core.thread.pc = s.scalar.core.thread.pc+14 := by
  simp [finalState,afterMma,loaded,mma_pc_once,Nat.add_assoc]
@[simp] theorem final_queries (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) :
    (finalState ctx oracle s p payload a b).scalar.core.queries = s.scalar.core.queries+10 := by
  simp [finalState,afterMma,loaded,mma_query_once,Nat.add_assoc]
@[simp] theorem final_status (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) :
    (finalState ctx oracle s p payload a b).scalar.core.thread.status = s.scalar.core.thread.status := by
  simp [finalState,afterMma,loaded,mmaAction,Ampere.advance,Ptx.advance]

@[simp] theorem final_groups (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) :
    (finalState ctx oracle s p payload a b).groups = s.groups+1 := rfl
@[simp] theorem final_mma_calls (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) :
    (finalState ctx oracle s p payload a b).mmaCalls = s.mmaCalls+1 := rfl

theorem final_generation (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) :
    Ptx.Event.generation (finalState ctx oracle s p payload a b).scalar.core 0 = Ptx.Event.generation s.scalar.core 0+2 := by
  rw [finalState,barrier_generation]
  change Ptx.Event.generation (CopyStage.prepared ctx s p payload).scalar.core 0+1 = _
  rw [CopyStage.prepared_generation]

theorem final_copies (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) :
    (finalState ctx oracle s p payload a b).copies = s.copies ++
      [CopyStage.operation ctx s p payload 0,CopyStage.operation ctx s p payload 1,CopyStage.operation ctx s p payload 2] := by
  simp [finalState,afterMma,loaded,barrierState,mmaAction,Ampere.advance]

theorem events_length (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (pa pb : Nat) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (acc : Fin 4 → ℝ) :
    (events ctx oracle s p payload pa pb a b acc).length = 17 := rfl

end
end Ptx.AmpereTiledStage
