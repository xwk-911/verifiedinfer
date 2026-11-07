import Ptx.Kernels.HopperDoubleBufferKernelSource

/-! Exact source global-write inventory of the constructed complete candidate.
TMA/native memory effects are separately expanded by graph admission. This
projection concerns ordinary source writes, not an admitted final heap. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def globalWrite : Wgmma.Event → Option (Nat × List Symbolic.Byte)
  | .base (.ampere (.ordinary (.write ⟨.global,address⟩ bytes))) => some (address,bytes)
  | _ => none

theorem initialization_no_global_write (leader : Bool) : (initializationEvents leader).filterMap globalWrite = [] := by
  cases leader <;> rfl

theorem initial_copies_no_global_write (tiles : Nat) (leader : Bool) : (initialCopies tiles leader).filterMap globalWrite = [] := by
  cases leader <;> rfl

theorem wait_replicate_no_global_write (context : Scalar.Context) (bar parity retries : Nat) (answer : Bool) :
    (List.replicate retries (waitEvent context bar parity answer)).filterMap globalWrite = [] := by
  induction retries with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,List.filterMap_cons,waitEvent,globalWrite] using ih

theorem prelude_no_global_write (context : Scalar.Context) (reply : Wgmma.Oracle) (s : Wgmma.State)
    (tile tiles : Nat) (leader : Bool) (mapA mapB : Nat) :
    (preludeEvents context reply s tile tiles leader mapA mapB).filterMap globalWrite = [] := by
  by_cases h : needsPrefetch tile tiles leader
  · simp only [preludeEvents,h,ite_true,prefetchTransferEvents,List.filterMap_cons,List.filterMap_nil,globalWrite]
  · simp only [preludeEvents,h,ite_false,List.filterMap_nil]

theorem iteration_no_global_write (context : Scalar.Context) (reply : Wgmma.Oracle) (s : Wgmma.State)
    (tile tiles retries : Nat) (leader : Bool) (mapA mapB : Nat) (values : Fin 4 → ℝ) :
    (iterationEvents context reply s tile tiles retries leader mapA mapB values).filterMap globalWrite = [] := by
  simp only [iterationEvents,List.filterMap_append]
  rw [wait_replicate_no_global_write]
  simp only [List.filterMap_cons,List.filterMap_nil,waitEvent,globalWrite,prelude_no_global_write,
    computeEvents,advanceEvents,List.nil_append,List.append_nil]

theorem loop_no_global_write (context : Scalar.Context) (reply : Wgmma.Oracle) (first tiles : Nat)
    (leader : Bool) (retries : Nat → Nat) (s : Wgmma.State) (values : Fin 4 → ℝ) (mapA mapB n : Nat) :
    (loopEvents context reply first tiles leader retries s values mapA mapB n).filterMap globalWrite = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [loopEvents,List.filterMap_append,iteration_no_global_write,ih,List.nil_append]

theorem pre_output_no_global_write (tiles : Nat) (lane : Wgmma.Lane) :
    (preOutputEvents tiles lane).filterMap globalWrite = [] := by
  by_cases h : tiles = 0
  · simp only [preOutputEvents,h,ite_true,initialization_no_global_write]
  · simp only [preOutputEvents,h,ite_false,kernelLoopEvents,List.filterMap_append,
      initialization_no_global_write,initial_copies_no_global_write,loop_no_global_write,List.nil_append]

theorem return_no_global_write (context : Scalar.Context) (s : Wgmma.State) (leader : Bool) :
    (returnEvents context s leader).filterMap globalWrite = [] := by cases leader <;> rfl

theorem output_write_inventory (lane : Wgmma.Lane) (values : Fin 4 → ℝ) :
    (outputWriteEvents lane values).filterMap globalWrite =
      (List.ofFn (fun i : Fin 4 => (wrap 64 (HopperStage.outFinal lane+HopperStage.storeOffset i),Symbolic.encode .f32 (values i)))) := by
  rfl

theorem complete_write_inventory (tiles : Nat) (lane : Wgmma.Lane) :
    (completeEvents tiles lane).filterMap globalWrite =
      List.ofFn (fun i : Fin 4 => (8192+4*(8*(Wgmma.cCoord (lane,i)).1.val+(Wgmma.cCoord (lane,i)).2.val),Symbolic.encode .f32 0)) := by
  simp only [completeEvents,outputEvents,List.filterMap_append,pre_output_no_global_write,
    return_no_global_write,List.nil_append,List.append_nil,output_write_inventory]
  congr 1
  funext i
  rw [output_write_address]

theorem complete_write_count (tiles : Nat) (lane : Wgmma.Lane) :
    ((completeEvents tiles lane).filterMap globalWrite).length = 4 := by
  rw [complete_write_inventory,List.length_ofFn]

theorem complete_write_bounds (tiles : Nat) (lane : Wgmma.Lane) (address : Nat) (bytes : List Symbolic.Byte)
    (hm : (address,bytes) ∈ (completeEvents tiles lane).filterMap globalWrite) :
    8192 ≤ address ∧ address+bytes.length ≤ 10240 ∧ bytes.length = 4 := by
  rw [complete_write_inventory] at hm
  obtain ⟨i,he⟩ := List.mem_ofFn.mp hm
  have ha := congrArg Prod.fst he
  have hb := congrArg Prod.snd he
  simp only [Symbolic.encode_length,Symbolic.Format.bytes] at hb
  have hrow := (Wgmma.cCoord (lane,i)).1.isLt
  have hcol := (Wgmma.cCoord (lane,i)).2.isLt
  have hlen : bytes.length = 4 := by rw [←hb,Symbolic.encode_length]; rfl
  simp only [Prod.fst] at ha
  exact ⟨by omega,by omega,hlen⟩

def outputWordAddress (owner : Wgmma.Lane × Wgmma.Slot) : Nat :=
  8192+4*(8*(Wgmma.cCoord owner).1.val+(Wgmma.cCoord owner).2.val)
def outputByteAddress (owner : Wgmma.Lane × Wgmma.Slot) (index : Fin 4) : Nat := outputWordAddress owner+index.val

theorem output_byte_unique {left right : Wgmma.Lane × Wgmma.Slot} {i j : Fin 4}
    (he : outputByteAddress left i = outputByteAddress right j) : left = right ∧ i = j := by
  have hcol := (Wgmma.cCoord left).2.isLt
  have hother := (Wgmma.cCoord right).2.isLt
  have hi := i.isLt
  have hj := j.isLt
  dsimp [outputByteAddress,outputWordAddress] at he
  have hc : Wgmma.cCoord left = Wgmma.cCoord right := by
    apply Prod.ext <;> apply Fin.ext <;> omega
  exact ⟨Wgmma.c_unique_owner hc,Fin.ext (by omega)⟩

theorem output_byte_covered (offset : Nat) (hb : offset < 2048) :
    ∃ owner : Wgmma.Lane × Wgmma.Slot, ∃ index : Fin 4, outputByteAddress owner index = 8192+offset := by
  let coord : Wgmma.CCoord := (⟨offset/32,by omega⟩,⟨(offset/4)%8,Nat.mod_lt _ (by decide)⟩)
  refine ⟨Wgmma.cOwner coord,⟨offset%4,Nat.mod_lt _ (by decide)⟩,?_⟩
  simp only [outputByteAddress,outputWordAddress,Wgmma.c_coord_owner]
  dsimp [coord]
  omega

theorem complete_output_byte_covered (tiles offset : Nat) (hb : offset < 2048) :
    ∃ lane : Wgmma.Lane, ∃ address bytes index,
      (address,bytes) ∈ (completeEvents tiles lane).filterMap globalWrite ∧
      index < bytes.length ∧ address+index = 8192+offset := by
  obtain ⟨⟨lane,slot⟩,index,he⟩ := output_byte_covered offset hb
  refine ⟨lane,outputWordAddress (lane,slot),Symbolic.encode .f32 0,index.val,?_,?_,he⟩
  · rw [complete_write_inventory]
    exact List.mem_ofFn.mpr ⟨slot,rfl⟩
  · simpa only [Symbolic.encode_length,Symbolic.Format.bytes] using index.isLt

end
end Ptx.Kernels.HopperDoubleBuffer
