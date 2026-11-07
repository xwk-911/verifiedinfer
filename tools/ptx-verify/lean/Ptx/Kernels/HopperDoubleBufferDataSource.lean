import Ptx.Kernels.HopperDoubleBufferDataLoop
import Ptx.Kernels.HopperDoubleBufferMatmul
import Ptx.Kernels.HopperDoubleBufferWriteInventory

/-! Full arbitrary-real source witness with instruction-derived arithmetic
replies. It produces the specification's symbolic output bytes. It is not a
universal kernel theorem: chosen tensor/byte replies still need admission
against the launch's memory and inter-thread/resource execution graph. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

theorem data_loop_control_frame (a b tiles lane) (ht : 0 < tiles) (hb : tiles ≤ 2^28) (name : String)
    (hx : name ∉ ["%phase0","%phase1","%even","%waitbar","%ad","%bd","%parity","%ready",
      "%next","%more","%nextbar","%copya","%copyb","%ay","%slot","%tile","%d0","%d1","%d2","%d3"]) :
    lookup name (dataCheckpoint a b tiles lane tiles).1.base.scalar.core.thread.regs =
      lookup name (initialLoopState tiles lane (HopperStage.leader lane)).base.scalar.core.thread.regs := by
  exact loopCheckpoint_control_frame (ctx tiles lane) (dataOracle a b tiles lane) 0 tiles (HopperStage.leader lane) zeroRetries
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) 4096 4224
    rfl rfl rfl (Nat.le_refl 0) (initial_loop_registers tiles lane _ hb) (initial_loop_accumulators tiles lane _) ht tiles (by omega) name hx

theorem data_loop_output_registers (a b tiles lane) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    OutputRegisters (dataCheckpoint a b tiles lane tiles).1 lane (HopperStage.leader lane) := by
  unfold OutputRegisters
  rw [data_loop_control_frame a b tiles lane ht hb "%x" (by decide),
    data_loop_control_frame a b tiles lane ht hb "%y" (by decide),data_loop_control_frame a b tiles lane ht hb "%z" (by decide),
    data_loop_control_frame a b tiles lane ht hb "%out" (by decide),data_loop_control_frame a b tiles lane ht hb "%leader" (by decide),
    data_loop_control_frame a b tiles lane ht hb "%bar0" (by decide),data_loop_control_frame a b tiles lane ht hb "%bar1" (by decide)]
  cases he : HopperStage.leader lane <;> simp [initialLoopState,initialLoopRegs,entryRegs,lookup,he]

def dataPreOutputState (a : TileA) (b : TileB) (tiles : Nat) (lane : Wgmma.Lane) : Wgmma.State :=
  if tiles = 0 then guardedInitialState 0 lane (HopperStage.leader lane) true else (dataCheckpoint a b tiles lane tiles).1

def dataPreOutputEvents (a : TileA) (b : TileB) (tiles : Nat) (lane : Wgmma.Lane) : List Wgmma.Event :=
  if tiles = 0 then initializationEvents (HopperStage.leader lane) else dataKernelLoopEvents a b tiles lane

theorem data_zero_tiles_source (a b lane) :
    Wgmma.run (ctx 0 lane) (dataOracle a b 0 lane) code (zeroTileSteps lane) {} =
      .ok (guardedInitialState 0 lane (HopperStage.leader lane) true,initializationEvents (HopperStage.leader lane)) := by
  rw [zeroTileSteps,Wgmma.run_add,Wgmma.run_add,entry_any_reply]
  simp only [Except.bind,initialize_any_reply,guard_any_reply 0 lane _ _ (by decide),decide_true,List.nil_append,List.append_nil]

theorem data_pre_output_source (a b tiles lane) (hb : tiles ≤ 2^28) :
    Wgmma.run (ctx tiles lane) (dataOracle a b tiles lane) code (preOutputSteps tiles lane) {} =
      .ok (dataPreOutputState a b tiles lane,dataPreOutputEvents a b tiles lane) := by
  by_cases ht : tiles = 0
  · subst tiles
    exact data_zero_tiles_source a b lane
  · simpa [preOutputSteps,dataPreOutputState,dataPreOutputEvents,ht] using data_kernel_loop_run a b tiles lane (Nat.pos_of_ne_zero ht) hb

theorem data_pre_output_ready (a b tiles lane) (hb : tiles ≤ 2^28) :
    (dataPreOutputState a b tiles lane).base.scalar.core.thread.status = .running ∧
    (dataPreOutputState a b tiles lane).base.scalar.core.thread.pc = 85 ∧
    Wgmma.pending (dataPreOutputState a b tiles lane).ledger = [] ∧
    OutputRegisters (dataPreOutputState a b tiles lane) lane (HopperStage.leader lane) ∧
    Accumulators (dataPreOutputState a b tiles lane) (fun slot => result a b tiles (Wgmma.cCoord (lane,slot))) := by
  by_cases ht : tiles = 0
  · subst tiles
    exact ⟨rfl,rfl,rfl,zero_output_registers lane,zero_output_accumulators lane⟩
  · have hr := data_loop_ready a b tiles lane tiles (Nat.pos_of_ne_zero ht) hb (Nat.le_refl _)
    refine ⟨?_,?_,?_,?_,?_⟩
    · simpa only [dataPreOutputState,ht,ite_false] using hr.1
    · simpa only [dataPreOutputState,ht,ite_false,lt_self_iff_false] using hr.2.1
    · simpa only [dataPreOutputState,ht,ite_false] using hr.2.2.1
    · simpa only [dataPreOutputState,ht,ite_false] using data_loop_output_registers a b tiles lane (Nat.pos_of_ne_zero ht) hb
    · simpa only [dataPreOutputState,ht,ite_false] using data_loop_accumulators a b tiles lane tiles (Nat.pos_of_ne_zero ht) hb (Nat.le_refl _)

def dataCompleteState (a : TileA) (b : TileB) (tiles : Nat) (lane : Wgmma.Lane) : Wgmma.State :=
  outputState (dataPreOutputState a b tiles lane) lane (HopperStage.leader lane)
def dataCompleteEvents (a : TileA) (b : TileB) (tiles : Nat) (lane : Wgmma.Lane) : List Wgmma.Event :=
  dataPreOutputEvents a b tiles lane++outputEvents (ctx tiles lane) (dataPreOutputState a b tiles lane) lane
    (HopperStage.leader lane) (fun slot => result a b tiles (Wgmma.cCoord (lane,slot)))

theorem data_complete_run (a b tiles lane) (hb : tiles ≤ 2^28) :
    Wgmma.run (ctx tiles lane) (dataOracle a b tiles lane) code (completeSteps tiles lane) {} =
      .ok (dataCompleteState a b tiles lane,dataCompleteEvents a b tiles lane) := by
  obtain ⟨hr,hpc,hp,hregs,hacc⟩ := data_pre_output_ready a b tiles lane hb
  obtain ⟨hx,hy,hz,ho,hl,hb0,hb1⟩ := hregs
  have hout := output_execute (ctx tiles lane) (dataOracle a b tiles lane) (dataPreOutputState a b tiles lane) lane
    (HopperStage.leader lane) (fun slot => result a b tiles (Wgmma.cCoord (lane,slot))) hr hpc hp hx hy hz ho hl hb0 hb1 hacc
  rw [completeSteps,Wgmma.run_add,data_pre_output_source a b tiles lane hb]
  simp only [Except.bind,hout,dataCompleteState,dataCompleteEvents]

theorem data_complete_local (a b tiles lane) (hb : tiles ≤ 2^28) : Wgmma.Complete (dataCompleteState a b tiles lane) :=
  outputState_complete _ _ _ (data_pre_output_ready a b tiles lane hb).2.2.1

def dataCompleteTrace (a : TileA) (b : TileB) (tiles : Nat) (lane : Wgmma.Lane) : Unified.ThreadTrace := {
  id := (ctx tiles lane).id,oracle := dataOracle a b tiles lane,count := completeSteps tiles lane,
  final := dataCompleteState a b tiles lane,events := dataCompleteEvents a b tiles lane
}
def dataCompleteCandidate (a : TileA) (b : TileB) (tiles : Nat) : Unified.Candidate := ⟨List.ofFn (dataCompleteTrace a b tiles)⟩

theorem data_source_produced (a b tiles lane) (hb : tiles ≤ 2^28) :
    Unified.Produced code (params tiles) HopperStage.block (dataCompleteTrace a b tiles lane) := data_complete_run a b tiles lane hb

theorem data_candidate_local (a b tiles) (hb : tiles ≤ 2^28) : Unified.Complete (dataCompleteCandidate a b tiles) := by
  intro trace ht
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
  exact data_complete_local a b tiles lane hb

theorem data_source_ids_unique (a b tiles) : ((dataCompleteCandidate a b tiles).traces.map Unified.ThreadTrace.id).Nodup := by
  simpa only [dataCompleteCandidate,List.map_ofFn,Function.comp_def,dataCompleteTrace,ctx] using
    (show (List.ofFn (fun lane : Wgmma.Lane => (HopperStage.ctx lane).id)).Nodup from by decide)

theorem data_source_well_formed (a b tiles) (initial : Location → Symbolic.Byte) (hb : tiles ≤ 2^28) :
    Unified.WellFormed code (completeLaunch tiles initial) (dataCompleteCandidate a b tiles) := by
  refine ⟨by simp [completeLaunch,HopperStage.geometry,HopperStage.block,Geometry.Valid,Dim3.Positive,Dim3.one],data_source_ids_unique a b tiles,?_,?_⟩
  · intro trace ht
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
    exact ⟨HopperStage.ctx_valid lane,data_source_produced a b tiles lane hb⟩
  · intro id hi
    obtain ⟨lane,he⟩ := HopperStage.ctx_covered hi
    exact ⟨dataCompleteTrace a b tiles lane,List.mem_ofFn.mpr ⟨lane,rfl⟩,he⟩

theorem data_pre_output_no_global_write (a b tiles lane) : (dataPreOutputEvents a b tiles lane).filterMap globalWrite = [] := by
  by_cases ht : tiles = 0
  · simp only [dataPreOutputEvents,ht,ite_true,initialization_no_global_write]
  · simp only [dataPreOutputEvents,ht,ite_false,dataKernelLoopEvents,dataLoopEvents,List.filterMap_append,
      initialization_no_global_write,loop_no_global_write,List.append_nil,List.nil_append]
    cases HopperStage.leader lane <;> rfl

theorem data_complete_write_specification (a b tiles lane) :
    (dataCompleteEvents a b tiles lane).filterMap globalWrite = List.ofFn (fun i : Fin 4 =>
      (8192+4*(8*(Wgmma.cCoord (lane,i)).1.val+(Wgmma.cCoord (lane,i)).2.val),
       Symbolic.encode .f32 (specification a b tiles (Wgmma.cCoord (lane,i))))) := by
  simp only [dataCompleteEvents,outputEvents,List.filterMap_append,data_pre_output_no_global_write,
    return_no_global_write,List.nil_append,List.append_nil,output_write_inventory]
  congr 1
  funext i
  rw [output_write_address,result_matches_specification]

theorem data_complete_write_matmul (a b tiles lane) :
    (dataCompleteEvents (tileA a) (tileB b) tiles lane).filterMap globalWrite = List.ofFn (fun i : Fin 4 =>
      (8192+4*(8*(Wgmma.cCoord (lane,i)).1.val+(Wgmma.cCoord (lane,i)).2.val),
       Symbolic.encode .f32 (matmul a b tiles (Wgmma.cCoord (lane,i))))) := by
  rw [data_complete_write_specification]
  congr 1
  funext i
  rw [specification_is_matmul]

end
end Ptx.Kernels.HopperDoubleBuffer
