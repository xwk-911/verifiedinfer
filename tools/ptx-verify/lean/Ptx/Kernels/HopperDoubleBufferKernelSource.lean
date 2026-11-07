import Ptx.Kernels.HopperDoubleBufferOutput

/-! Constructed full-source candidate for every lane and supported tile count,
including T=0. Arithmetic/byte replies represent zero input. Source production,
thread coverage and local completion are proved; resource, collective/tensor,
memory/observer admission and general-input correctness are not inferred. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def OutputRegisters (s : Wgmma.State) (lane : Wgmma.Lane) (leader : Bool) : Prop :=
  lookup "%x" s.base.scalar.core.thread.regs = some (HopperStage.xWord lane) ∧
  lookup "%y" s.base.scalar.core.thread.regs = some (HopperStage.yWord lane) ∧
  lookup "%z" s.base.scalar.core.thread.regs = some (HopperStage.zWord lane) ∧
  lookup "%out" s.base.scalar.core.thread.regs = some (wrap 64 8192) ∧
  lookup "%leader" s.base.scalar.core.thread.regs = some (if leader then 1 else 0) ∧
  lookup "%bar0" s.base.scalar.core.thread.regs = some 0 ∧
  lookup "%bar1" s.base.scalar.core.thread.regs = some 8

theorem kernel_loop_output_registers (tiles : Nat) (lane : Wgmma.Lane) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    OutputRegisters (kernelLoopState tiles lane) lane (HopperStage.leader lane) := by
  unfold OutputRegisters
  have hx := kernel_loop_control_frame tiles lane ht hb "%x" (by decide)
  have hy := kernel_loop_control_frame tiles lane ht hb "%y" (by decide)
  have hz := kernel_loop_control_frame tiles lane ht hb "%z" (by decide)
  have ho := kernel_loop_control_frame tiles lane ht hb "%out" (by decide)
  have hl := kernel_loop_control_frame tiles lane ht hb "%leader" (by decide)
  have hb0 := kernel_loop_control_frame tiles lane ht hb "%bar0" (by decide)
  have hb1 := kernel_loop_control_frame tiles lane ht hb "%bar1" (by decide)
  rw [hx,hy,hz,ho,hl,hb0,hb1]
  cases he : HopperStage.leader lane <;> simp [initialLoopState,initialLoopRegs,entryRegs,lookup,he]

theorem zero_output_registers (lane : Wgmma.Lane) :
    OutputRegisters (guardedInitialState 0 lane (HopperStage.leader lane) true) lane (HopperStage.leader lane) := by
  cases he : HopperStage.leader lane <;>
    simp [OutputRegisters,guardedInitialState,initializedState,entryRegs,lookup,he]

theorem zero_output_accumulators (lane : Wgmma.Lane) :
    Accumulators (guardedInitialState 0 lane (HopperStage.leader lane) true) (fun _ => 0) := by
  intro i
  have hfloat : declarationLookup (computeSlotName i) (initializedState 0 lane (HopperStage.leader lane)).base.scalar.floats = some (.f32,0) := by
    fin_cases i <;> simp [initializedState,computeSlotName,HopperStage.zeroFloats,HopperStage.zeroLiteral,Scalar.F32Literal.zero_value,declarationLookup]
  have hnat : lookup (computeSlotName i) (initializedState 0 lane (HopperStage.leader lane)).base.scalar.core.thread.regs = none := by
    fin_cases i <;> simp [initializedState,entryRegs,computeSlotName,lookup]
  have hdiff : computeSlotName i ≠ "%more" := by fin_cases i <;> decide
  constructor
  · rw [guardedInitialState,Wgmma.integerPC_float,Wgmma.integerAssign_float _ _ _ _ _ hdiff hnat]
    · exact hfloat
    · simp [hdiff,hnat]
  · simp [guardedInitialState,hdiff,hnat]

def preOutputState (tiles : Nat) (lane : Wgmma.Lane) : Wgmma.State :=
  if tiles = 0 then guardedInitialState 0 lane (HopperStage.leader lane) true else kernelLoopState tiles lane
def preOutputSteps (tiles : Nat) (lane : Wgmma.Lane) : Nat :=
  if tiles = 0 then zeroTileSteps lane else kernelLoopSteps tiles lane
def preOutputEvents (tiles : Nat) (lane : Wgmma.Lane) : List Wgmma.Event :=
  if tiles = 0 then initializationEvents (HopperStage.leader lane) else kernelLoopEvents tiles lane

theorem pre_output_source (tiles : Nat) (lane : Wgmma.Lane) (hb : tiles ≤ 2^28) :
    Wgmma.run (ctx tiles lane) (oracle tiles) code (preOutputSteps tiles lane) {} = .ok (preOutputState tiles lane,preOutputEvents tiles lane) := by
  by_cases ht : tiles = 0
  · subst tiles
    exact kernel_zero_tiles_source lane
  · simpa [preOutputSteps,preOutputState,preOutputEvents,ht] using kernel_loop_source tiles lane (Nat.pos_of_ne_zero ht) hb

theorem pre_output_ready (tiles : Nat) (lane : Wgmma.Lane) (hb : tiles ≤ 2^28) :
    (preOutputState tiles lane).base.scalar.core.thread.status = .running ∧
    (preOutputState tiles lane).base.scalar.core.thread.pc = 85 ∧
    Wgmma.pending (preOutputState tiles lane).ledger = [] ∧
    OutputRegisters (preOutputState tiles lane) lane (HopperStage.leader lane) ∧
    Accumulators (preOutputState tiles lane) (fun _ => 0) := by
  by_cases ht : tiles = 0
  · subst tiles
    exact ⟨rfl,rfl,rfl,zero_output_registers lane,zero_output_accumulators lane⟩
  · have hpos := Nat.pos_of_ne_zero ht
    simpa only [preOutputState,ht,ite_false] using
      And.intro (kernel_loop_status tiles lane hpos hb)
        (And.intro (kernel_loop_output tiles lane hpos hb).1
          (And.intro (kernel_loop_output tiles lane hpos hb).2
            (And.intro (kernel_loop_output_registers tiles lane hpos hb) (kernel_loop_zero_accumulators tiles lane hpos hb))))

def completeSteps (tiles : Nat) (lane : Wgmma.Lane) : Nat := preOutputSteps tiles lane+outputSteps (HopperStage.leader lane)
def completeState (tiles : Nat) (lane : Wgmma.Lane) : Wgmma.State := outputState (preOutputState tiles lane) lane (HopperStage.leader lane)
def completeEvents (tiles : Nat) (lane : Wgmma.Lane) : List Wgmma.Event :=
  preOutputEvents tiles lane++outputEvents (ctx tiles lane) (preOutputState tiles lane) lane (HopperStage.leader lane) (fun _ => 0)

theorem complete_source_run (tiles : Nat) (lane : Wgmma.Lane) (hb : tiles ≤ 2^28) :
    Wgmma.run (ctx tiles lane) (oracle tiles) code (completeSteps tiles lane) {} = .ok (completeState tiles lane,completeEvents tiles lane) := by
  obtain ⟨hr,hpc,hp,hregs,hacc⟩ := pre_output_ready tiles lane hb
  obtain ⟨hx,hy,hz,ho,hl,hb0,hb1⟩ := hregs
  have hout := output_execute (ctx tiles lane) (oracle tiles) (preOutputState tiles lane) lane (HopperStage.leader lane) (fun _ => 0)
    hr hpc hp hx hy hz ho hl hb0 hb1 hacc
  rw [completeSteps,Wgmma.run_add,pre_output_source tiles lane hb]
  simp only [Except.bind,hout,completeState,completeEvents]

theorem complete_source_status (tiles : Nat) (lane : Wgmma.Lane) (hb : tiles ≤ 2^28) :
    Wgmma.Complete (completeState tiles lane) :=
  outputState_complete _ _ _ (pre_output_ready tiles lane hb).2.2.1

def completeTrace (tiles : Nat) (lane : Wgmma.Lane) : Unified.ThreadTrace := {
  id := (ctx tiles lane).id,oracle := oracle tiles,count := completeSteps tiles lane,
  final := completeState tiles lane,events := completeEvents tiles lane
}
def completeCandidate (tiles : Nat) : Unified.Candidate := ⟨List.ofFn (completeTrace tiles)⟩
def completeLaunch (tiles : Nat) (initial : Location → Symbolic.Byte) : Scalar.Launch := ⟨HopperStage.geometry,params tiles,initial⟩

theorem complete_source_produced (tiles : Nat) (lane : Wgmma.Lane) (hb : tiles ≤ 2^28) :
    Unified.Produced code (params tiles) HopperStage.block (completeTrace tiles lane) := by
  exact complete_source_run tiles lane hb

theorem complete_candidate_local (tiles : Nat) (hb : tiles ≤ 2^28) : Unified.Complete (completeCandidate tiles) := by
  intro trace ht
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
  exact complete_source_status tiles lane hb

theorem complete_trace_ids_unique (tiles : Nat) :
    ((completeCandidate tiles).traces.map Unified.ThreadTrace.id).Nodup := by
  simpa only [completeCandidate,List.map_ofFn,Function.comp_def,completeTrace,ctx] using
    (show (List.ofFn (fun lane : Wgmma.Lane => (HopperStage.ctx lane).id)).Nodup from by decide)

theorem complete_source_well_formed (tiles : Nat) (initial : Location → Symbolic.Byte) (hb : tiles ≤ 2^28) :
    Unified.WellFormed code (completeLaunch tiles initial) (completeCandidate tiles) := by
  refine ⟨by simp [completeLaunch,HopperStage.geometry,HopperStage.block,Geometry.Valid,Dim3.Positive,Dim3.one],complete_trace_ids_unique tiles,?_,?_⟩
  · intro trace ht
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
    exact ⟨HopperStage.ctx_valid lane,complete_source_produced tiles lane hb⟩
  · intro id hi
    obtain ⟨lane,he⟩ := HopperStage.ctx_covered hi
    exact ⟨completeTrace tiles lane,List.mem_ofFn.mpr ⟨lane,rfl⟩,he⟩

theorem complete_source_located (tiles : Nat) (lane : Wgmma.Lane) (hb : tiles ≤ 2^28) :
    ∃ located, Wgmma.runLocated (ctx tiles lane) (oracle tiles) code (completeSteps tiles lane) {} = .ok (completeState tiles lane,located) ∧
      located.map SourceRun.Located.kind = completeEvents tiles lane :=
  Wgmma.run_located_exists (complete_source_run tiles lane hb)

end
end Ptx.Kernels.HopperDoubleBuffer
