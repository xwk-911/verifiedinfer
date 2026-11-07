import Ptx.Kernels.HopperDoubleBufferControlClock

/-! Actual CTA barrier generations through the repeated source execution.
Ordinary/TMA/native arithmetic preserves counters; only the CTA step changes
them. This does not prove convergence or global control consistency by itself. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev generations (s : Wgmma.State) := s.base.scalar.core.generations

theorem write_results_generations (calls : List Wgmma.Call) (s : Hopper.State) :
    (calls.foldl Wgmma.writeResult s).scalar.core.generations = s.scalar.core.generations := by
  induction calls generalizing s with
  | nil => rfl
  | cons call calls ih => rw [List.foldl_cons,ih]; rfl

theorem native_wait_generations (s : Wgmma.State) (keep reply : Nat) : generations (Wgmma.waitState s keep reply) = generations s := by
  exact write_results_generations _ s.base

theorem compute_generations (ctx oracle s pa pb values) : generations (computeState ctx oracle s pa pb values) = generations s := by
  rw [computeState,native_wait_generations]
  rfl

theorem selection_generations (s : Wgmma.State) (tile) : generations (selectionState s tile) = generations s := by
  unfold selectionState
  split_ifs <;> rfl

theorem tested_generations (s : Wgmma.State) (answer) : generations (testedState s answer) = generations s := rfl

theorem retry_generations (s : Wgmma.State) (retries) : generations (retryState retries s) = generations s := by
  induction retries with
  | zero => rfl
  | succ n ih => rw [retryState,tested_generations,ih]

theorem phase_generations (s : Wgmma.State) (tile) : generations (phaseState s tile) = generations s := by
  unfold phaseState
  split_ifs <;> rfl

theorem header_generations (s : Wgmma.State) (tile retries) : generations (headerState s tile retries) = generations s := by
  rw [headerState,phase_generations,tested_generations,retry_generations,selection_generations]

theorem prefetch_guard_generations (s : Wgmma.State) (tile tiles leader) : generations (prefetchGuardState s tile tiles leader) = generations s := by
  unfold prefetchGuardState
  split_ifs <;> rfl

theorem prefetch_generations (s : Wgmma.State) (tile next) : generations (prefetchState s tile next) = generations s := by
  unfold prefetchState prefetchAddressState prefetchSelected
  split_ifs <;> rfl

theorem prelude_generations (s : Wgmma.State) (tile tiles leader) : generations (preludeState s tile tiles leader) = generations s := by
  unfold preludeState
  split_ifs <;> simp only [prefetch_generations,prefetch_guard_generations]

theorem prepared_generations (s : Wgmma.State) (tile tiles retries leader) : generations (preparedState s tile tiles retries leader) = generations s := by
  rw [preparedState,prelude_generations,header_generations]

theorem iteration_generations (ctx oracle s tile tiles retries leader values) :
    generations (iterationState ctx oracle s tile tiles retries leader values) =
      (2,Ptx.Event.generation s.base.scalar.core 2+1)::(generations s).filter (fun kv => kv.1 != 2) := by
  change generations (Wgmma.barrierState (computeState ctx oracle (preparedState s tile tiles retries leader)
    (aDescriptor (stage tile)) (bDescriptor (stage tile)) values) 2) = _
  change (2,Ptx.Event.generation (computeState ctx oracle (preparedState s tile tiles retries leader)
    (aDescriptor (stage tile)) (bDescriptor (stage tile)) values).base.scalar.core 2+1)::
    (generations (computeState ctx oracle (preparedState s tile tiles retries leader) (aDescriptor (stage tile)) (bDescriptor (stage tile)) values)).filter _ = _
  simp only [Ptx.Event.generation,compute_generations,prepared_generations]

def loopGenerations (n : Nat) : List (Nat × Nat) := if n = 0 then [(0,1)] else [(2,n),(0,1)]

theorem data_checkpoint_generations (a b tiles lane n) : generations (dataCheckpoint a b tiles lane n).1 = loopGenerations n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : generations (dataCheckpoint a b tiles lane (n+1)).1 =
        (2,Ptx.Event.generation (dataCheckpoint a b tiles lane n).1.base.scalar.core 2+1)::
          (generations (dataCheckpoint a b tiles lane n).1).filter (fun kv => kv.1 != 2) := by
      simp only [dataCheckpoint,loopCheckpoint,Nat.zero_add,zeroRetries,iteration_generations]
    rw [he]
    change (2,(((generations (dataCheckpoint a b tiles lane n).1).find? (fun kv => kv.1 == 2)).map Prod.snd).getD 0+1)::
      (generations (dataCheckpoint a b tiles lane n).1).filter (fun kv => kv.1 != 2) = _
    rw [ih]
    cases n <;> simp [loopGenerations]

theorem data_prepared_generation_two (a b tiles lane tile) :
    Ptx.Event.generation (computeState (ctx tiles lane) (dataOracle a b tiles lane)
      (preparedState (dataCheckpoint a b tiles lane tile).1 tile tiles 0 (HopperStage.leader lane))
      (aDescriptor (stage tile)) (bDescriptor (stage tile)) (dataCheckpoint a b tiles lane tile).2).base.scalar.core 2 = tile := by
  simp only [Ptx.Event.generation,compute_generations,prepared_generations,data_checkpoint_generations]
  cases tile <;> simp [loopGenerations]

theorem data_pre_output_generation_one (a b tiles lane) :
    Ptx.Event.generation (dataPreOutputState a b tiles lane).base.scalar.core 1 = 0 := by
  by_cases hz : tiles = 0
  · subst tiles
    rfl
  · simp only [dataPreOutputState,hz,ite_false,Ptx.Event.generation,data_checkpoint_generations,loopGenerations]
    simp [hz]

theorem output_generations (s : Wgmma.State) (lane : Wgmma.Lane) :
    generations (outputStored (outputAddressState s lane)) = generations s := rfl

theorem data_return_generation_one (a b tiles lane) :
    Ptx.Event.generation (outputStored (outputAddressState (dataPreOutputState a b tiles lane) lane)).base.scalar.core 1 = 0 := by
  simpa only [Ptx.Event.generation,output_generations] using data_pre_output_generation_one a b tiles lane

end
end Ptx.Kernels.HopperDoubleBuffer
