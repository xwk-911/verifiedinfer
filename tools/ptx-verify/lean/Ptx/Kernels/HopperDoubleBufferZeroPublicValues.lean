import Ptx.Kernels.HopperDoubleBufferZeroValues
import Ptx.Iris.ByteContentsPreparationExecution
import Ptx.Iris.ByteContentsImmutable

/-! The minimal two-region zero-K native client from no loans through actual
output/resource source actions, checked completion and acquire. No descriptor
or input reservation is fabricated. Protocol buffers remain scalar metadata,
and full-source native adequacy retains the existing whole-map baseline.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

def zeroValuePrepared (values : List Nat) :=
  (Ptx.Async.run (Ptx.Async.initial 1 values) (KernelLease.prepareActions kernelReservations)).toOption.getD (Ptx.Async.initial 1 values)
def zeroValueReturned (values : List Nat) :=
  (Ptx.Async.run (zeroValuePrepared values) (KernelLease.returnActions kernelReservations)).toOption.getD (zeroValuePrepared values)
def zeroValueProtocolContext (candidate : Unified.Candidate) : ByteContentsProtocolHeap.Context :=
  ⟨zeroValueContext candidate,dataCluster,KernelLease.plan 2⟩
def zeroValuePreparationContext (candidate : Unified.Candidate) : ByteContentsPreparation.Context :=
  ⟨zeroValueProtocolContext candidate,KernelLease.commands kernelReservations,0⟩
def zeroValuePreparationActions := ByteContentsPreparation.requests (KernelLease.requests kernelReservations) ++ [.seal]
def zeroValueExecutionActions (actions : List ByteContentsHeap.Action) :=
  ByteContentsProtocolHeap.sourceActions actions ++ ByteContentsProtocolHeap.protocolActions (KernelLease.returnCommands kernelReservations)
def zeroValuePublicActions (actions : List ByteContentsHeap.Action) :=
  zeroValuePreparationActions ++ ByteContentsPreparation.execution (zeroValueExecutionActions actions)

theorem zero_value_preparation_succeeds (values : List Nat) (hv : values.length = 2) :
    Ptx.Async.run (Ptx.Async.initial 1 values) (KernelLease.prepareActions kernelReservations) = .ok (zeroValuePrepared values) := by
  obtain ⟨state,hs,_⟩ := KernelLease.preparation_exists values kernelReservations (kernel_reservations_valid values hv)
  simp only [zeroValuePrepared,hs,Except.toOption,Option.getD_some]

theorem zero_value_preparation_properties (values : List Nat) (hv : values.length = 2) :
    Ptx.Async.Preparation.Ready (zeroValuePrepared values) (KernelLease.commands kernelReservations) ∧
      Ptx.Async.Invariant (zeroValuePrepared values) ∧ Ptx.Async.getEvent (zeroValuePrepared values) 0 = .ok ⟨0,2⟩ :=
  KernelLease.preparation_properties (kernel_reservations_valid values hv) (zero_value_preparation_succeeds values hv)

theorem zero_value_return_succeeds (values : List Nat) (hv : values.length = 2) :
    Ptx.Async.run (zeroValuePrepared values) (KernelLease.returnActions kernelReservations) = .ok (zeroValueReturned values) ∧
      Ptx.Async.Drain.Returned (zeroValueReturned values) ∧ Ptx.Async.Preparation.Live (zeroValueReturned values) ∧
      (zeroValueReturned values).buffers.length = 2 := by
  have hp := zero_value_preparation_properties values hv
  obtain ⟨final,hr,hrtn,hlive,hlen,_⟩ := Ptx.Async.Drain.drain_and_acquire hp.1 hp.2.1
    (Ptx.Async.Drain.requests_plain (KernelLease.requests kernelReservations)) hp.2.2
  have hr' : Ptx.Async.run (zeroValuePrepared values) (KernelLease.returnActions kernelReservations) = .ok final := by
    simpa only [KernelLease.returnActions,KernelLease.commands,KernelLease.requests,List.length_map] using hr
  have he : zeroValueReturned values = final := by simp only [zeroValueReturned,hr',Except.toOption,Option.getD_some]
  rw [he]
  refine ⟨hr',hrtn,hlive,?_⟩
  have hpLen := Ptx.Async.steps_buffers_length (Ptx.Async.run_sound (zero_value_preparation_succeeds values hv))
  simpa only [Ptx.Async.initial,List.length_map,hv] using hlen.trans hpLen

theorem zero_value_native_preparation (candidate : Unified.Candidate) (initial : Location → Symbolic.Byte) (values : List Nat) (hv : values.length = 2) :
    IrisExecution.run (ByteContentsPreparation.transition (zeroValuePreparationContext candidate)) zeroValuePreparationActions
      (zeroValueInitialState candidate initial (Ptx.Async.initial 1 values)) = .ok (zeroValueInitialState candidate initial (zeroValuePrepared values)) ∧
      ByteContentsPreparation.Enabled (zeroValuePreparationContext candidate) (zeroValueInitialState candidate initial (zeroValuePrepared values)) := by
  let ctx := zeroValuePreparationContext candidate
  let state := zeroValueInitialState candidate initial (Ptx.Async.initial 1 values)
  have hp : ByteContentsPreparation.CanPrepare ctx state :=
    ⟨⟨fun _ h => h,ByteContentsHeap.initial_cells_available _ _ _⟩,rfl⟩
  obtain ⟨next,hrun,hen,hcells,hcut,hpublic⟩ := ByteContentsPreparation.prepare_run ctx (KernelLease.requests kernelReservations) state hp
    (Ptx.Async.Preparation.ready_initial values) (by
      intro request hm
      simp only [KernelLease.requests,kernelReservations,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl <;> simp [state,zeroValueInitialState,Ptx.Async.initial,Ptx.Async.Preparation.Request.Valid,hv]) rfl
  change Ptx.Async.run (Ptx.Async.initial 1 values) (KernelLease.prepareActions kernelReservations) = .ok next.coupled.protocol at hpublic
  have he : next.coupled.protocol = zeroValuePrepared values := Except.ok.inj (hpublic.symm.trans (zero_value_preparation_succeeds values hv))
  have hn : next = zeroValueInitialState candidate initial (zeroValuePrepared values) := by
    cases next with
    | mk coupled cells =>
      cases coupled with
      | mk protocol done =>
        change protocol = zeroValuePrepared values at he
        change done = (fun _ => False) at hcut
        change cells = ByteContents.initialCells zeroValueLocations initial at hcells
        cases he
        cases hcut
        cases hcells
        rfl
  rw [hn] at hrun hen
  exact ⟨hrun,hen⟩

theorem zero_value_public_output_of_run {initial candidate values actions next}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    (hr : IrisExecution.run (ByteContentsPreparation.transition (zeroValuePreparationContext candidate)) actions
      (zeroValueInitialState candidate initial (Ptx.Async.initial 1 values)) = .ok next)
    (hcut : next.coupled.done = Present candidate) (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    ByteContents.valueAt next ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = some (.realPart .f32 0 index.val) := by
  apply zero_value_output_of_unique_writes hw hc _ hcut lane slot index
  exact ByteContentsPreparation.unique_writes_run (zeroValuePreparationContext candidate) actions
    (ByteContentsHeap.unique_writes_initial (by intro _ h; exact h)) hr

theorem zero_value_public_frame_of_run {initial candidate values actions next loc}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    (hr : IrisExecution.run (ByteContentsPreparation.transition (zeroValuePreparationContext candidate)) actions
      (zeroValueInitialState candidate initial (Ptx.Async.initial 1 values)) = .ok next)
    (hout : ¬outputStorageRegion.Contains loc) :
    ByteContents.valueAt next loc = ByteContents.valueAt (zeroValueInitialState candidate initial (Ptx.Async.initial 1 values)) loc := by
  apply ByteContentsPreparation.immutable_value_run (zeroValuePreparationContext candidate) actions loc _ hr
  intro memory
  change ByteContents.writeByte candidate memory loc = none
  cases he : ByteContents.writeByte candidate memory loc with
  | none => rfl
  | some value => exact (hout (zero_value_write_in_output hw hc he)).elim

theorem zero_value_public_witness {initial candidate} (values : List Nat) (hv : values.length = 2)
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    ∃ actions final,
      IrisExecution.run (ByteContentsPreparation.transition (zeroValuePreparationContext candidate)) (zeroValuePublicActions actions)
        (zeroValueInitialState candidate initial (Ptx.Async.initial 1 values)) = .ok final ∧
      final.coupled = ⟨zeroValueReturned values,Present candidate⟩ ∧ ByteContentsHeap.Available final ∧
      Ptx.Async.Drain.Returned final.coupled.protocol ∧ Ptx.Async.Preparation.Live final.coupled.protocol ∧
      (∀ (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4), ByteContents.valueAt final ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = some (.realPart .f32 0 index.val)) ∧
      (∀ bid, bid < 2 → (∃ next, Ptx.Async.reclaim final.coupled.protocol bid = .ok next) ∧
        ∀ value, ∃ next, Ptx.Async.hostWrite final.coupled.protocol bid value = .ok next) ∧
      adequate .NotStuck (ByteContentsPreparation.script (zeroValuePreparationContext candidate) (zeroValuePublicActions actions))
        (zeroValueInitialState candidate initial (Ptx.Async.initial 1 values)) (fun result _ => result = .ok final) := by
  obtain ⟨hprep,hen⟩ := zero_value_native_preparation candidate initial values hv
  obtain ⟨actions,mid,hs,hcut,hprotocol,ha,_,hm,_⟩ := zero_value_source_witness (zeroValuePrepared values) hw hc
  have hcompleted : Bridge.AllCompleted Tma.localShared candidate zeroHistories dataCluster (KernelLease.plan 2) mid.coupled.done := by
    rw [hcut]
    intro ticket work hm
    unfold KernelLease.plan at hm
    split at hm
    · cases hm; exact .kernel hc (fun _ h => h)
    · cases hm
  have hprops := zero_value_return_succeeds values hv
  have hreturn : Ptx.Async.run mid.coupled.protocol ((KernelLease.returnCommands kernelReservations).map Bridge.Command.action) = .ok (zeroValueReturned values) := by
    rw [hprotocol]
    simpa [KernelLease.returnCommands,KernelLease.returnActions,Bridge.Command.action,Bridge.HostAction.action] using hprops.1
  let final := ByteContents.withCoupled mid ⟨zeroValueReturned values,mid.coupled.done⟩
  have hprotocolRun : IrisExecution.run (ByteContentsProtocolHeap.transition (zeroValueProtocolContext candidate)) (zeroValueExecutionActions actions)
      (zeroValueInitialState candidate initial (zeroValuePrepared values)) = .ok final :=
    ByteContentsProtocolHeap.source_protocol_run _ actions _ hs hcompleted hreturn
  have hexec := (ByteContentsPreparation.execution_run (zeroValuePreparationContext candidate) (zeroValueExecutionActions actions) hen hprotocolRun).1
  have hrun : IrisExecution.run (ByteContentsPreparation.transition (zeroValuePreparationContext candidate)) (zeroValuePublicActions actions)
      (zeroValueInitialState candidate initial (Ptx.Async.initial 1 values)) = .ok final := by
    rw [zeroValuePublicActions,IrisExecution.run_append,hprep]
    exact hexec
  refine ⟨actions,final,hrun,congrArg₂ Bridge.State.mk rfl hcut,ha,hprops.2.1,hprops.2.2.1,hm,?_,ByteContentsPreparation.script_adequate _ _ _ _ hrun⟩
  intro bid hb
  have hbound : bid < (zeroValueReturned values).buffers.length := by rw [hprops.2.2.2]; exact hb
  exact ⟨Ptx.Async.Drain.returned_can_reclaim hprops.2.1 hprops.2.2.1 bid hbound,
    fun value => Ptx.Async.Drain.returned_can_write hprops.2.1 hprops.2.2.1 bid value hbound⟩

theorem zero_value_public_active_blocks_host {initial candidate} (values : List Nat) (hv : values.length = 2)
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    {actions state loc node mode target region}
    (hr : IrisExecution.run (ByteContentsPreparation.transition (zeroValuePreparationContext candidate))
      (zeroValuePreparationActions ++ ByteContentsPreparation.execution actions) (zeroValueInitialState candidate initial (Ptx.Async.initial 1 values)) = .ok state)
    (hheld : get? (ByteContents.erase state).bytes (ByteAuthority.key loc) = some (.held node mode))
    (hl : kernelStorageLayout target = some region) (hcontains : region.Contains loc) :
    ByteContentsPreparation.transition (zeroValuePreparationContext candidate) (.execute (.protocol (.host (.reclaim target)))) state = .error (.authority (.protocolFailure .outstandingLoan)) ∧
      ∀ value, ByteContentsPreparation.transition (zeroValuePreparationContext candidate) (.execute (.protocol (.host (.write target value)))) state = .error (.authority (.protocolFailure .outstandingLoan)) := by
  obtain ⟨hp,hen⟩ := zero_value_native_preparation candidate initial values hv
  rw [IrisExecution.run_append,hp] at hr
  have hr' : IrisExecution.run (ByteContentsPreparation.transition (zeroValuePreparationContext candidate)) (ByteContentsPreparation.execution actions)
      (zeroValueInitialState candidate initial (zeroValuePrepared values)) = .ok state := hr
  have hexec := ByteContentsPreparation.execution_projects _ actions hr'
  have he := (ByteContentsPreparation.execution_run _ actions hen hexec).2
  have hauth := ByteContentsProtocolHeap.run_projects _ actions hexec
  have hpool : ∀ k owner, get? (ByteContents.erase (zeroValueInitialState candidate initial (zeroValuePrepared values))).bytes k = some owner → owner = .available := by
    intro k owner hg
    change get? (Iris.Std.PartialMap.map ByteContents.Payload.owner _) k = some owner at hg
    rw [get?_map] at hg
    cases hx : get? (zeroValueInitialState candidate initial (zeroValuePrepared values)).cells k with
    | none => simp [hx] at hg
    | some payload =>
      have ho : payload.owner = owner := by simpa only [hx,Option.map_some,Option.some.injEq] using hg
      rw [← ho]
      exact ByteContents.initialCells_owner_available hx
  have hactive := ByteAuthority.steps_active (ByteAuthority.available_pool_active hpool) hauth
  obtain ⟨hu,hready⟩ := hactive loc node mode hheld
  have hg := zero_kernel_public_pending_rejected hv (zero_value_preparation_succeeds values hv) hw hc
    (ByteAuthority.steps_projects hauth) (zero_value_uses_are_kernel hw hc hu) hready.2.1 hl hcontains
  constructor
  · rw [ByteContentsPreparation.execution_step he]
    apply ByteContentsProtocolHeap.protocol_error
    exact ByteAuthority.execute_host_error hg.1
  · intro value
    rw [ByteContentsPreparation.execution_step he]
    apply ByteContentsProtocolHeap.protocol_error
    exact ByteAuthority.execute_host_error (hg.2 value)

end
end Ptx.Kernels.HopperDoubleBuffer
