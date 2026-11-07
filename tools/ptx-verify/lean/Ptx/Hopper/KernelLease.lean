import Ptx.Hopper.KernelUse
import Ptx.Hopper.ProtocolScript

/-! Public construction and return of conservative whole-kernel lifetime
reservations. Exact modes and separated modeled regions are checked explicitly.
This adapter connects ordinary/resource uses to the existing coupled prefix
semantics; it does not equate abstract scalar cells with physical tensor bytes.
-/
namespace Ptx.Hopper.Progress.KernelLease
open Ptx.ISA
noncomputable section

structure Reservation where
  buffer : Nat
  mode : Ptx.Async.Mode
  region : Regions.Region
  deriving Repr, DecidableEq

def requests (resources : List Reservation) : List Ptx.Async.Preparation.Request :=
  resources.map (fun resource => .access resource.buffer resource.mode)
def commands (resources : List Reservation) := (requests resources).map Ptx.Async.Preparation.Request.command
def prepareActions (resources : List Reservation) := (requests resources).map Ptx.Async.Preparation.Request.action ++ [.record 0 0]
def returnActions (resources : List Reservation) : List Ptx.Async.Action :=
  List.replicate resources.length (.device 0) ++ [.acquire 0]
def returnCommands (resources : List Reservation) : List Bridge.Command :=
  List.replicate resources.length (.device 0) ++ [.host (.acquire 0)]
def plan (count : Nat) : Bridge.Plan := fun ticket =>
  if ticket.stream = 0 ∧ 0 < ticket.seq ∧ ticket.seq ≤ count then some .kernel else none

def binding (resources : List Reservation) (index : Fin resources.length) : Regions.Binding :=
  ⟨.kernel,⟨0,index.val+1⟩,(resources[index]).buffer,(resources[index]).mode,(resources[index]).region⟩
def bindings (resources : List Reservation) : List Regions.Binding := List.ofFn (binding resources)
def Valid (values : List Nat) (resources : List Reservation) : Prop :=
  ∀ resource ∈ resources, resource.buffer < values.length

def Covers (resolve : Tma.SharedResolver) (candidate : Unified.Candidate) (resources : List Reservation) : Prop :=
  ∀ control loc mode, KernelUse resolve candidate control loc mode →
    ∃ index : Fin resources.length, (resources[index]).mode = mode ∧ (resources[index]).region.Contains loc

def Mapped (layout : Regions.Layout) (resources : List Reservation) : Prop :=
  ∀ resource ∈ resources, layout resource.buffer = some resource.region

theorem binding_mapped (resources : List Reservation) (index : Fin resources.length) :
    plan resources.length (binding resources index).ticket = some .kernel := by
  simp [plan,binding]

theorem preparation_exists (values : List Nat) (resources : List Reservation) (hv : Valid values resources) :
    ∃ prepared, Ptx.Async.run (Ptx.Async.initial 1 values) (prepareActions resources) = .ok prepared ∧
      Ptx.Async.Preparation.Ready prepared (commands resources) ∧ Ptx.Async.Invariant prepared ∧
      Ptx.Async.getEvent prepared 0 = .ok ⟨0,resources.length⟩ := by
  obtain ⟨state,hs,hr,_,he⟩ := Ptx.Async.Preparation.ready_requests (Ptx.Async.Preparation.ready_initial values) (requests resources)
    (by
      intro request hm
      change request ∈ resources.map (fun resource => Ptx.Async.Preparation.Request.access resource.buffer resource.mode) at hm
      obtain ⟨resource,hmem,heq⟩ := (List.mem_map.mp hm : ∃ resource : Reservation, resource ∈ resources ∧
        Ptx.Async.Preparation.Request.access resource.buffer resource.mode = request)
      subst request
      simpa [Ptx.Async.Preparation.Request.Valid,Ptx.Async.initial] using hv resource hmem)
  have hready : Ptx.Async.Preparation.Ready state (commands resources) := by simpa [commands] using hr
  let prepared : Ptx.Async.State := {state with events := ⟨0,⟨0,(commands resources).length⟩⟩::state.events}
  have hrecord : Ptx.Async.step state (.record 0 0) = .ok prepared :=
    Ptx.Async.Preparation.ready_record hready (by simp [he,Ptx.Async.initial])
  have hp : Ptx.Async.run (Ptx.Async.initial 1 values) (prepareActions resources) = .ok prepared := by
    simp only [prepareActions,Ptx.Async.Client.run_append,hs,Except.bind,Ptx.Async.run,hrecord]
  refine ⟨prepared,hp,hready,Ptx.Async.steps_invariant (Ptx.Async.initial_invariant 1 values) (Ptx.Async.run_sound hp),?_⟩
  simp [Ptx.Async.getEvent,prepared,commands,requests,bind,Except.bind,pure,Except.pure]

theorem preparation_properties {values resources prepared} (hv : Valid values resources)
    (hp : Ptx.Async.run (Ptx.Async.initial 1 values) (prepareActions resources) = .ok prepared) :
    Ptx.Async.Preparation.Ready prepared (commands resources) ∧ Ptx.Async.Invariant prepared ∧
      Ptx.Async.getEvent prepared 0 = .ok ⟨0,resources.length⟩ := by
  obtain ⟨actual,ha,hr,hi,he⟩ := preparation_exists values resources hv
  have heq : actual = prepared := Except.ok.inj (ha.symm.trans hp)
  subst actual
  exact ⟨hr,hi,he⟩

theorem prepared_bindings_borrowed {resources prepared}
    (hr : Ptx.Async.Preparation.Ready prepared (commands resources)) (hi : Ptx.Async.Invariant prepared) :
    Regions.Borrowed (bindings resources) prepared := by
  intro actual hm _
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp hm
  let st : Ptx.Async.Stream := ⟨(commands resources).length,0,commands resources,[]⟩
  have hstream : prepared.streams[0]? = some st := by simp [hr.1,st]
  have hcmd : st.queue[index.val]? = some (.access (resources[index]).buffer (resources[index]).mode) := by
    simp [st,commands,requests,Ptx.Async.Preparation.Request.command]
  simpa [binding,st] using hi.pending 0 st hstream index.val _ hcmd _ _ (.accessMode ..)

theorem prepared_faithful {resources prepared resolve candidate histories cluster}
    (hr : Ptx.Async.Preparation.Ready prepared (commands resources)) :
    Bridge.Faithful resolve candidate histories cluster (plan resources.length) ⟨prepared,fun _ => False⟩ := by
  apply Bridge.prepared_faithful
  · intro sid stream hg
    rw [hr.1] at hg
    cases sid with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at hg; subst stream; rfl
    | succ sid => simp at hg
  · intro ticket work hm
    simp only [plan] at hm
    split at hm
    · rename_i hg; exact hg.2.1
    · cases hm

theorem pending_region_reclaim_write_rejected {resources prepared block resolve candidate histories cluster state layout bid region control loc mode}
    (hr : Ptx.Async.Preparation.Ready prepared (commands resources)) (hi : Ptx.Async.Invariant prepared)
    (hs : Bridge.Steps block resolve candidate histories cluster (plan resources.length) ⟨prepared,fun _ => False⟩ state)
    (hm : Mapped layout resources) (hsep : Regions.Separated layout) (hcover : Covers resolve candidate resources)
    (hu : KernelUse resolve candidate control loc mode) (hp : ¬state.done control)
    (hl : layout bid = some region) (hc : region.Contains loc) :
    Ptx.Async.reclaim state.protocol bid = .error .outstandingLoan ∧
      ∀ value, Ptx.Async.hostWrite state.protocol bid value = .error .outstandingLoan := by
  obtain ⟨index,_,hcontains⟩ := hcover control loc mode hu
  have hregion := hm (resources[index]) (List.getElem_mem _)
  have hbid : (resources[index]).buffer = bid := by
    by_contra hne
    exact hsep _ _ _ _ hregion hl hne loc hcontains hc
  have hf := Bridge.steps_faithful (prepared_faithful hr) hs
  have hn : Ptx.Async.complete state.protocol (binding resources index).ticket ≠ true :=
    fun hcomplete => pending_kernel_use_not_completed hu hp (hf _ _ (binding_mapped resources index) hcomplete)
  have hb := Regions.borrowed_steps (prepared_bindings_borrowed hr hi) hs
  have hh := hb (binding resources index) (List.mem_ofFn.mpr ⟨index,rfl⟩) hn
  have hheld : Ptx.Async.Holds state.protocol bid ⟨(binding resources index).ticket,(binding resources index).mode⟩ := by
    simpa only [binding,hbid] using hh
  exact ⟨Ptx.Async.reclaim_of_holds hheld,fun value => Ptx.Async.hostWrite_of_holds hheld⟩

theorem public_pending_region_reclaim_write_rejected {values resources prepared block resolve candidate histories cluster state layout bid region control loc mode}
    (hv : Valid values resources)
    (hprep : Ptx.Async.run (Ptx.Async.initial 1 values) (prepareActions resources) = .ok prepared)
    (hs : Bridge.Steps block resolve candidate histories cluster (plan resources.length) ⟨prepared,fun _ => False⟩ state)
    (hm : Mapped layout resources) (hsep : Regions.Separated layout) (hcover : Covers resolve candidate resources)
    (hu : KernelUse resolve candidate control loc mode) (hp : ¬state.done control)
    (hl : layout bid = some region) (hc : region.Contains loc) :
    Ptx.Async.reclaim state.protocol bid = .error .outstandingLoan ∧
      ∀ value, Ptx.Async.hostWrite state.protocol bid value = .error .outstandingLoan := by
  obtain ⟨hr,hi,_⟩ := preparation_properties hv hprep
  exact pending_region_reclaim_write_rejected hr hi hs hm hsep hcover hu hp hl hc

/-- Chosen finite actual-prefix execution followed by actual FIFO completion and
acquisition. Completion is guarded by the source, rather than assumed from the
abstract access task's scalar identity effect. -/
theorem coupled_return_exists (values : List Nat) (resources : List Reservation) (hv : Valid values resources)
    {block resolve candidate histories cluster} (hc : Unified.Complete candidate)
    (hp : Reached block candidate histories (Present candidate)) :
    ∃ prepared final,
      Ptx.Async.run (Ptx.Async.initial 1 values) (prepareActions resources) = .ok prepared ∧
      Regions.Borrowed (bindings resources) prepared ∧
      Bridge.Steps block resolve candidate histories cluster (plan resources.length)
        ⟨prepared,fun _ => False⟩ ⟨final,Present candidate⟩ ∧
      Ptx.Async.run prepared (returnActions resources) = .ok final ∧
      Ptx.Async.Drain.Returned final ∧ Ptx.Async.Preparation.Live final ∧ final.buffers.length = values.length := by
  obtain ⟨prepared,hr,hrdy,hi,he⟩ := preparation_exists values resources hv
  have hevent : Ptx.Async.getEvent prepared 0 = .ok ⟨0,(commands resources).length⟩ := by
    simpa only [commands,requests,List.length_map] using he
  obtain ⟨final,hret,hreturned,hlive,hlen,_⟩ := Ptx.Async.Drain.drain_and_acquire hrdy hi
    (Ptx.Async.Drain.requests_plain (requests resources)) hevent
  have hreturn : Ptx.Async.run prepared (returnActions resources) = .ok final := by
    simpa only [returnActions,commands,requests,List.length_map] using hret
  refine ⟨prepared,final,hr,prepared_bindings_borrowed hrdy hi,?_,hreturn,hreturned,hlive,?_⟩
  · apply Bridge.steps_trans (Bridge.prefix_execution prepared hp)
    apply Bridge.completed_script_execution (commands := returnCommands resources) _
    · simpa [returnCommands,returnActions,Bridge.Command.action,Bridge.HostAction.action] using hreturn
    · intro ticket work hm
      simp only [plan] at hm
      split at hm
      · cases hm; exact .kernel hc (fun _ h => h)
      · cases hm
  · have ha := Ptx.Async.steps_buffers_length (Ptx.Async.run_sound hr)
    simpa only [Ptx.Async.initial,List.length_map] using hlen.trans ha

end
end Ptx.Hopper.Progress.KernelLease
