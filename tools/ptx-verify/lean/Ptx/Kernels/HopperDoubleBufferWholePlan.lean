import Ptx.Kernels.HopperDoubleBufferKernelOwnership
import Ptx.Kernels.HopperDoubleBufferPreparedLoans
import Ptx.Kernels.HopperDoubleBufferAsyncCompletion

/-! One ten-region layout and one public queue for async TMA/native lifetimes
and ordinary/resource lifetimes. These are modeled regions and reservations;
physical allocation, command/value simulation and Iris byte ownership remain
separate obligations. The existing minimal zero-K client still uses two buffers.
-/
namespace Ptx.Kernels.HopperDoubleBuffer.Whole
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

def regions (tiles : Nat) := asyncRegions tiles ++ [outputStorageRegion,barrierStorageRegion]
def layout (tiles : Nat) : Regions.Layout := fun bid => (regions tiles)[bid]?
def requests (tiles : Nat) : List Ptx.Async.Preparation.Request :=
  (List.range tiles).flatMap tileRequests ++ [.access 8 .write,.access 9 .write]
def commands (tiles : Nat) := (requests tiles).map Ptx.Async.Preparation.Request.command
def prepareActions (tiles : Nat) := (requests tiles).map Ptx.Async.Preparation.Request.action ++ [.record 0 0]
def returnActions (tiles : Nat) : List Ptx.Async.Action := List.replicate (6*tiles+2) (.device 0) ++ [.acquire 0]
def returnCommands (tiles : Nat) : List Bridge.Command := List.replicate (6*tiles+2) (.device 0) ++ [.host (.acquire 0)]
def prepared (values : List Nat) (tiles : Nat) : Ptx.Async.State :=
  (Ptx.Async.run (Ptx.Async.initial 1 values) (prepareActions tiles)).toOption.getD (Ptx.Async.initial 1 values)
def returned (values : List Nat) (tiles : Nat) : Ptx.Async.State :=
  (Ptx.Async.run (prepared values tiles) (returnActions tiles)).toOption.getD (prepared values tiles)

def plan {tiles candidate} (family : ReplySourceFamily tiles candidate) : Bridge.Plan := fun ticket =>
  if ticket.seq ≤ 6*tiles then asyncPlan family ticket
  else if ticket.stream = 0 ∧ ticket.seq ≤ 6*tiles+2 then some .kernel else none

def rootBindings (tiles : Nat) : List Regions.Binding :=
  [⟨.kernel,⟨0,6*tiles+1⟩,8,.write,outputStorageRegion⟩,
    ⟨.kernel,⟨0,6*tiles+2⟩,9,.write,barrierStorageRegion⟩]
def bindings {tiles candidate} (family : ReplySourceFamily tiles candidate) := asyncBindings family ++ rootBindings tiles

theorem regions_separated (tiles : Nat) : Regions.Separated (layout tiles) := by
  apply Regions.separated_of_pairwise
  simp [regions,asyncRegions,List.pairwise_cons,Regions.Region.Disjoint,regionDescriptorA,regionDescriptorB,
    regionInputA,regionInputB,regionA,regionB,aBase,bBase,stage,dataBBase,outputStorageRegion,barrierStorageRegion]
  omega

theorem layout_extends_async {tiles bid region} (hl : asyncLayout tiles bid = some region) : layout tiles bid = some region := by
  have hb : bid < (asyncRegions tiles).length := (List.getElem?_eq_some_iff.mp hl).1
  simpa only [layout,regions,asyncLayout,List.getElem?_append_left hb] using hl

theorem plan_extends_async {tiles candidate ticket work} (family : ReplySourceFamily tiles candidate)
    (hm : asyncPlan family ticket = some work) : plan family ticket = some work := by
  have hb : ticket.seq ≤ 6*tiles := by
    unfold asyncPlan at hm
    split at hm
    · rename_i hg; exact hg.2.2
    · cases hm
  simp only [plan,hb,ite_true,hm]

theorem bindings_mapped {tiles candidate} (family : ReplySourceFamily tiles candidate) :
    Regions.Mapped (layout tiles) (plan family) (bindings family) := by
  intro binding hm
  rcases List.mem_append.mp hm with ha | hr
  · have hx := async_bindings_mapped family binding ha
    exact ⟨layout_extends_async hx.1,plan_extends_async family hx.2⟩
  · simp only [rootBindings,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    all_goals constructor
    all_goals first | rfl | simp [plan]

theorem commands_shape (tiles : Nat) : commands tiles = asyncCommands tiles ++ [.access 8 .write,.access 9 .write] := by
  simp only [commands,requests,List.map_append,List.map_flatMap,List.map_cons,List.map_nil,Ptx.Async.Preparation.Request.command]
  rfl

theorem commands_length (tiles : Nat) : (commands tiles).length = 6*tiles+2 := by
  simp [commands_shape,async_commands_length]

private theorem request_valid_mono {request : Ptx.Async.Preparation.Request} {before after : Nat}
    (hv : request.Valid before) (hle : before ≤ after) : request.Valid after := by
  cases request <;> simp only [Ptx.Async.Preparation.Request.Valid] at hv ⊢
  all_goals omega

theorem requests_valid (values : List Nat) (hv : values.length = 10) (tiles : Nat) :
    ∀ request ∈ requests tiles, request.Valid values.length := by
  intro request hm
  rcases List.mem_append.mp hm with ha | hr
  · obtain ⟨tile,_,hmem⟩ := List.mem_flatMap.mp ha
    exact request_valid_mono (tile_requests_valid tile request hmem) (by omega)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp [Ptx.Async.Preparation.Request.Valid,hv]

theorem preparation_exists (values : List Nat) (hv : values.length = 10) (tiles : Nat) :
    ∃ state, Ptx.Async.run (Ptx.Async.initial 1 values) (prepareActions tiles) = .ok state ∧
      Ptx.Async.Preparation.Ready state (commands tiles) ∧ state.buffers.length = 10 ∧
      Ptx.Async.getEvent state 0 = .ok ⟨0,6*tiles+2⟩ := by
  obtain ⟨state,hs,hr,hl,he⟩ := Ptx.Async.Preparation.ready_requests (Ptx.Async.Preparation.ready_initial values) (requests tiles)
    (by simpa [Ptx.Async.initial] using requests_valid values hv tiles)
  have hready : Ptx.Async.Preparation.Ready state (commands tiles) := by simpa [commands] using hr
  let next : Ptx.Async.State := {state with events := [⟨0,⟨0,(commands tiles).length⟩⟩]}
  have hrecord : Ptx.Async.step state (.record 0 0) = .ok next := by
    have hf := Ptx.Async.Preparation.ready_record hready (event := 0) (by simp [he,Ptx.Async.initial])
    simpa only [he,Ptx.Async.initial] using hf
  refine ⟨next,?_,hready,by simpa only [next,hl,Ptx.Async.initial,List.length_map] using hv,?_⟩
  · simp only [prepareActions,Ptx.Async.Client.run_append,hs,Except.bind,Ptx.Async.run,hrecord]
  · simp [Ptx.Async.getEvent,next,commands_length,bind,Except.bind,pure,Except.pure]

theorem preparation_succeeds (values : List Nat) (hv : values.length = 10) (tiles : Nat) :
    Ptx.Async.run (Ptx.Async.initial 1 values) (prepareActions tiles) = .ok (prepared values tiles) := by
  obtain ⟨state,hs,_⟩ := preparation_exists values hv tiles
  simp only [prepared,hs,Except.toOption,Option.getD_some]

theorem prepared_properties (values : List Nat) (hv : values.length = 10) (tiles : Nat) :
    Ptx.Async.Preparation.Ready (prepared values tiles) (commands tiles) ∧
      (prepared values tiles).buffers.length = 10 ∧ Ptx.Async.getEvent (prepared values tiles) 0 = .ok ⟨0,6*tiles+2⟩ := by
  obtain ⟨state,hs,hr,hl,he⟩ := preparation_exists values hv tiles
  have heq : state = prepared values tiles := Except.ok.inj (hs.symm.trans (preparation_succeeds values hv tiles))
  subst state
  exact ⟨hr,hl,he⟩

theorem prepared_invariant (values : List Nat) (hv : values.length = 10) (tiles : Nat) : Ptx.Async.Invariant (prepared values tiles) :=
  Ptx.Async.steps_invariant (Ptx.Async.initial_invariant 1 values) (Ptx.Async.run_sound (preparation_succeeds values hv tiles))

theorem prepared_command_loan (values : List Nat) (hv : values.length = 10) (tiles index : Nat)
    {command bid mode} (hc : (commands tiles)[index]? = some command) (ha : Ptx.Async.Accesses command bid mode) :
    Ptx.Async.Holds (prepared values tiles) bid ⟨⟨0,index+1⟩,mode⟩ := by
  have hr := (prepared_properties values hv tiles).1
  have hg : (prepared values tiles).streams[0]? = some ⟨(commands tiles).length,0,commands tiles,[]⟩ := by rw [hr.1]; rfl
  simpa only [Nat.zero_add] using (prepared_invariant values hv tiles).pending 0 _ hg index command hc bid mode ha

end
end Ptx.Kernels.HopperDoubleBuffer.Whole
