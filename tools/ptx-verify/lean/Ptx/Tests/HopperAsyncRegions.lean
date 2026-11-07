import Ptx.Kernels.HopperDoubleBufferAsyncCompletion
import Ptx.Tests.HopperRegionLoans

/-! Aggregate async coverage and a real publicly prepared three-tile client.
This includes both A/B copies and native uses across slot reuse. Ordinary
source/resource uses and physical runtime/byte-value refinement remain open.
-/
namespace Ptx.HopperAsyncRegionTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section

abbrev family := HopperProgressTests.family
abbrev candidate := HopperProgressTests.candidate
abbrev histories := HopperProgressTests.histories
abbrev source := HopperProgressTests.source

def tileActions (tile : Nat) : List Ptx.Async.Action :=
  [.use 0 0,.copy 0 2 (aBuffer tile),.use 0 1,.copy 0 3 (bBuffer tile),.use 0 (aBuffer tile),.use 0 (bBuffer tile)]
def preparation : List Ptx.Async.Action :=
  [.record 0 0] ++ (List.range 3).flatMap (fun tile => tileActions tile ++ [.record 0 (tile+10)]) ++ [.record 0 99]
def initialProtocol : Ptx.Async.State := Ptx.Async.initial 1 [0,0,17,19,0,0,0,0]
def prepared : Ptx.Async.State := (Ptx.Async.run initialProtocol preparation).toOption.getD (Ptx.Async.initial 0 [])

theorem public_preparation_succeeds : Ptx.Async.run initialProtocol preparation = .ok prepared := by decide
theorem prepared_valid : Ptx.Async.Invariant prepared :=
  Ptx.Async.steps_invariant (Ptx.Async.initial_invariant 1 _) (Ptx.Async.run_sound public_preparation_succeeds)
theorem prepared_has_eighteen_commands : (prepared.streams[0]?.map (fun stream => (stream.issued,stream.completed,stream.queue.length))) = some (18,0,18) := by decide
theorem prepared_has_twenty_four_loans : (prepared.buffers.map (fun buffer => buffer.loans.length)).sum = 24 := by decide

theorem bindings_count (a b) : (asyncBindings (family a b)).length = 24 := by
  simp [asyncBindings,tileAsyncBindings,tmaABindings,tmaBBindings,nativeBindings]

theorem all_async_uses_covered (a b) :
    Regions.Covers Tma.localShared Access.globalDescriptor (candidate a b) (fun _ => True) (asyncBindings (family a b)) :=
  all_async_region_coverage (family a b) (by decide) (by decide) (source a b)
    (retry_data_descriptors a b 3 HopperRetryDataMemoryTests.schedule (by decide) (by decide))

theorem all_bindings_borrowed (a b) : Regions.Borrowed (asyncBindings (family a b)) prepared := by
  intro binding hm hn
  obtain ⟨tile,ht,hmem⟩ := List.mem_flatMap.mp hm
  have hcases : tile = 0 ∨ tile = 1 ∨ tile = 2 := by have := List.mem_range.mp ht; omega
  rcases hcases with rfl | rfl | rfl
  all_goals
    simp only [tileAsyncBindings,tmaABindings,tmaBBindings,nativeBindings,List.map_cons,List.map_nil,
      List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    dsimp only [Regions.Binding.rename,ticketShift,aBuffers,bBuffers,nativeBuffers,aBuffer,bBuffer,stage]
    rw [Regions.holds_check]
    decide

theorem initial_faithful (a b) : Bridge.Faithful Tma.localShared (candidate a b) (histories a b) dataCluster (asyncPlan (family a b))
    ⟨prepared,fun _ => False⟩ := by
  apply Bridge.prepared_faithful
  · intro sid stream hg
    have hlen : prepared.streams.length = 1 := by decide
    have hs : sid = 0 := by have := (List.getElem?_eq_some_iff.mp hg).1; omega
    subst sid
    have hz : (prepared.streams[0]?.map Ptx.Async.Stream.completed) = some 0 := by decide
    simpa only [hg,Option.map_some,Option.some.injEq] using hz
  · intro ticket work hm
    simp only [asyncPlan] at hm
    split at hm
    · rename_i hguard; exact hguard.2.1
    · cases hm

theorem every_pending_async_region_protected (a b) {next work control node loc mode target region}
    (hs : Bridge.Steps HopperStage.block Tma.localShared (candidate a b) (histories a b) dataCluster (asyncPlan (family a b))
      ⟨prepared,fun _ => False⟩ next)
    (hu : Use Tma.localShared Access.globalDescriptor (candidate a b) work control node loc mode)
    (hp : ¬next.done control) (ht : asyncLayout 3 target = some region) (hl : region.Contains loc) :
    Ptx.Async.reclaim next.protocol target = .error .outstandingLoan :=
  Regions.pending_region_reclaim_rejected (async_layout_separated 3) (async_bindings_mapped (family a b))
    (all_async_uses_covered a b) (Regions.borrowed_steps (all_bindings_borrowed a b) hs)
    (Bridge.steps_faithful (initial_faithful a b) hs) (Bridge.steps_reached Reached.empty hs) trivial hu hp ht hl

def finish : List Bridge.Command := List.replicate 18 (.device 0) ++ [.host (.acquire 99),.host (.write 4 99)]
def finalProtocol : Ptx.Async.State := (Ptx.Async.run prepared (finish.map Bridge.Command.action)).toOption.getD (Ptx.Async.initial 0 [])

theorem finish_protocol_succeeds : Ptx.Async.run prepared (finish.map Bridge.Command.action) = .ok finalProtocol := by decide
theorem finish_returns_every_loan : finalProtocol.buffers.map Ptx.Async.Buffer.loans = List.replicate 8 [] := by decide
theorem finish_reuses_shared_a : Ptx.Async.getBuffer finalProtocol 4 = .ok ⟨99,true,[]⟩ := by decide

theorem aggregate_complete_coupled_run (a b) :
    Bridge.Steps HopperStage.block Tma.localShared (candidate a b) (histories a b) dataCluster (asyncPlan (family a b))
      ⟨prepared,fun _ => False⟩ ⟨finalProtocol,Present (candidate a b)⟩ := by
  have htma := (HopperRetryDataMemoryTests.positive_joint_components a b).1
  exact Bridge.steps_trans (Bridge.prefix_execution prepared (HopperProgressTests.actual_full_prefix a b))
    (Bridge.completed_script_execution (async_plan_full_completed (family a b) (by decide) (by decide) htma) finish finish_protocol_succeeds)

def oldAcquire : List Ptx.Async.Action := List.replicate 6 (.device 0) ++ [.acquire 10]
def afterOld : Ptx.Async.State := (Ptx.Async.run prepared oldAcquire).toOption.getD (Ptx.Async.initial 0 [])

theorem old_acquire_succeeds : Ptx.Async.run prepared oldAcquire = .ok afterOld := by decide
theorem old_event_returns_tile_zero_loan : ∀ buffer ∈ afterOld.buffers, (⟨⟨0,5⟩,.read⟩ : Ptx.Async.Loan) ∉ buffer.loans := by
  decide
theorem old_event_keeps_tile_two_loan : ∃ buffer, Ptx.Async.getBuffer afterOld 4 = .ok buffer ∧ ⟨⟨0,17⟩,.read⟩ ∈ buffer.loans := by
  exact ⟨(afterOld.buffers[4]?).getD {},by decide,by decide⟩
theorem old_event_cannot_reclaim_reused_slot : Ptx.Async.reclaim afterOld 4 = .error .outstandingLoan := by decide
theorem old_event_cannot_overwrite_reused_slot : Ptx.Async.hostWrite afterOld 4 99 = .error .outstandingLoan := by decide

theorem zero_ticket_rejected (a b) : asyncPlan (family a b) ⟨0,0⟩ = none := by simp [asyncPlan]
theorem wrong_stream_rejected (a b) : asyncPlan (family a b) ⟨1,1⟩ = none := by simp [asyncPlan]
theorem reused_slot_has_new_ticket : aBuffer 0 = aBuffer 2 ∧ asyncTicket 0 4 ≠ asyncTicket 2 4 := by decide

theorem b_ticket_cannot_name_a_copy (a b) :
    asyncPlan (family a b) (asyncTicket 1 2) ≠ some (.tma ((family a b).copyAId 1)) := by
  have ht := async_plan_ticket (family a b) 1 (by decide) 2
  simp only [show (2 : Fin 6).val = 2 from rfl,show ¬(2 < 2) from by decide,show 2 < 4 from by decide,ite_false,ite_true] at ht
  rw [ht]
  intro he
  exact retry_copy_roles_disjoint (family a b) 1 1 (by decide) (by decide) (Work.tma.inj (Option.some.inj he)).symm

theorem missing_b_descriptor_rejected (a b) :
    ¬Regions.Covers Tma.localShared Access.globalDescriptor (candidate a b) (fun _ => True)
      ((asyncBindings (family a b)).filter (fun binding => binding.buffer != 1)) := by
  intro hc
  have hcopy := family_copy_b_at (family a b) (source a b) 0 (by decide)
  have hu := Use.descriptor (resolve := Tma.localShared) (descriptor := Access.globalDescriptor) hcopy (offset := 0) (by decide)
  obtain ⟨binding,hm,_,_,hregion⟩ := hc _ _ _ _ _ trivial hu
  have hmap := (async_bindings_mapped (family a b) binding (List.mem_filter.mp hm).1).1
  have hregion' : binding.region.Contains (⟨.global,4224⟩ : Location) := by
    simpa only [Access.globalDescriptor,Location.add,reply_copy_b_descriptor_address,Nat.add_zero] using hregion
  have hcontains : regionDescriptorB.Contains (⟨.global,4224⟩ : Location) := by
    simp [Regions.Region.Contains,regionDescriptorB]
  have heq : binding.buffer = 1 := by
    by_contra hne
    exact async_layout_separated 3 _ _ _ _ hmap rfl hne _ hregion' hcontains
  have hkeep := (List.mem_filter.mp hm).2
  simp [heq] at hkeep

end
end Ptx.HopperAsyncRegionTests
