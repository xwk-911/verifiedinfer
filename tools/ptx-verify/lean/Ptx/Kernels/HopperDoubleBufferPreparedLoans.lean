import Ptx.Kernels.HopperDoubleBufferPreparation
import Ptx.Kernels.HopperDoubleBufferAsyncCoverage

/-! Every aggregate loan comes from a real publicly queued command, for any
finite tile count. The executable protocol invariant supplies the exact ticket,
buffer and mode; no initial Borrowed certificate is assumed by the caller. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

theorem async_command_at (tiles tile : Nat) (ht : tile < tiles) (part : Fin 6) :
    (asyncCommands tiles)[6*tile+part.val]? = (tileCommands tile)[part.val]? := by
  induction tiles with
  | zero => omega
  | succ tiles ih =>
    by_cases hbefore : tile < tiles
    · rw [async_commands_succ,List.getElem?_append_left (by rw [async_commands_length]; have := part.isLt; omega)]
      exact ih hbefore
    · have heq : tile = tiles := by omega
      subst tile
      rw [async_commands_succ,List.getElem?_append_right (by rw [async_commands_length]; omega),async_commands_length,Nat.add_sub_cancel_left]

theorem public_command_loan (values : List Nat) (hv : values.length = 8) (tiles tile : Nat) (ht : tile < tiles) (part : Fin 6)
    {command bid mode} (hc : (tileCommands tile)[part.val]? = some command) (ha : Ptx.Async.Accesses command bid mode) :
    Ptx.Async.Holds (publicPrepared values tiles) bid ⟨asyncTicket tile part,mode⟩ := by
  have hr := (public_prepared_properties values hv tiles).1
  have hi := public_prepared_invariant values hv tiles
  have hg : (publicPrepared values tiles).streams[0]? = some ⟨(asyncCommands tiles).length,0,asyncCommands tiles,[]⟩ := by
    rw [hr.1]; rfl
  simpa only [asyncTicket,Nat.zero_add] using hi.pending 0 _ hg (6*tile+part.val) command
    ((async_command_at tiles tile ht part).trans hc) bid mode ha

theorem public_bindings_borrowed {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (values : List Nat) (hv : values.length = 8) : Regions.Borrowed (asyncBindings family) (publicPrepared values tiles) := by
  intro binding hm _
  obtain ⟨tile,ht,hmem⟩ := List.mem_flatMap.mp hm
  have htile := List.mem_range.mp ht
  simp only [tileAsyncBindings,tmaABindings,tmaBBindings,nativeBindings,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [Regions.Binding.rename,ticketShift,aBuffers,asyncTicket,Nat.add_assoc] using
      public_command_loan values hv tiles tile htile 0 (by rfl) (.useRead 0)
  · simpa [Regions.Binding.rename,ticketShift,aBuffers,asyncTicket,Nat.add_assoc] using
      public_command_loan values hv tiles tile htile 1 (by rfl) (.copyRead 2 (aBuffer tile))
  · simpa [Regions.Binding.rename,ticketShift,aBuffers,asyncTicket,Nat.add_assoc] using
      public_command_loan values hv tiles tile htile 1 (by rfl) (.copyWrite 2 (aBuffer tile))
  · simpa [Regions.Binding.rename,ticketShift,bBuffers,asyncTicket,Nat.add_assoc] using
      public_command_loan values hv tiles tile htile 2 (by rfl) (.useRead 1)
  · simpa [Regions.Binding.rename,ticketShift,bBuffers,asyncTicket,Nat.add_assoc] using
      public_command_loan values hv tiles tile htile 3 (by rfl) (.copyRead 3 (bBuffer tile))
  · simpa [Regions.Binding.rename,ticketShift,bBuffers,asyncTicket,Nat.add_assoc] using
      public_command_loan values hv tiles tile htile 3 (by rfl) (.copyWrite 3 (bBuffer tile))
  · simpa [Regions.Binding.rename,ticketShift,nativeBuffers,asyncTicket,Nat.add_assoc] using
      public_command_loan values hv tiles tile htile 4 (by rfl) (.useRead (aBuffer tile))
  · simpa [Regions.Binding.rename,ticketShift,nativeBuffers,asyncTicket,Nat.add_assoc] using
      public_command_loan values hv tiles tile htile 5 (by rfl) (.useRead (bBuffer tile))

theorem public_initial_faithful {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (values : List Nat) (hv : values.length = 8) {resolve histories cluster} :
    Bridge.Faithful resolve candidate histories cluster (asyncPlan family) ⟨publicPrepared values tiles,fun _ => False⟩ := by
  apply Bridge.prepared_faithful
  · intro sid stream hg
    rw [(public_prepared_properties values hv tiles).1.1] at hg
    cases sid with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at hg; subst stream; rfl
    | succ sid => simp at hg
  · intro ticket work hm
    simp only [asyncPlan] at hm
    split at hm
    · rename_i hguard; exact hguard.2.1
    · cases hm

theorem public_pending_async_reclaim_rejected {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (values : List Nat) (hv : values.length = 8)
    {histories : Location → List Tma.Entry} {next work control node loc mode target region}
    (hs : Bridge.Steps HopperStage.block Tma.localShared candidate histories dataCluster (asyncPlan family)
      ⟨publicPrepared values tiles,fun _ => False⟩ next)
    (hu : Use Tma.localShared Access.globalDescriptor candidate work control node loc mode) (hp : ¬next.done control)
    (hm : asyncLayout tiles target = some region) (hl : region.Contains loc) :
    Ptx.Async.reclaim next.protocol target = .error .outstandingLoan :=
  Regions.pending_region_reclaim_rejected (async_layout_separated tiles) (async_bindings_mapped family)
    (all_async_region_coverage family ht hb hw hd) (Regions.borrowed_steps (public_bindings_borrowed family values hv) hs)
    (Bridge.steps_faithful (public_initial_faithful family values hv) hs) (Bridge.steps_reached Reached.empty hs) trivial hu hp hm hl

theorem public_pending_async_write_rejected {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (values : List Nat) (hv : values.length = 8)
    {histories : Location → List Tma.Entry} {next work control node loc mode target region value}
    (hs : Bridge.Steps HopperStage.block Tma.localShared candidate histories dataCluster (asyncPlan family)
      ⟨publicPrepared values tiles,fun _ => False⟩ next)
    (hu : Use Tma.localShared Access.globalDescriptor candidate work control node loc mode) (hp : ¬next.done control)
    (hm : asyncLayout tiles target = some region) (hl : region.Contains loc) :
    Ptx.Async.hostWrite next.protocol target value = .error .outstandingLoan :=
  Regions.pending_region_write_rejected (async_layout_separated tiles) (async_bindings_mapped family)
    (all_async_region_coverage family ht hb hw hd) (Regions.borrowed_steps (public_bindings_borrowed family values hv) hs)
    (Bridge.steps_faithful (public_initial_faithful family values hv) hs) (Bridge.steps_reached Reached.empty hs) trivial hu hp hm hl

end
end Ptx.Kernels.HopperDoubleBuffer
