import Ptx.Kernels.HopperDoubleBufferWholePlan

/-! Exact public loan provenance for the combined ten-region protocol. -/
namespace Ptx.Kernels.HopperDoubleBuffer.Whole
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

theorem async_command_loan (values : List Nat) (hv : values.length = 10) (tiles tile : Nat) (ht : tile < tiles) (part : Fin 6)
    {command bid mode} (hc : (tileCommands tile)[part.val]? = some command) (ha : Ptx.Async.Accesses command bid mode) :
    Ptx.Async.Holds (prepared values tiles) bid ⟨asyncTicket tile part,mode⟩ := by
  have hindex : 6*tile+part.val < (asyncCommands tiles).length := by rw [async_commands_length]; have := part.isLt; omega
  apply prepared_command_loan values hv tiles (6*tile+part.val) _ ha
  rw [commands_shape,List.getElem?_append_left hindex]
  exact (async_command_at tiles tile ht part).trans hc

theorem async_bindings_borrowed {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (values : List Nat) (hv : values.length = 10) : Regions.Borrowed (asyncBindings family) (prepared values tiles) := by
  intro binding hm _
  obtain ⟨tile,ht,hmem⟩ := List.mem_flatMap.mp hm
  have htile := List.mem_range.mp ht
  simp only [tileAsyncBindings,tmaABindings,tmaBBindings,nativeBindings,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [Regions.Binding.rename,ticketShift,aBuffers,asyncTicket,Nat.add_assoc] using
      async_command_loan values hv tiles tile htile 0 (by rfl) (.useRead 0)
  · simpa [Regions.Binding.rename,ticketShift,aBuffers,asyncTicket,Nat.add_assoc] using
      async_command_loan values hv tiles tile htile 1 (by rfl) (.copyRead 2 (aBuffer tile))
  · simpa [Regions.Binding.rename,ticketShift,aBuffers,asyncTicket,Nat.add_assoc] using
      async_command_loan values hv tiles tile htile 1 (by rfl) (.copyWrite 2 (aBuffer tile))
  · simpa [Regions.Binding.rename,ticketShift,bBuffers,asyncTicket,Nat.add_assoc] using
      async_command_loan values hv tiles tile htile 2 (by rfl) (.useRead 1)
  · simpa [Regions.Binding.rename,ticketShift,bBuffers,asyncTicket,Nat.add_assoc] using
      async_command_loan values hv tiles tile htile 3 (by rfl) (.copyRead 3 (bBuffer tile))
  · simpa [Regions.Binding.rename,ticketShift,bBuffers,asyncTicket,Nat.add_assoc] using
      async_command_loan values hv tiles tile htile 3 (by rfl) (.copyWrite 3 (bBuffer tile))
  · simpa [Regions.Binding.rename,ticketShift,nativeBuffers,asyncTicket,Nat.add_assoc] using
      async_command_loan values hv tiles tile htile 4 (by rfl) (.useRead (aBuffer tile))
  · simpa [Regions.Binding.rename,ticketShift,nativeBuffers,asyncTicket,Nat.add_assoc] using
      async_command_loan values hv tiles tile htile 5 (by rfl) (.useRead (bBuffer tile))

theorem bindings_borrowed {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (values : List Nat) (hv : values.length = 10) : Regions.Borrowed (bindings family) (prepared values tiles) := by
  intro binding hm hn
  rcases List.mem_append.mp hm with ha | hr
  · exact async_bindings_borrowed family values hv binding ha hn
  · simp only [rootBindings,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · apply prepared_command_loan values hv tiles (6*tiles) _ (.accessMode 8 .write)
      rw [commands_shape,List.getElem?_append_right (by rw [async_commands_length]),async_commands_length]
      simp
    · have hh := prepared_command_loan values hv tiles (6*tiles+1) (command := .access 9 .write) ?_ (.accessMode 9 .write)
      · simpa only [Nat.add_assoc] using hh
      · rw [commands_shape,List.getElem?_append_right (by rw [async_commands_length]; omega),async_commands_length]
        simp

theorem initial_faithful {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (values : List Nat) (hv : values.length = 10) {resolve histories cluster} :
    Bridge.Faithful resolve candidate histories cluster (plan family) ⟨prepared values tiles,fun _ => False⟩ := by
  apply Bridge.prepared_faithful
  · intro sid stream hg
    rw [(prepared_properties values hv tiles).1.1] at hg
    cases sid with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at hg; subst stream; rfl
    | succ sid => simp at hg
  · intro ticket work hm
    unfold plan at hm
    split at hm
    · unfold asyncPlan at hm
      split at hm
      · rename_i hg; exact hg.2.1
      · cases hm
    · rename_i hlarge
      split at hm
      · omega
      · cases hm

end
end Ptx.Kernels.HopperDoubleBuffer.Whole
