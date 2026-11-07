import Ptx.Kernels.HopperDoubleBufferBRegions
import Ptx.Hopper.RegionComposition

/-! One separated eight-buffer layout and six logical tickets per K tile.
These are modeled lifetime resources; public preparation and CUDA allocation/
command/byte-value correspondence are distinct obligations. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

def asyncRegions (tiles : Nat) : List Regions.Region :=
  [regionDescriptorA,regionDescriptorB,regionInputA tiles,regionInputB tiles,
    regionA 0,regionB 0,regionA 1,regionB 1]
def asyncLayout (tiles : Nat) : Regions.Layout := fun bid => (asyncRegions tiles)[bid]?
def aBuffer (tile : Nat) : Nat := 4+2*(stage tile).val
def bBuffer (tile : Nat) : Nat := 5+2*(stage tile).val
def aBuffers (tile : Nat) : Nat → Nat | 0 => 0 | 1 => 2 | _ => aBuffer tile
def bBuffers (tile : Nat) : Nat → Nat | 0 => 1 | 1 => 3 | _ => bBuffer tile
def nativeBuffers (tile : Nat) : Nat → Nat | 0 => aBuffer tile | _ => bBuffer tile
def ticketShift (offset : Nat) (ticket : Ptx.Async.Ticket) : Ptx.Async.Ticket := ⟨ticket.stream,offset+ticket.seq⟩
def asyncTicket (tile : Nat) (part : Fin 6) : Ptx.Async.Ticket := ⟨0,6*tile+part.val+1⟩

def asyncPlan {tiles candidate} (family : ReplySourceFamily tiles candidate) : Bridge.Plan := fun ticket =>
  if ticket.stream = 0 ∧ 0 < ticket.seq ∧ ticket.seq ≤ 6*tiles then
    let tile := (ticket.seq-1)/6
    match (ticket.seq-1)%6 with
    | 0 | 1 => some (.tma (family.copyAId tile))
    | 2 | 3 => some (.tma (family.copyBId tile))
    | _ => some (.native (family.mmaId tile 0))
  else none

def tileAsyncBindings {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) : List Regions.Binding :=
  ((tmaABindings (.tma (family.copyAId tile)) tiles tile).map (Regions.Binding.rename (aBuffers tile) (ticketShift (6*tile))) ++
    (tmaBBindings (.tma (family.copyBId tile)) tiles tile).map (Regions.Binding.rename (bBuffers tile) (ticketShift (6*tile+2)))) ++
    (nativeBindings (.native (family.mmaId tile 0)) tile).map (Regions.Binding.rename (nativeBuffers tile) (ticketShift (6*tile+4)))
def asyncBindings {tiles candidate} (family : ReplySourceFamily tiles candidate) : List Regions.Binding :=
  (List.range tiles).flatMap (tileAsyncBindings family)

theorem async_regions_disjoint (tiles : Nat) : (asyncRegions tiles).Pairwise Regions.Region.Disjoint := by
  simp [asyncRegions,List.pairwise_cons,Regions.Region.Disjoint,regionDescriptorA,regionDescriptorB,
    regionInputA,regionInputB,regionA,regionB,aBase,bBase,stage,dataBBase]
  omega

theorem async_layout_separated (tiles : Nat) : Regions.Separated (asyncLayout tiles) :=
  Regions.separated_of_pairwise _ (async_regions_disjoint tiles)

theorem async_layout_a (tiles tile : Nat) : asyncLayout tiles (aBuffer tile) = some (regionA tile) := by
  dsimp only [asyncLayout,asyncRegions,aBuffer,regionA,regionB]
  generalize stage tile = slot
  fin_cases slot <;> rfl

theorem async_layout_b (tiles tile : Nat) : asyncLayout tiles (bBuffer tile) = some (regionB tile) := by
  dsimp only [asyncLayout,asyncRegions,bBuffer,regionA,regionB]
  generalize stage tile = slot
  fin_cases slot <;> rfl

theorem async_plan_ticket {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (tile : Nat) (ht : tile < tiles) (part : Fin 6) :
    asyncPlan family (asyncTicket tile part) = some (if part.val < 2 then .tma (family.copyAId tile)
      else if part.val < 4 then .tma (family.copyBId tile) else .native (family.mmaId tile 0)) := by
  have hp := part.isLt
  have hpos : 0 < 6*tile+part.val+1 := by omega
  have hb : 6*tile+part.val+1 ≤ 6*tiles := by omega
  have hdiv : (6*tile+part.val+1-1)/6 = tile := by omega
  have hmod : (6*tile+part.val+1-1)%6 = part.val := by omega
  simp only [asyncPlan,asyncTicket,ite_true,hpos,hb,and_self,hdiv,hmod]
  fin_cases part <;> rfl

theorem async_plan_work {tiles candidate ticket work} (family : ReplySourceFamily tiles candidate)
    (hm : asyncPlan family ticket = some work) :
    ∃ tile, tile < tiles ∧ (work = .tma (family.copyAId tile) ∨ work = .tma (family.copyBId tile) ∨ work = .native (family.mmaId tile 0)) := by
  simp only [asyncPlan] at hm
  split at hm
  · rename_i hguard
    have ht : (ticket.seq-1)/6 < tiles := by omega
    split at hm
    all_goals first
      | exact ⟨_,ht,.inl (Option.some.inj hm).symm⟩
      | exact ⟨_,ht,.inr (.inl (Option.some.inj hm).symm)⟩
      | exact ⟨_,ht,.inr (.inr (Option.some.inj hm).symm)⟩
  · cases hm

theorem tile_async_bindings_mapped {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles) :
    Regions.Mapped (asyncLayout tiles) (asyncPlan family) (tileAsyncBindings family tile) := by
  intro binding hm
  simp only [tileAsyncBindings,tmaABindings,tmaBBindings,nativeBindings,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals try first
    | exact async_layout_a tiles tile
    | exact async_layout_b tiles tile
    | rfl
  · simpa [Regions.Binding.rename,ticketShift,asyncTicket,Nat.add_assoc] using async_plan_ticket family tile ht 0
  · simpa [Regions.Binding.rename,ticketShift,asyncTicket,Nat.add_assoc] using async_plan_ticket family tile ht 1
  · simpa [Regions.Binding.rename,ticketShift,asyncTicket,Nat.add_assoc] using async_plan_ticket family tile ht 1
  · simpa [Regions.Binding.rename,ticketShift,asyncTicket,Nat.add_assoc] using async_plan_ticket family tile ht 2
  · simpa [Regions.Binding.rename,ticketShift,asyncTicket,Nat.add_assoc] using async_plan_ticket family tile ht 3
  · simpa [Regions.Binding.rename,ticketShift,asyncTicket,Nat.add_assoc] using async_plan_ticket family tile ht 3
  · simpa [Regions.Binding.rename,ticketShift,asyncTicket,Nat.add_assoc] using async_plan_ticket family tile ht 4
  · simpa [Regions.Binding.rename,ticketShift,asyncTicket,Nat.add_assoc] using async_plan_ticket family tile ht 5

theorem async_bindings_mapped {tiles candidate} (family : ReplySourceFamily tiles candidate) :
    Regions.Mapped (asyncLayout tiles) (asyncPlan family) (asyncBindings family) := by
  intro binding hm
  obtain ⟨tile,ht,hmem⟩ := List.mem_flatMap.mp hm
  exact tile_async_bindings_mapped family tile (List.mem_range.mp ht) binding hmem

end
end Ptx.Kernels.HopperDoubleBuffer
