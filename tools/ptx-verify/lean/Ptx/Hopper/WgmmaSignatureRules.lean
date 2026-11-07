import Ptx.Hopper.WgmmaCollective

/-! Native collective signatures retain the actual fetched PC, dynamic
sequence and physical warpgroup. This rules out trusting a forged mark when
projecting an unlocated rich trace. No memory-publication edge is introduced. -/
namespace Ptx.Hopper.Wgmma
open Ptx.ISA
noncomputable section
set_option maxHeartbeats 1000000

def eventSignature (event : Event) : Option SourceSignature :=
  (collective event).map (fun pair => ⟨pair.1.pc,pair.1,pair.2⟩)
def eventSchedule (events : List Event) : List SourceSignature := events.filterMap eventSignature

/-- The evaluated per-thread accumulator predicate belongs to local value
semantics. Keep it in the raw signature but do not add a uniform-predicate
requirement to the aligned collective check. -/
def alignedSignature (signature : SourceSignature) : SourceSignature :=
  {signature with kind := match signature.kind with
    | .mma ordinal group registers a b _ => .mma ordinal group registers a b false
    | other => other}
theorem aligned_signature_local_scale (pc mark ordinal group registers a b) :
    alignedSignature ⟨pc,mark,.mma ordinal group registers a b true⟩ =
      alignedSignature ⟨pc,mark,.mma ordinal group registers a b false⟩ := rfl

theorem event_schedule_append (left right : List Event) :
    eventSchedule (left++right) = eventSchedule left++eventSchedule right := List.filterMap_append
theorem base_has_no_event_signature (event : Hopper.Event) : eventSignature (.base event) = none := rfl

theorem step_collective_mark {ctx oracle code before after emitted event mark kind}
    (hs : step ctx oracle code before = .ok (after,emitted))
    (hm : event ∈ emitted) (hc : collective event = some (mark,kind)) :
    mark.pc = before.base.scalar.core.thread.pc ∧
    mark.sequence = before.ledger.syncs ∧ mark.warpgroup = Ampere.linearThread ctx/128 := by
  simp only [step,liftBase,liftInteger,bind,Except.bind,pure,Except.pure] at hs
  repeat' first | split at hs | cases hs
  all_goals simp_all [collective,Wgmma.mark]
  all_goals first
    | (cases hc.1; exact ⟨rfl,rfl,rfl⟩)
    | (rcases hm with ⟨_,_,rfl⟩; cases hc)

theorem located_signature_sound {ctx oracle code count initial final located event} {serial : Nat}
    (hr : runLocated ctx oracle code count initial = .ok (final,located))
    (he : located[serial]? = some event) : sourceSignature event = eventSignature event.kind := by
  obtain ⟨before,after,emitted,hs,hm,hpc⟩ := SourceRun.event_origin hr he
  cases hc : collective event.kind with
  | none => simp only [sourceSignature,eventSignature,hc,Option.map_none]
  | some pair =>
    rcases pair with ⟨mark,kind⟩
    have hp : event.pc = mark.pc := hpc.trans (step_collective_mark hs hm hc).1.symm
    simp only [sourceSignature,eventSignature,hc,Option.map_some,hp]
theorem located_schedule_sound {ctx oracle code count initial final located}
    (hr : runLocated ctx oracle code count initial = .ok (final,located)) :
    schedule located = eventSchedule (located.map SourceRun.Located.kind) := by
  unfold schedule eventSchedule
  rw [List.filterMap_map]
  apply List.filterMap_congr
  intro event he
  obtain ⟨serial,hget⟩ := List.getElem?_of_mem he
  exact located_signature_sound hr hget

end
end Ptx.Hopper.Wgmma
