import Ptx.Hopper.WgmmaRules

/-! Checkable source schedule projections for all 128 lanes. These retain
instruction PC, dynamic sequence, warpgroup, descriptors and fixed-profile
operands. They do not by themselves admit shared memory reads, arithmetic,
SIMT control or an entire physical warpgroup execution. -/
namespace Ptx.Hopper.Wgmma
noncomputable section

inductive CollectiveKind
  | fence
  | mma (ordinal group : Nat) (registers : List String) (a b : Nat) (scaleD : Bool)
  | commit (group : Nat)
  | wait (groups keep : Nat)
  deriving Repr, DecidableEq
structure SourceSignature where
  pc : Nat
  mark : Mark
  kind : CollectiveKind
  deriving Repr, DecidableEq

def collective : Event → Option (Mark × CollectiveKind)
  | .base _ => none
  | .fence m => some (m,.fence)
  | .mma m call => some (m,.mma call.ordinal call.group call.d.names call.a call.b call.scaleD)
  | .commit m group => some (m,.commit group)
  | .wait m groups keep _ _ _ => some (m,.wait groups keep)
def sourceSignature (event : SourceRun.Located Event) : Option SourceSignature :=
  (collective event.kind).map (fun pair => ⟨event.pc,pair.1,pair.2⟩)
def schedule (events : List (SourceRun.Located Event)) : List SourceSignature :=
  events.filterMap sourceSignature

theorem schedule_append (left right : List (SourceRun.Located Event)) :
    schedule (left++right) = schedule left++schedule right := List.filterMap_append
theorem source_mma_signature (pc mark call) :
    sourceSignature ⟨.mma mark call,pc⟩ =
      some ⟨pc,mark,.mma call.ordinal call.group call.d.names call.a call.b call.scaleD⟩ := rfl
theorem source_wait_signature (pc mark groups keep before after query) :
    sourceSignature ⟨.wait mark groups keep before after query,pc⟩ = some ⟨pc,mark,.wait groups keep⟩ := rfl
theorem ordinary_has_no_collective_signature (pc event) : sourceSignature ⟨.base event,pc⟩ = none := rfl

end
end Ptx.Hopper.Wgmma
