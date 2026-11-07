import Ptx.Kernels.AtomicDispatchTickets

/-! Complete local candidates for arbitrary reply assignments. This intentionally
constructs locally legal bad assignments too; memory consistency is separate.
AtomicDispatchWitness reuses these constructors for global nonvacuity. -/
namespace Ptx.AtomicDispatchEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.AtomicDispatchTrace
noncomputable section

def canonicalTrace (cfg : Config) (values : Nat → Nat) (cta : Nat) : Scalar.ThreadTrace := {
  id := id cta,oracle := fun _ => .integer (values cta),count := sourceCount (values cta)
  final := (finalState cfg.counter cfg.x cfg.y (wrap 32 (values cta))).core
  events := events cfg.counter cfg.x cfg.y (values cta)
}
def canonical (cfg : Config) (values : Nat → Nat) : Scalar.Candidate :=
  ⟨(List.range 2).map (canonicalTrace cfg values)⟩

theorem canonical_produced (cfg : Config) (values : Nat → Nat) (cta : Nat) (params : Bindings)
    (hp : Params cfg.counter cfg.x cfg.y params) : Scalar.Produced code params (canonicalTrace cfg values cta) .one := by
  exact ⟨(finalState cfg.counter cfg.x cfg.y (wrap 32 (values cta))).floats,
    translated_trace {id := id cta,params := params} (fun _ => .integer (values cta)) cfg.counter cfg.x cfg.y (values cta)
      hp (by have := cfg.counterEnd; omega) (by have := cfg.xEnd; omega) (by have := cfg.yEnd; omega) rfl⟩

theorem canonical_member (cfg : Config) (values : Nat → Nat) {cta : Nat} (hc : cta < 2) :
    canonicalTrace cfg values cta ∈ (canonical cfg values).traces :=
  List.mem_map.mpr ⟨cta,List.mem_range.mpr hc,rfl⟩

theorem canonical_ids (cfg : Config) (values : Nat → Nat) :
    ((canonical cfg values).traces.map Event.ThreadTrace.id).Nodup := by
  change [id 0,id 1].Nodup
  decide

theorem canonical_wellFormed (cfg : Config) (values : Nat → Nat) {launch : Scalar.Launch}
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params) :
    Scalar.WellFormed code launch (canonical cfg values) := by
  refine ⟨?_,canonical_ids cfg values,?_,?_⟩
  · simp [hg,geometry,Geometry.Valid,Dim3.Positive,Dim3.one]
  · intro t ht
    obtain ⟨cta,hin,rfl⟩ := List.mem_map.mp ht
    refine ⟨?_,?_⟩
    · simpa only [hg,canonicalTrace] using id_valid (List.mem_range.mp hin)
    · simpa only [hg,geometry] using canonical_produced cfg values cta launch.params hp
  · intro thread hv
    have hv' : thread.Valid geometry := by simpa only [hg] using hv
    obtain ⟨cta,hcta,rfl⟩ := valid_id hv'
    exact ⟨canonicalTrace cfg values cta,canonical_member cfg values hcta,rfl⟩

theorem canonical_complete (cfg : Config) (values : Nat → Nat) : (canonical cfg values).Complete := by
  intro t ht
  obtain ⟨cta,_,rfl⟩ := List.mem_map.mp ht
  exact final_done cfg.counter cfg.x cfg.y (wrap 32 (values cta))

end
end Ptx.AtomicDispatchEvent
