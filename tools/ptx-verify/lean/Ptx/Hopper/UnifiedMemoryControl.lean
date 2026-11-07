import Ptx.Hopper.UnifiedControl
import Ptx.Hopper.UnifiedOrder

/-! One-way control refinement of already justified byte-memory edges. For
sources without non-bulk copies, every byte edge/path maps to a native/TMA
control path. Control order alone never creates a memory-publication edge.
The no-nonbulk premise must be proved from the actual source inventory. -/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def baseMemoryControlNode : Access.Node → Tma.Node
  | .tma node => node
  | .copyRead id | .copyWrite id => .source id
def memoryControlNode : Node → ControlNode
  | .base node => .base (baseMemoryControlNode node)
  | .wgmmaRead issue operand => .operand issue operand

theorem program_order_control_edge {block c histories left right} (hp : ProgramOrder c left right) :
    ControlEdge block c histories (memoryControlNode left) (memoryControlNode right) := by
  cases left <;> cases right <;> try exact False.elim hp
  rename_i left right
  cases left <;> cases right <;> try exact False.elim hp
  exact base_control_edge (.inl hp)

theorem write_present_of_location {resolve c id offset loc}
    (hl : Tma.writeLocation resolve c id offset = some loc) : Tma.WritePresent c id offset := by
  cases hc : Tma.copyAt c id with
  | none => simp only [Tma.writeLocation,hc,Option.bind_none] at hl; cases hl
  | some op =>
    simp only [Tma.writeLocation,hc,Option.bind_some] at hl
    unfold Tma.WritePresent
    rw [hc]
    split at hl
    · assumption
    · cases hl

theorem protected_control_path {resolve c histories event id offset loc}
    (h : Access.Protected resolve c (.tma (.source event)) (.tma (.write id offset)) loc) :
    Ptx.Event.Path (Tma.ControlEdge c histories) (.source event) (.write id offset) := by
  obtain ⟨fence,_,hp,hq,hl,_⟩ := h
  have hw := write_present_of_location hl
  obtain ⟨op,hc,_⟩ := Tma.write_has_copy hw
  exact .trans (.single (.inl (show Tma.ProgramOrder c (.source event) (.source fence) from hp)))
    (.trans (.single (.inl (show Tma.ProgramOrder c (.source fence) (.source id.issue) from hq)))
    (.trans (.single (.inr (.inr (.inl (.issue (by rw [hc]; rfl))))))
      (.single (.inr (.inr (.inl (.descriptorWrite hw)))))))

theorem base_byte_control_path {resolve descriptor block c histories cluster loc left right}
    (hn : ∀ id, Access.copyAt c.view id = none)
    (h : Access.ByteEdge resolve descriptor c.view histories cluster loc left right) :
    Ptx.Event.Path (ControlEdge block c histories) (memoryControlNode (.base left)) (memoryControlNode (.base right)) := by
  apply base_control_path
  rcases h with hg | hi | hc | ht | hp | hf
  · cases left with
    | tma left =>
      cases left <;> cases right <;> try exact False.elim hg
      rename_i left right
      cases right <;> try exact False.elim hg
      exact .single (hg.elim (fun h => .inl h) (fun h => .inr (.inl h)))
    | copyRead _ | copyWrite _ => exact False.elim hg
  · cases left <;> cases right <;> simp [Access.NonbulkInternal,hn] at hi
  · cases left <;> cases right <;> simp only [Access.NonbulkCompleted] at hc
    rename_i issue node
    cases node <;> simp_all [hn]
  · cases left <;> cases right <;> simp only [Access.TensorInternal] at ht
    rename_i left right
    cases left <;> cases right <;> simp only [Access.TensorInternal] at ht
    obtain ⟨rfl,rfl,hr⟩ := ht
    exact .single (.inr (.inr (.inl (.data hr))))
  · cases left <;> cases right <;> simp only [Access.Published] at hp
    rename_i left right
    cases left <;> cases right <;> simp only [Access.Published] at hp
    exact Access.published_control_path hp
  · cases left <;> cases right <;> simp only [Access.Protected] at hf
    rename_i left right
    cases left <;> cases right <;> simp only [Access.Protected] at hf
    exact protected_control_path hf

theorem native_published_control_path {resolve block c histories cluster loc left right}
    (h : NativePublished resolve c histories cluster loc left right) :
    Ptx.Event.Path (ControlEdge block c histories) (memoryControlNode left) (memoryControlNode right) := by
  cases left <;> cases right <;> simp only [NativePublished] at h
  rename_i left issue operand
  cases left <;> try exact False.elim h
  rename_i node
  cases node <;> try exact False.elim h
  · obtain ⟨collective,_,_,all⟩ := h
    obtain ⟨fence,_,_,ha,hb⟩ := all 0
    have hs := Access.generic_after_control (histories := histories) (.trans ha hb)
    rw [collective.representative] at hs
    exact .trans (base_control_path hs) (.single (native_issue_edge (by rw [collective_representative collective]; rfl)))
  · obtain ⟨collective,hl,_,all⟩ := h
    obtain ⟨wait,ho,ha⟩ := all 0
    have hw := write_present_of_location hl
    have hs : Ptx.Event.Path (Tma.ControlEdge c.view histories) (.write _ _) (.source (collective.sources 0)) :=
      .trans (.single (.inr (.inr (.inl (.complete hw)))))
        (.trans (.single (.inr (.inr (.inr (Access.observed_resource_edge ho))))) (Access.generic_after_control ha))
    rw [collective.representative] at hs
    exact .trans (base_control_path hs) (.single (native_issue_edge (by rw [collective_representative collective]; rfl)))

theorem native_completed_control_path {block c histories loc left right}
    (h : NativeCompleted c loc left right) :
    Ptx.Event.Path (ControlEdge block c histories) (memoryControlNode left) (memoryControlNode right) := by
  cases left <;> cases right <;> try exact False.elim h
  rename_i issue operand right
  cases right <;> try exact False.elim h
  rename_i node
  cases node <;> try exact False.elim h
  exact .single (native_finish_edge h.1)

theorem native_reuse_control_path {resolve block c histories loc left right}
    (h : NativeReuse resolve c loc left right) :
    Ptx.Event.Path (ControlEdge block c histories) (memoryControlNode left) (memoryControlNode right) := by
  cases left <;> cases right <;> try exact False.elim h
  rename_i issue operand right
  cases right <;> try exact False.elim h
  rename_i node
  cases node <;> try exact False.elim h
  obtain ⟨wait,hc,ha,hl,_⟩ := h
  have hw := write_present_of_location hl
  obtain ⟨op,hcopy,_⟩ := Tma.write_has_copy hw
  have hs := Access.generic_after_control (histories := histories) ha
  have ht : Ptx.Event.Path (Tma.ControlEdge c.view histories) (.source _) (.write _ _) :=
    .trans (.single (.inr (.inr (.inl (.issue (by rw [hcopy]; rfl))))))
      (.single (.inr (.inr (.inl (.descriptorWrite hw)))))
  exact .trans (.single (native_finish_edge hc)) (.trans (base_control_path hs) (base_control_path ht))

theorem byte_edge_control_path {resolve descriptor block c histories cluster loc left right}
    (hn : ∀ id, Access.copyAt c.view id = none)
    (h : ByteEdge resolve descriptor c histories cluster loc left right) :
    Ptx.Event.Path (ControlEdge block c histories) (memoryControlNode left) (memoryControlNode right) := by
  rcases h with hb | hp | hc | hr
  · cases left <;> cases right <;> try exact False.elim hb
    exact base_byte_control_path hn hb
  · exact native_published_control_path hp
  · exact native_completed_control_path hc
  · exact native_reuse_control_path hr

theorem byte_order_control_path {resolve descriptor block c histories cluster loc left right}
    (hn : ∀ id, Access.copyAt c.view id = none)
    (h : ByteOrder resolve descriptor c histories cluster loc left right) :
    Ptx.Event.Path (ControlEdge block c histories) (memoryControlNode left) (memoryControlNode right) := by
  induction h with
  | single he => exact byte_edge_control_path hn he
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem byte_order_acyclic_of_control {resolve descriptor block c histories cluster}
    (hn : ∀ id, Access.copyAt c.view id = none) (hc : ControlAcyclic block c histories) :
    ∀ loc node, ¬ByteOrder resolve descriptor c histories cluster loc node node := by
  intro loc node ho
  exact hc (memoryControlNode node) (byte_order_control_path hn ho)

end
end Ptx.Hopper.Unified
