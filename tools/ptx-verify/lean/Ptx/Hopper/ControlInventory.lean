import Ptx.Hopper.InFlightAccess

/-! A finite upper inventory for all actual unified control nodes. Extra
arrival/read/operand entries are harmless: reachability uses Present to retain
only actual nodes. No source completeness or physical launch bound is needed.
-/
namespace Ptx.Hopper.Progress
open Ptx.ISA
noncomputable section

def operands : List Wgmma.OperandByte :=
  List.ofFn (fun index : Fin 2304 => Classical.choose (Wgmma.operand_index_covered index))

theorem operand_mem (operand : Wgmma.OperandByte) : operand ∈ operands := by
  apply List.mem_ofFn.mpr
  refine ⟨⟨operand.index,Wgmma.operand_index_bounded operand⟩,?_⟩
  apply Wgmma.operand_index_unique
  exact Classical.choose_spec (Wgmma.operand_index_covered _)

def sourceNodes (event : Ptx.Event.EventId) : List Unified.ControlNode :=
  [.base (.source event),.arrival event] ++ operands.map (Unified.ControlNode.operand event)

def copyNodes (candidate : Unified.Candidate) (id : Tma.CopyId) : List Unified.ControlNode :=
  match Tma.copyAt candidate.view id with
  | none => []
  | some op => [.base (.descriptor id),.base (.notify id)] ++
      (List.range op.descriptor.bytes).flatMap (fun offset => [.base (.read id offset),.base (.write id offset)])

def inventory (candidate : Unified.Candidate) : List Unified.ControlNode :=
  candidate.view.eventIds.flatMap sourceNodes ++ (Tma.copies candidate.view).flatMap (copyNodes candidate)

private theorem source_node_mem {candidate event node}
    (hp : candidate.view.Present event) (hn : node ∈ sourceNodes event) : node ∈ inventory candidate := by
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨event,Hopper.present_mem_eventIds hp,hn⟩

private theorem copy_node_mem {candidate id op node}
    (hc : Tma.copyAt candidate.view id = some op) (hn : node ∈ copyNodes candidate id) : node ∈ inventory candidate := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨id,Tma.copy_present_mem hc,hn⟩

theorem present_mem_inventory {candidate node} (hp : Present candidate node) : node ∈ inventory candidate := by
  cases node with
  | base node =>
    cases node with
    | source event => exact source_node_mem hp (by simp [sourceNodes])
    | descriptor id =>
      obtain ⟨op,hc⟩ := Option.isSome_iff_exists.mp hp
      exact copy_node_mem hc (by simp [copyNodes,hc])
    | notify id =>
      obtain ⟨op,hc⟩ := Option.isSome_iff_exists.mp hp
      exact copy_node_mem hc (by simp [copyNodes,hc])
    | read id offset =>
      obtain ⟨op,hc,hb⟩ := Tma.read_has_copy hp
      apply copy_node_mem hc
      simp only [copyNodes,hc,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_flatMap,List.mem_range]
      exact .inr ⟨offset,hb,by simp⟩
    | write id offset =>
      obtain ⟨op,hc,hb⟩ := Tma.write_has_copy hp
      apply copy_node_mem hc
      simp only [copyNodes,hc,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_flatMap,List.mem_range]
      exact .inr ⟨offset,hb,by simp⟩
  | arrival event =>
    obtain ⟨signature,hs⟩ := Option.isSome_iff_exists.mp hp
    exact source_node_mem ((Unified.view_present_iff candidate event).mpr (Unified.native_signature_present hs)) (by simp [sourceNodes])
  | operand event operand =>
    obtain ⟨⟨mark,call⟩,hr⟩ := Option.isSome_iff_exists.mp hp
    have hp : candidate.Present event := by simp only [Unified.Candidate.Present,(Unified.representative_at hr).1,Option.isSome_some]
    apply source_node_mem ((Unified.view_present_iff candidate event).mpr hp)
    exact List.mem_append_right _ (List.mem_map.mpr ⟨operand,operand_mem operand,rfl⟩)

end
end Ptx.Hopper.Progress
