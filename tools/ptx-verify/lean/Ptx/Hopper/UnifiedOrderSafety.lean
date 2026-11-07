import Ptx.Hopper.UnifiedOrder

namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

theorem native_incoming_edge {resolve descriptor c histories cluster loc left issue operand}
    (h : ByteEdge resolve descriptor c histories cluster loc left (.wgmmaRead issue operand)) :
    (∃ copy offset, left = .base (.tma (.write copy offset)) ∧ TmaReady resolve c histories cluster copy offset issue operand loc) ∨
      (∃ source, left = .base (.tma (.source source)) ∧ GenericReady c source issue operand loc) := by
  cases left with
  | wgmmaRead _ _ => simp [ByteEdge,NativePublished,NativeCompleted,NativeReuse] at h
  | base node =>
    cases node with
    | copyRead _ | copyWrite _ => simp [ByteEdge,NativePublished,NativeCompleted,NativeReuse] at h
    | tma node =>
      cases node with
      | write copy offset => exact .inl ⟨copy,offset,rfl,by simpa only [ByteEdge,NativePublished,NativeCompleted,NativeReuse,false_or,or_false] using h⟩
      | source source => exact .inr ⟨source,rfl,by simpa only [ByteEdge,NativePublished,NativeCompleted,NativeReuse,false_or,or_false] using h⟩
      | descriptor _ | read _ _ | notify _ => simp [ByteEdge,NativePublished,NativeCompleted,NativeReuse] at h
theorem path_has_last_edge {α : Type} {edge : α → α → Prop} {a b : α} (h : Ptx.Event.Path edge a b) : ∃ left, edge left b := by
  induction h with
  | single he => exact ⟨_,he⟩
  | trans _ _ _ ih => exact ih
theorem native_incoming_is_shared {resolve descriptor c histories cluster loc left issue operand}
    (h : ByteEdge resolve descriptor c histories cluster loc left (.wgmmaRead issue operand)) : loc.space = .shared issue.thread.cta := by
  rcases native_incoming_edge h with ⟨copy,offset,_,hready⟩ | ⟨source,_,hready⟩
  · obtain ⟨_,_,hl,_⟩ := hready
    rw [← hl]
    cases operand <;> rfl
  · exact hready.choose_spec.2.1
theorem global_order_stays_base {resolve descriptor c histories cluster loc a b}
    (hg : loc.space = .global) (h : ByteOrder resolve descriptor c histories cluster loc a b) :
    (∃ node, a = .base node) → ∃ node, b = .base node := by
  induction h with
  | @single a b he =>
    rintro ⟨node,rfl⟩
    cases b with
    | base other => exact ⟨other,rfl⟩
    | wgmmaRead issue operand => have hs := native_incoming_is_shared he; rw [hg] at hs; cases hs
  | trans _ _ ih1 ih2 => exact fun h => ih2 (ih1 h)
theorem global_order_base_projection {resolve descriptor c histories cluster loc a b}
    (hg : loc.space = .global) (h : ByteOrder resolve descriptor c histories cluster loc a b) :
    ∀ left right, a = .base left → b = .base right → Access.ByteOrder resolve descriptor c.view histories cluster loc left right := by
  induction h with
  | single he =>
    intro left right ha hb
    cases ha; cases hb
    exact .single (by simpa only [ByteEdge,NativePublished,NativeCompleted,NativeReuse,or_false] using he)
  | @trans a middle b hp hq ih1 ih2 =>
    intro left right ha hb
    obtain ⟨node,hm⟩ := global_order_stays_base hg hp ⟨left,ha⟩
    exact .trans (ih1 left node ha hm) (ih2 node right hm hb)
theorem global_base_order_iff {resolve descriptor c histories cluster loc left right} (hg : loc.space = .global) :
    ByteOrder resolve descriptor c histories cluster loc (.base left) (.base right) ↔
      Access.ByteOrder resolve descriptor c.view histories cluster loc left right :=
  ⟨fun h => global_order_base_projection hg h left right rfl rfl,base_byte_order⟩
theorem no_publication_no_native_order {resolve descriptor c histories cluster loc issue operand left}
    (ht : ∀ copy offset, ¬TmaReady resolve c histories cluster copy offset issue operand loc)
    (hg : ∀ source, ¬GenericReady c source issue operand loc) :
    ¬ByteOrder resolve descriptor c histories cluster loc left (.wgmmaRead issue operand) := by
  intro h
  obtain ⟨other,he⟩ := path_has_last_edge h
  rcases native_incoming_edge he with ⟨copy,offset,_,hc⟩ | ⟨source,_,hc⟩
  · exact ht copy offset hc
  · exact hg source hc
theorem no_proxy_fence_no_generic_ready {c source issue operand loc}
    (hn : ∀ fence cta, c.view.eventAt fence ≠ some (.proxyFenceAsyncShared cta)) : ¬GenericReady c source issue operand loc := by
  intro h
  obtain ⟨fence,he⟩ := generic_ready_requires_fence h
  exact hn _ _ he
theorem zero_groups_cannot_complete {c issue wait mark keep before after query}
    (he : c.eventAt wait = some (.wait mark 0 keep before after query)) : ¬WgmmaCompletedAt c issue wait := by
  intro h
  obtain ⟨collective,lane,m,groups,k,before',after',q,hs,_,_,_,_,hg,_,ha,_⟩ := h
  have hh := Wgmma.Event.wait.inj (Option.some.inj (he.symm.trans hs))
  rcases hh with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  omega
theorem no_completion_no_native_reuse {resolve c loc issue operand right}
    (hn : ∀ wait, ¬WgmmaCompletedAt c issue wait) : ¬NativeReuse resolve c loc (.wgmmaRead issue operand) right := by
  cases right with
  | wgmmaRead _ _ => exact id
  | base node =>
    cases node with
    | copyRead _ | copyWrite _ => exact id
    | tma node =>
      cases node with
      | source _ | descriptor _ | read _ _ | notify _ => exact id
      | write copy offset => rintro ⟨wait,hc,_⟩; exact hn wait hc

end
end Ptx.Hopper.Unified
