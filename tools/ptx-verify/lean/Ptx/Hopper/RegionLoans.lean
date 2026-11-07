import Ptx.Hopper.PrefixExecution
import Ptx.Async.LoanPreservation

/-! Explicit byte-region bindings for actual descriptor/TMA/native uses.
The checked binding certificate covers every use in its declared work scope,
matches read/write modes and ticket identities, and names separated regions.
This establishes lifetime protection under the coupled protocol. It does not
identify CUDA allocations, simulate byte values or cover ordinary source uses
not represented by Progress.Use. Region layouts are fixed in this slice.
-/
namespace Ptx.Hopper.Progress.Regions
open Ptx.ISA
noncomputable section

structure Region where
  base : Location
  bytes : Nat
  deriving Repr, DecidableEq

def Region.Contains (region : Region) (loc : Location) : Prop :=
  loc.space = region.base.space ∧ region.base.address ≤ loc.address ∧ loc.address < region.base.address+region.bytes

abbrev Layout := Nat → Option Region

def Separated (layout : Layout) : Prop := ∀ left right a b, layout left = some a → layout right = some b →
  left ≠ right → ∀ loc, a.Contains loc → ¬b.Contains loc

structure Binding where
  work : Work
  ticket : Ptx.Async.Ticket
  buffer : Nat
  mode : Ptx.Async.Mode
  region : Region
  deriving Repr, DecidableEq

def Mapped (layout : Layout) (plan : Bridge.Plan) (bindings : List Binding) : Prop :=
  ∀ binding ∈ bindings, layout binding.buffer = some binding.region ∧ plan binding.ticket = some binding.work

def Covers (resolve : Tma.SharedResolver) (descriptor : Access.DescriptorResolver) (candidate : Unified.Candidate)
    (scope : Work → Prop) (bindings : List Binding) : Prop :=
  ∀ work control node loc mode, scope work → Use resolve descriptor candidate work control node loc mode →
    ∃ binding ∈ bindings, binding.work = work ∧ binding.mode = mode ∧ binding.region.Contains loc

def Borrowed (bindings : List Binding) (protocol : Ptx.Async.State) : Prop :=
  ∀ binding ∈ bindings, Ptx.Async.complete protocol binding.ticket ≠ true →
    Ptx.Async.Holds protocol binding.buffer ⟨binding.ticket,binding.mode⟩

theorem borrowed_step {block resolve candidate histories cluster plan bindings s next}
    (hb : Borrowed bindings s.protocol)
    (hs : Bridge.Step block resolve candidate histories cluster plan s next) : Borrowed bindings next.protocol := by
  cases hs with
  | access advance => exact hb
  | host action run =>
    intro binding hm hn
    have hstreams := Bridge.host_preserves_streams run
    have hnold : Ptx.Async.complete s.protocol binding.ticket ≠ true := by simpa only [Ptx.Async.complete,hstreams] using hn
    have hh := hb binding hm hnold
    cases action with
    | record sid event => exact Ptx.Async.record_holds run hh
    | acquire event => exact Ptx.Async.await_incomplete_holds run hh hnold
    | reclaim bid => exact Ptx.Async.reclaim_holds run hh
    | write bid value => exact Ptx.Async.holds_extend (Ptx.Async.hostWrite_extends run) hh
  | device stream run completion =>
    intro binding hm hn
    have hnold : Ptx.Async.complete s.protocol binding.ticket ≠ true := fun hc => hn (Ptx.Async.deviceStep_complete_monotone run hc)
    exact Ptx.Async.holds_extend (Ptx.Async.deviceStep_extends run) (hb binding hm hnold)

theorem borrowed_steps {block resolve candidate histories cluster plan bindings s next}
    (hb : Borrowed bindings s.protocol)
    (hs : Bridge.Steps block resolve candidate histories cluster plan s next) : Borrowed bindings next.protocol := by
  induction hs with
  | refl => exact hb
  | next first rest ih => exact ih (borrowed_step hb first)

theorem pending_use_binding {block resolve descriptor candidate histories cluster plan layout bindings scope s work control node loc mode}
    (hm : Mapped layout plan bindings) (hc : Covers resolve descriptor candidate scope bindings)
    (hb : Borrowed bindings s.protocol) (hf : Bridge.Faithful resolve candidate histories cluster plan s)
    (hr : Reached block candidate histories s.done) (hw : scope work)
    (hu : Use resolve descriptor candidate work control node loc mode) (hp : ¬s.done control) :
    ∃ binding ∈ bindings, layout binding.buffer = some binding.region ∧ binding.region.Contains loc ∧
      binding.work = work ∧ binding.mode = mode ∧ Ptx.Async.Holds s.protocol binding.buffer ⟨binding.ticket,binding.mode⟩ := by
  obtain ⟨binding,hmem,hwork,hmode,hregion⟩ := hc _ _ _ _ _ hw hu
  have hmap := hm binding hmem
  have hn : Ptx.Async.complete s.protocol binding.ticket ≠ true := by
    intro hdone
    have hcomp := hf binding.ticket binding.work hmap.2 hdone
    rw [hwork] at hcomp
    exact pending_use_not_completed (reached_valid hr).1 hu hp hcomp
  exact ⟨binding,hmem,hmap.1,hregion,hwork,hmode,hb binding hmem hn⟩

theorem pending_region_reclaim_rejected {block resolve descriptor candidate histories cluster plan layout bindings scope s work control node loc mode target region}
    (hsep : Separated layout) (hm : Mapped layout plan bindings) (hc : Covers resolve descriptor candidate scope bindings)
    (hb : Borrowed bindings s.protocol) (hf : Bridge.Faithful resolve candidate histories cluster plan s)
    (hr : Reached block candidate histories s.done) (hw : scope work)
    (hu : Use resolve descriptor candidate work control node loc mode) (hp : ¬s.done control)
    (ht : layout target = some region) (hl : region.Contains loc) :
    Ptx.Async.reclaim s.protocol target = .error .outstandingLoan := by
  obtain ⟨binding,hmem,hmap,hregion,hwork,hmode,hholds⟩ := pending_use_binding hm hc hb hf hr hw hu hp
  have heq : binding.buffer = target := by
    by_contra hne
    exact hsep _ _ _ _ hmap ht hne loc hregion hl
  subst target
  exact Ptx.Async.reclaim_of_holds hholds

theorem pending_region_write_rejected {block resolve descriptor candidate histories cluster plan layout bindings scope s work control node loc mode target region value}
    (hsep : Separated layout) (hm : Mapped layout plan bindings) (hc : Covers resolve descriptor candidate scope bindings)
    (hb : Borrowed bindings s.protocol) (hf : Bridge.Faithful resolve candidate histories cluster plan s)
    (hr : Reached block candidate histories s.done) (hw : scope work)
    (hu : Use resolve descriptor candidate work control node loc mode) (hp : ¬s.done control)
    (ht : layout target = some region) (hl : region.Contains loc) :
    Ptx.Async.hostWrite s.protocol target value = .error .outstandingLoan := by
  obtain ⟨binding,hmem,hmap,hregion,hwork,hmode,hholds⟩ := pending_use_binding hm hc hb hf hr hw hu hp
  have heq : binding.buffer = target := by
    by_contra hne
    exact hsep _ _ _ _ hmap ht hne loc hregion hl
  subst target
  exact Ptx.Async.hostWrite_of_holds hholds

end
end Ptx.Hopper.Progress.Regions
