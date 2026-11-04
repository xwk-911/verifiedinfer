import Ptx.Async.Invariant
import Ptx.Iris.Async
import Iris.BI.Lib.GenHeap

/-! A physical heap interpretation for the actual async state. Key zero is the
stream/event control state; buffer bid has the unique key bid+1. Unlike OwnP,
points-to fragments split by physical buffer and support fractional read shares.
The buffer snapshot includes alive/loans, so changing metadata requires full
ownership too. This module does not hide that obligation behind a pure token.
-/
namespace Ptx.AsyncHeap
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language
open Iris.ProgramLogic.Language.Notation
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap

inductive Cell where
  | control (streams : List Async.Stream) (events : List Async.Event) (buffers : Nat)
  | buffer (value : Async.Buffer)
abbrev HeapF (V : Type) := _root_.Std.ExtTreeMap Nat V compare
local instance : Iris.Std.LawfulPartialMap HeapF Nat :=
  (inferInstance : Iris.Std.LawfulFiniteMap HeapF Nat).toLawfulPartialMap
local instance : Iris.Std.PartialMap HeapF Nat :=
  (inferInstance : Iris.Std.LawfulFiniteMap HeapF Nat).toLawfulPartialMap.toPartialMap
abbrev Heap := HeapF Cell

def bufferMap (start : Nat) : List Async.Buffer → Heap
  | [] => empty
  | b::bs => insert (bufferMap (start+1) bs) start (.buffer b)

def store (s : Async.State) : Heap :=
  insert (bufferMap 1 s.buffers) 0 (.control s.streams s.events s.buffers.length)

theorem bufferMap_lookup (start key : Nat) (xs : List Async.Buffer) :
    get? (bufferMap start xs) key =
      if start ≤ key then (xs[key-start]?).map Cell.buffer else none := by
  induction xs generalizing start with
  | nil =>
    simp only [bufferMap,List.getElem?_nil,Option.map_none,ite_self]
    exact get?_empty key
  | cons b bs ih =>
    by_cases he : start = key
    · subst key; simp [bufferMap,get?_insert]
    · rw [bufferMap,get?_insert_ne he,ih]
      by_cases hle : start ≤ key
      · have hnext : start+1 ≤ key := by omega
        have hsub : key-start = (key-(start+1))+1 := by omega
        simp [hle,hnext,hsub]
      · have hnext : ¬ start+1 ≤ key := by omega
        simp [hle,hnext]

@[simp] theorem store_control (s : Async.State) :
    get? (store s) 0 = some (.control s.streams s.events s.buffers.length) := by simp [store,get?_insert]

@[simp] theorem store_buffer (s : Async.State) (bid : Nat) :
    get? (store s) (bid+1) = (s.buffers[bid]?).map Cell.buffer := by
  simp [store,get?_insert,bufferMap_lookup]

theorem buffer_lookup {s bid b} : get? (store s) (bid+1) = some (.buffer b) ↔
    s.buffers[bid]? = some b := by
  rw [store_buffer]
  cases h : s.buffers[bid]? <;> simp_all

theorem store_set_buffer {s : Async.State} {bid : Nat} {b : Async.Buffer}
    (hb : bid < s.buffers.length) :
    store {s with buffers := s.buffers.set bid b} = insert (store s) (bid+1) (.buffer b) := by
  apply equiv_iff_eq.mp
  intro key
  cases key with
  | zero => simp [get?_insert]
  | succ i =>
    by_cases hi : bid = i
    · subst i; simp [hb,get?_insert]
    · simp [get?_insert_ne (by omega : bid+1 ≠ i+1), List.getElem?_set_ne hi]

theorem store_set_control (s : Async.State) (streams : List Async.Stream) (events : List Async.Event) :
    store {s with streams := streams,events := events} =
      insert (store s) 0 (.control streams events s.buffers.length) := by
  apply equiv_iff_eq.mp
  intro key
  cases key <;> simp [store,get?_insert]

/-- The control cell includes the buffer count, so owning all expected cells
also excludes a hidden suffix of additional physical buffers. -/
theorem store_submap_eq {s t : Async.State} (h : submap (store s) (store t)) : s = t := by
  have hc := h 0 (.control s.streams s.events s.buffers.length) (store_control s)
  rw [store_control] at hc
  obtain ⟨hstreams,hevents,hlen⟩ := Cell.control.inj (Option.some.inj hc)
  have hbuf : s.buffers = t.buffers := by
    apply List.ext_getElem?
    intro bid
    cases hs : s.buffers[bid]? with
    | none =>
      have hi : s.buffers.length ≤ bid := List.getElem?_eq_none_iff.mp hs
      have ht : t.buffers[bid]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      exact ht.symm
    | some b =>
      have ht := buffer_lookup.mp (h (bid+1) (.buffer b) (buffer_lookup.mpr hs))
      exact ht.symm
  cases s
  cases t
  simp_all

theorem store_dom_eq {s t : Async.State} (hlen : s.buffers.length = t.buffers.length) :
    dom (store s) = dom (store t) := by
  funext key
  apply propext
  cases key with
  | zero => simp [dom]
  | succ i =>
    by_cases hi : i < s.buffers.length
    · have ht : i < t.buffers.length := by omega
      simp [dom,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem ht]
    · have hs : s.buffers[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      have ht : t.buffers[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      simp [dom,hs,ht]

theorem store_union {s t : Async.State} (hlen : s.buffers.length = t.buffers.length) :
    Iris.Std.PartialMap.union (store t) (store s) = store t := by
  apply equiv_iff_eq.mp
  intro key
  simp only [Iris.Std.PartialMap.union,get?_merge]
  cases ht : get? (store t) key with
  | some value => cases get? (store s) key <;> simp [Option.merge]
  | none =>
    have hs : get? (store s) key = none := by
      cases hs : get? (store s) key with
      | none => rfl
      | some value =>
        have hd : dom (store s) key := by simp [dom,hs]
        rw [store_dom_eq hlen] at hd
        simp [dom,ht] at hd
    simp [hs,Option.merge]

open COFE Auth Std.LawfulSet
noncomputable def GF : BundledGFunctors := fun n =>
  match n with
  | 0 => ⟨InvMapF⟩
  | 1 => ⟨constOF CoPsetDisjL⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet)⟩
  | 3 => ⟨AuthURF (constOF Credit)⟩
  | 4 => ⟨constOF (HeapView Nat (Agree (DiscreteO Cell)) HeapF)⟩
  | 5 => ⟨constOF (HeapView Nat (Agree (DiscreteO GName)) HeapF)⟩
  | 6 => ⟨constOF MetaUR⟩
  | _ => ⟨constOF Unit⟩

instance : WsatGpreS GF where
  inv := {τ := 0,transp := by unfold GF; rfl}
  enabled := {τ := 1,transp := by unfold GF; rfl}
  disabled := {τ := 2,transp := by unfold GF; rfl}
instance : LcGpreS GF where
  lc_elem := {τ := 3,transp := by unfold GF; rfl}
instance : InvGpreS GF where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance
instance : genHeapPreS Nat Cell GF HeapF where
  heap := ⟨⟨4,by unfold GF; rfl⟩⟩
  metaInfo := ⟨⟨5,by unfold GF; rfl⟩⟩
  metaData := ⟨6,by unfold GF; rfl⟩

class GS where
  inv : InvGS GF
  heap : genHeapGS Nat Cell GF HeapF
attribute [reducible, instance] GS.heap

noncomputable section

instance [GS] : StateInterp Async.State Unit GF where
  stateInterp s _ _ _ := genHeapInterp (store s)

instance [g : GS] : IrisGS_gen .hasLC IrisAsync.Expr GF where
  invGS := g.inv
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := letI := g.inv; fupd_intro

local bi (IProp GF)

def buffer [GS] (bid : Nat) (dq : DFrac) (b : Async.Buffer) : IProp GF :=
  pointsTo (bid+1) dq (.buffer b)

def control [GS] (streams : List Async.Stream) (events : List Async.Event) (count : Nat) : IProp GF :=
  pointsTo 0 (.own 1) (.control streams events count)

def allPoints [GS] (s : Async.State) : IProp GF :=
  iprop([∗map] key ↦ value ∈ store s, pointsTo key (.own 1) value)

theorem buffer_split [GS] (bid : Nat) (q : Qp) (b : Async.Buffer) :
    buffer bid (.own q) b ⊣⊢ buffer bid (.own q.half) b ∗ buffer bid (.own q.half) b := by
  unfold buffer
  have hs := (Iris.instFractionalPointsTo (GF := GF) (l := bid+1) (v := Cell.buffer b)).fractional q.half q.half
  simpa only [Qp.half_add_half] using hs

theorem buffer_agree [GS] (bid : Nat) (dq dr : DFrac) (a b : Async.Buffer) :
    buffer bid dq a ∗ buffer bid dr b ⊢ ⌜a = b⌝ := by
  unfold buffer
  iintro H
  ihave %he := pointsTo_agree $$ H
  ipureintro; exact Cell.buffer.inj he

theorem buffer_full_exclusive [GS] (bid : Nat) (a b : Async.Buffer) :
    buffer bid (.own 1) a ∗ buffer bid (.own 1) b ⊢ False := by
  unfold buffer
  iintro ⟨Ha,Hb⟩
  ihave %hne := pointsTo_ne $$ Ha Hb
  ipureintro; exact hne rfl

theorem buffer_full_read_exclusive [GS] (bid : Nat) (q : Qp) (a b : Async.Buffer) :
    buffer bid (.own 1) a ∗ buffer bid (.own q) b ⊢ False := by
  unfold buffer
  iintro ⟨Ha,Hb⟩
  ihave %hne := pointsTo_ne $$ Ha Hb
  ipureintro; exact hne rfl

/-- Lookup comes from the actual authoritative heap, not a free realization premise. -/
theorem buffer_valid [GS] (s : Async.State) (bid : Nat) (dq : DFrac) (b : Async.Buffer) :
    genHeapInterp (store s) ∗ buffer bid dq b ==∗ ⌜s.buffers[bid]? = some b⌝ := by
  unfold buffer
  iintro H
  imod genHeap_valid $$ H with %h
  imodintro
  ipureintro; exact buffer_lookup.mp h

/-- Updating one physical buffer updates the authoritative store while preserving
all other location fragments by the existing Iris frame-preserving update. -/
theorem buffer_update [GS] {s : Async.State} {bid : Nat} {old fresh : Async.Buffer}
    (hb : bid < s.buffers.length) :
    genHeapInterp (store s) ∗ buffer bid (.own 1) old ==∗
      genHeapInterp (store {s with buffers := s.buffers.set bid fresh}) ∗ buffer bid (.own 1) fresh := by
  unfold buffer
  rw [store_set_buffer hb]
  exact genHeap_update

theorem allPoints_valid [g : GS] (actual expected : Async.State) :
    genHeapInterp (store actual) ∗ allPoints expected ==∗ ⌜actual = expected⌝ := by
  letI : genHeapPreS Nat Cell GF HeapF := g.heap.togenHeapPreS
  unfold genHeapInterp allPoints pointsTo
  iintro ⟨⟨%metadata,_,Hauth,_⟩,Hpts⟩
  icases ghost_map_lookup_big (store expected) $$ Hauth Hpts with %hsub
  imodintro
  ipureintro; exact (store_submap_eq hsub).symm

/-- A same-domain bulk update consumes the actual map's separated full fragments.
This permits retaining the existing global acquire API, whose loan filtering
can touch several buffers; local rules above do not require this aggregate. -/
theorem allPoints_update [g : GS] (s t : Async.State) (hlen : s.buffers.length = t.buffers.length) :
    genHeapInterp (store s) ∗ allPoints s ==∗ genHeapInterp (store t) ∗ allPoints t := by
  letI : genHeapPreS Nat Cell GF HeapF := g.heap.togenHeapPreS
  unfold genHeapInterp allPoints pointsTo
  iintro ⟨⟨%metadata,%hdom,Hauth,Hmeta⟩,Hpts⟩
  imod ghost_map_update_big (store s) (store t) (store_dom_eq hlen) $$ Hauth Hpts
    with ⟨Hauth,Hpts⟩
  isimp only [Union.union] at Hauth
  isimp only [store_union hlen] at Hauth
  imodintro
  iframe Hpts
  iexists metadata
  iframe Hauth Hmeta
  ipureintro
  intro key hk
  rw [← store_dom_eq hlen]
  exact hdom key hk

/-- This is a closed adequacy bridge with a concrete GF and real initialization.
Its premise receives the actual initial heap's location fragments, not a freely
assumed GS instance with unspecified authority. -/
theorem heap_adequacy (s : Async.State) (e : IrisAsync.Expr)
    (φ : Except Async.Error Async.State → Prop)
    (hwp : ∀ [GS], allPoints s ⊢ WP e {{ v, ⌜φ v⌝ }}) :
    adequate .NotStuck e s (fun v _ => φ v) := by
  apply wp_adequacy (GF := GF) .NotStuck e s φ
  intro inv obs
  imod genHeap_init (GF := GF) (H := HeapF) (store s) with ⟨%heap,Hinterp,Hpts,_⟩
  letI : GS := ⟨inv,heap⟩
  imodintro
  iexists (fun s (_ : List Unit) => genHeapInterp (store s)), (fun _ => iprop(True))
  isplitl [Hinterp]
  · iexact Hinterp
  · ihave Hinitial : allPoints s $$ [Hpts]
    · unfold allPoints
      iexact Hpts
    ihave Hwp := (@hwp _) $$ Hinitial
    iexact Hwp

theorem allPoints_buffer [GS] {s : Async.State} {bid : Nat} {b : Async.Buffer}
    (hb : s.buffers[bid]? = some b) : allPoints s ⊢ buffer bid (.own 1) b := by
  unfold allPoints buffer
  exact BigSepM.bigSepM_lookup (buffer_lookup.mpr hb)

end
end Ptx.AsyncHeap
