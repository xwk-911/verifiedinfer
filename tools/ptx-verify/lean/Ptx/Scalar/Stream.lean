import Ptx.Scalar.Checked
import Ptx.Scalar.Memory
import Ptx.Scalar.IntegerMemory
import Ptx.Event.Publication

/-! Completed kernel launches on one ordered stream in the current model.
Only global bytes persist; each invocation supplies its own shared initialization.
Publication covers every actual global write, and the successor receives that
published map, never an arbitrary observer value outside its finite domain.
This models a completed API boundary; CUDA runtime/full PTX correspondence and
concurrent kernels are not proved by these relational rules. -/
namespace Ptx.Scalar.Stream
open Ptx.ISA
noncomputable section

abbrev Heap := Nat → Symbolic.Byte
abbrev SharedInitial := Dim3 → Nat → Symbolic.Byte

structure Invocation where
  code : List Scalar.Instr
  geometry : Geometry
  params : Bindings
  shared : SharedInitial
  domain : List Location

def initial (heap : Heap) (shared : SharedInitial) (loc : Location) : Symbolic.Byte :=
  match loc.space with | .global => heap loc.address | .shared cta => shared cta loc.address

def Invocation.launch (inv : Invocation) (heap : Heap) : Scalar.Launch :=
  ⟨inv.geometry,inv.params,initial heap inv.shared⟩

def publish (heap : Heap) (o : Scalar.Observation) (address : Nat) : Symbolic.Byte :=
  if (⟨.global,address⟩ : Location) ∈ o.domain then o.output ⟨.global,address⟩ else heap address

@[simp] theorem initial_global (heap : Heap) (shared : SharedInitial) (address : Nat) :
    initial heap shared ⟨.global,address⟩ = heap address := rfl
@[simp] theorem initial_shared (heap : Heap) (shared : SharedInitial) (cta : Dim3) (address : Nat) :
    initial heap shared ⟨.shared cta,address⟩ = shared cta address := rfl

theorem publish_on {heap : Heap} {o : Scalar.Observation} {address : Nat}
    (hm : (⟨.global,address⟩ : Location) ∈ o.domain) : publish heap o address = o.output ⟨.global,address⟩ := by
  simp [publish,hm]
theorem publish_outside {heap : Heap} {o : Scalar.Observation} {address : Nat}
    (hm : (⟨.global,address⟩ : Location) ∉ o.domain) : publish heap o address = heap address := by
  simp [publish,hm]

def Represents (format : Symbolic.Format) (heap : Heap) (base : Nat) (value : ℝ) : Prop :=
  ∀ offset, offset < format.bytes → heap (base+offset) = .realPart format value offset

@[simp] theorem represents_initial (format : Symbolic.Format) (heap : Heap) (shared : SharedInitial) (base : Nat) (value : ℝ) :
    Scalar.RepresentsReal format (initial heap shared) ⟨.global,base⟩ value ↔ Represents format heap base value := Iff.rfl

theorem publish_represents {format : Symbolic.Format} {heap : Heap} {o : Scalar.Observation} {base : Nat} {value : ℝ}
    (hr : Scalar.RepresentsReal format o.output ⟨.global,base⟩ value)
    (hd : ∀ offset, offset < format.bytes → (⟨.global,base+offset⟩ : Location) ∈ o.domain) :
    Represents format (publish heap o) base value := by
  intro offset ho
  rw [publish_on (hd offset ho)]
  exact hr offset ho

def RepresentsWord (heap : Heap) (base value : Nat) : Prop :=
  ∀ offset, offset < 4 → heap (base+offset) = u32Byte value offset

@[simp] theorem represents_word_initial (heap : Heap) (shared : SharedInitial) (base value : Nat) :
    Scalar.RepresentsU32 (initial heap shared) ⟨.global,base⟩ value ↔ RepresentsWord heap base value := Iff.rfl

theorem publish_word {heap : Heap} {o : Scalar.Observation} {base value : Nat}
    (hr : Scalar.RepresentsU32 o.output ⟨.global,base⟩ value)
    (hd : ∀ offset, offset < 4 → (⟨.global,base+offset⟩ : Location) ∈ o.domain) :
    RepresentsWord (publish heap o) base value := by
  intro offset ho
  rw [publish_on (hd offset ho)]
  exact hr offset ho

structure Completed (inv : Invocation) (heap : Heap) where
  candidate : Scalar.Candidate
  rf : Event.ReadsFrom
  co : Event.Coherence
  observation : Scalar.Observation
  checked : Scalar.CheckedConditions inv.code (inv.launch heap) candidate rf co
  observed : Event.ObserverConditions candidate (inv.launch heap).initial rf co observation
  domain : observation.domain = inv.domain
  writes : Event.CoversGlobalWrites candidate inv.domain

theorem Completed.publication_observed {inv : Invocation} {heap : Heap} (done : Completed inv heap)
    (domain : List Location) (hg : ∀ loc ∈ domain, loc.space = .global) :
    Event.ObserverConditions done.candidate (inv.launch heap).initial done.rf done.co
      (Event.publication (inv.launch heap).initial done.observation domain) :=
  Event.publication_observed done.observed (done.domain ▸ done.writes) hg

theorem Completed.published_global {inv : Invocation} {heap : Heap} (done : Completed inv heap) (address : Nat) :
    Event.published (inv.launch heap).initial done.observation ⟨.global,address⟩ =
      publish heap done.observation address := rfl

def Step (inv : Invocation) (before after : Heap) : Prop :=
  ∃ done : Completed inv before, after = publish before done.observation

inductive Runs : List Invocation → Heap → Heap → Prop
  | nil (heap) : Runs [] heap heap
  | cons {inv rest before mid after} : Step inv before mid → Runs rest mid after → Runs (inv::rest) before after

theorem runs_single {inv before after} : Runs [inv] before after ↔ Step inv before after := by
  constructor
  · intro h
    cases h with
    | cons hs ht => cases ht; exact hs
  · intro h; exact .cons h (.nil _)

theorem runs_append {first rest before mid after}
    (hf : Runs first before mid) (hr : Runs rest mid after) : Runs (first++rest) before after := by
  induction hf with
  | nil => exact hr
  | cons hs _ ih => exact .cons hs (ih hr)

theorem runs_split {first rest before after} (h : Runs (first++rest) before after) :
    ∃ mid, Runs first before mid ∧ Runs rest mid after := by
  induction first generalizing before with
  | nil => exact ⟨before,.nil _,h⟩
  | cons inv tail ih =>
    cases h with
    | cons hs ht =>
      obtain ⟨mid,hfirst,hrest⟩ := ih ht
      exact ⟨mid,.cons hs hfirst,hrest⟩

def Triple (invocations : List Invocation) (pre : Heap → Prop) (post : Heap → Heap → Prop) : Prop :=
  ∀ before after, pre before → Runs invocations before after → post before after
def Nonvacuous (invocations : List Invocation) (pre : Heap → Prop) : Prop :=
  ∀ before, pre before → ∃ after, Runs invocations before after

theorem triple_consequence {commands pre post pre' post'} (hc : Triple commands pre post)
    (hp : ∀ heap, pre' heap → pre heap) (hq : ∀ before after, pre' before → post before after → post' before after) :
    Triple commands pre' post' := by
  intro before after hpre hr
  exact hq before after hpre (hc before after (hp before hpre) hr)

theorem triple_append {first rest pre mid post}
    (hf : Triple first pre mid) (hr : ∀ before, pre before → Triple rest (mid before) (fun _ after => post before after)) :
    Triple (first++rest) pre post := by
  intro before after hp hex
  obtain ⟨intermediate,hfirst,hrest⟩ := runs_split hex
  exact hr before hp intermediate after (hf before intermediate hp hfirst) hrest

theorem nonvacuous_append {first rest pre mid}
    (hn : Nonvacuous first pre) (hf : Triple first pre mid)
    (hr : ∀ before, pre before → Nonvacuous rest (mid before)) : Nonvacuous (first++rest) pre := by
  intro before hp
  obtain ⟨intermediate,hfirst⟩ := hn before hp
  obtain ⟨after,hrest⟩ := hr before hp intermediate (hf before intermediate hp hfirst)
  exact ⟨after,runs_append hfirst hrest⟩

theorem single_correct (inv : Invocation) {pre : Heap → Prop} {post : Heap → Heap → Prop}
    {kernelPre : Scalar.Launch → Prop} {kernelPost : Scalar.Launch → Scalar.ByteMap → Prop}
    (hk : Scalar.CheckedTriple inv.code kernelPre (fun _ => inv.domain) kernelPost)
    (hp : ∀ heap, pre heap → kernelPre (inv.launch heap))
    (hq : ∀ (heap : Heap) (o : Scalar.Observation), pre heap → o.domain = inv.domain → kernelPost (inv.launch heap) o.output →
      post heap (publish heap o)) : Triple [inv] pre post := by
  intro before after hpre hr
  obtain ⟨done,rfl⟩ := runs_single.mp hr
  exact hq before done.observation hpre done.domain
    (Scalar.checked_apply hk (hp before hpre) done.checked done.observed done.domain)

theorem single_nonvacuous (inv : Invocation) {pre : Heap → Prop} {kernelPre : Scalar.Launch → Prop}
    (hn : Scalar.CheckedNonvacuous inv.code kernelPre (fun _ => inv.domain))
    (hp : ∀ heap, pre heap → kernelPre (inv.launch heap))
    (hw : ∀ heap c rf co o, pre heap → Scalar.CheckedConditions inv.code (inv.launch heap) c rf co →
      Event.ObserverConditions c (inv.launch heap).initial rf co o → o.domain = inv.domain →
      Event.CoversGlobalWrites c inv.domain) : Nonvacuous [inv] pre := by
  intro before hpre
  obtain ⟨c,rf,co,o,hchecked,hobs,hdomain⟩ := hn (inv.launch before) (hp before hpre)
  let done : Completed inv before := ⟨c,rf,co,o,hchecked,hobs,hdomain,hw before c rf co o hpre hchecked hobs hdomain⟩
  exact ⟨publish before o,runs_single.mpr ⟨done,rfl⟩⟩

end
end Ptx.Scalar.Stream
