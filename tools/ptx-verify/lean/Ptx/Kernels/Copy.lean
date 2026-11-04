import Ptx.Generated.Copy
import Ptx.Rules.Permissions

/-! External specification of the real generated copy kernel. Array bases below
are cell indices; PTX pointers are their byte addresses. Length, launch size, input
words, disjoint layouts and initial destination/frame contents are parameters.
The explicit bounds rule out u32 index and u64 pointer wrap, not floating error.
-/
namespace Ptx.CopyContract
open Permissions
abbrev code := Generated.copy.program
def word (x : Nat) := wrap 32 x

structure Config where
  src : Nat
  dst : Nat
  n : Nat
  count : Nat
  input : Nat → Nat
  before : List (Option Nat)
  coverage : n ≤ count
  count32 : count < 2^32
  src64 : 4 * (src+n) < 2^64
  dst64 : 4 * (dst+n) < 2^64
  srcBound : src+n ≤ before.length
  dstBound : dst+n ≤ before.length
  disjoint : src+n ≤ dst ∨ dst+n ≤ src
  initialized : ∀ i, i < n → before[src+i]? = some (some (word (input i)))

def Params (c : Config) (xs : Bindings) : Prop :=
  lookup "src" xs = some (4*c.src) ∧ lookup "dst" xs = some (4*c.dst) ∧
  lookup "n" xs = some c.n

def ThreadInv (c : Config) (tid : Nat) (t : Thread) : Prop :=
  (t.status = .running ∨ t.status = .done) ∧ t.pc ≤ 11 ∧
  (t.status = .done → t.pc = 11) ∧
  (1 ≤ t.pc → lookup "%rd0" t.regs = some (4*c.src)) ∧
  (2 ≤ t.pc → lookup "%rd1" t.regs = some (4*c.dst)) ∧
  (3 ≤ t.pc → lookup "%r0" t.regs = some c.n) ∧
  (4 ≤ t.pc → lookup "%r1" t.regs = some tid) ∧
  (5 ≤ t.pc → lookup "%p" t.regs = some (if tid ≥ c.n then 1 else 0)) ∧
  (6 ≤ t.pc → t.pc ≤ 10 → tid < c.n) ∧
  (7 ≤ t.pc → t.pc ≤ 10 → lookup "%rd2" t.regs = some (4*tid)) ∧
  (8 ≤ t.pc → t.pc ≤ 10 → lookup "%rd3" t.regs = some (4*(c.src+tid))) ∧
  (9 ≤ t.pc → t.pc ≤ 10 → lookup "%rd4" t.regs = some (4*(c.dst+tid))) ∧
  (t.pc = 10 → lookup "%r2" t.regs = some (word (c.input tid)))

theorem wrap_small {w x : Nat} (h : x < 2^w) : wrap w x = x := Nat.mod_eq_of_lt h
@[simp] theorem word_word (x : Nat) : word (word x) = word x := by simp [word,wrap]

theorem tid32 (c : Config) {tid} (h : tid < c.count) : wrap 32 tid = tid :=
  wrap_small (by have := c.count32; omega)
theorem n32 (c : Config) : wrap 32 c.n = c.n :=
  wrap_small (by have := c.coverage; have := c.count32; omega)
theorem src64 (c : Config) : wrap 64 (4*c.src) = 4*c.src :=
  wrap_small (by have := c.src64; omega)
theorem dst64 (c : Config) : wrap 64 (4*c.dst) = 4*c.dst :=
  wrap_small (by have := c.dst64; omega)
theorem offset64 (c : Config) {tid} (ht : tid < c.count) : wrap 64 (4*tid) = 4*tid := by
  apply wrap_small
  have hc := c.count32
  have h : 4 * 2^32 < 2^64 := by decide
  omega
theorem srcAddr64 (c : Config) {tid} (ht : tid < c.n) :
    wrap 64 (4*(c.src+tid)) = 4*(c.src+tid) := wrap_small (by have := c.src64; omega)
theorem dstAddr64 (c : Config) {tid} (ht : tid < c.n) :
    wrap 64 (4*(c.dst+tid)) = 4*(c.dst+tid) := wrap_small (by have := c.dst64; omega)

/-- Every non-memory instruction both executes and preserves its register contract.
For active threads a local instruction cannot newly commit an output: only the
actual store instruction may do that. -/
theorem local_step (c : Config) {tid t params} (htid : tid < c.count)
    (hp : Params c params) (hi : ThreadInv c tid t) (hr : t.status = .running)
    (h9 : t.pc ≠ 9) (h10 : t.pc ≠ 10) :
    ∃ i t', code[t.pc]? = some i ∧ isLocal i = true ∧
      localStep params tid t i = .ok t' ∧ ThreadInv c tid t' ∧
      (tid < c.n → t'.pc = 11 → t.pc = 11) := by
  have hle := hi.2.1
  rcases hp with ⟨hsrc,hdst,hn⟩
  match hpc : t.pc with
  | 0 =>
    refine ⟨.param 64 "%rd0" "src", assign t "%rd0" (4*c.src), ?_, rfl, ?_, ?_, ?_⟩
    · simp [code,Generated.copy.program]
    · simp [localStep,hsrc,src64,bind,Except.bind,pure,Except.pure]
    · simp_all [ThreadInv,assign,advance]
    · simp [assign,advance,hpc]
  | 1 =>
    refine ⟨.param 64 "%rd1" "dst", assign t "%rd1" (4*c.dst), ?_, rfl, ?_, ?_, ?_⟩
    · simp [code,Generated.copy.program]
    · simp [localStep,hdst,dst64,bind,Except.bind,pure,Except.pure]
    · simp_all [ThreadInv,assign,advance]
    · simp [assign,advance,hpc]
  | 2 =>
    refine ⟨.param 32 "%r0" "n", assign t "%r0" c.n, ?_, rfl, ?_, ?_, ?_⟩
    · simp [code,Generated.copy.program]
    · simp [localStep,hn,n32,bind,Except.bind,pure,Except.pure]
    · simp_all [ThreadInv,assign,advance]
    · simp [assign,advance,hpc]
  | 3 =>
    refine ⟨.mov 32 "%r1" .tid, assign t "%r1" tid, ?_, rfl, ?_, ?_, ?_⟩
    · simp [code,Generated.copy.program]
    · simp [localStep,eval,tid32 c htid,bind,Except.bind,pure,Except.pure]
    · simp_all [ThreadInv,assign,advance]
    · simp [assign,advance,hpc]
  | 4 =>
    have hv : lookup "%r1" t.regs = some tid := hi.2.2.2.2.2.2.1 (by omega)
    have hn' : lookup "%r0" t.regs = some c.n := hi.2.2.2.2.2.1 (by omega)
    refine ⟨.setp .ge "%p" (.reg "%r1") (.reg "%r0"),
      assign t "%p" (if tid ≥ c.n then 1 else 0), ?_, rfl, ?_, ?_, ?_⟩
    · simp [code,Generated.copy.program]
    · simp [localStep,eval,hv,hn',tid32 c htid,n32,bind,Except.bind,pure,Except.pure]
    · simp_all [ThreadInv,assign,advance]
    · simp [assign,advance,hpc]
  | 5 =>
    have hp' : lookup "%p" t.regs = some (if tid ≥ c.n then 1 else 0) := hi.2.2.2.2.2.2.2.1 (by omega)
    by_cases hactive : tid < c.n
    · refine ⟨.branch "%p" true 11, {t with pc := 6}, ?_, rfl, ?_, ?_, ?_⟩
      · simp [code,Generated.copy.program]
      · simp [localStep,hp',Nat.not_le_of_lt hactive,hpc,bind,Except.bind,pure,Except.pure]
      · simp_all [ThreadInv]
      · simp
    · refine ⟨.branch "%p" true 11, {t with pc := 11}, ?_, rfl, ?_, ?_, ?_⟩
      · simp [code,Generated.copy.program]
      · simp [localStep,hp',Nat.le_of_not_gt hactive,bind,Except.bind,pure,Except.pure]
      · simp_all [ThreadInv]
      · exact fun h => (hactive h).elim
  | 6 =>
    have hv : lookup "%r1" t.regs = some tid := hi.2.2.2.2.2.2.1 (by omega)
    have hwide : wrap 64 (tid*4) = tid*4 := by simpa [Nat.mul_comm] using offset64 c htid
    refine ⟨.bin .mul 32 64 "%rd2" (.reg "%r1") (.imm 4), assign t "%rd2" (4*tid), ?_, rfl, ?_, ?_, ?_⟩
    · simp [code,Generated.copy.program]
    · simp [localStep,eval,hv,tid32 c htid,wrap_small (by decide : 4 < 2^32),
        Nat.mul_comm,hwide,bind,Except.bind,pure,Except.pure]
    · simp_all [ThreadInv,assign,advance]
    · simp [assign,advance,hpc]
  | 7 =>
    have hactive : tid < c.n := hi.2.2.2.2.2.2.2.2.1 (by omega) (by omega)
    have hsrc' : lookup "%rd0" t.regs = some (4*c.src) := hi.2.2.2.1 (by omega)
    have hoff : lookup "%rd2" t.regs = some (4*tid) := hi.2.2.2.2.2.2.2.2.2.1 (by omega) (by omega)
    refine ⟨.bin .add 64 64 "%rd3" (.reg "%rd0") (.reg "%rd2"), assign t "%rd3" (4*(c.src+tid)), ?_, rfl, ?_, ?_, ?_⟩
    · simp [code,Generated.copy.program]
    · simp [localStep,eval,hsrc',hoff,src64,offset64 c htid,← Nat.mul_add,srcAddr64 c hactive,
        bind,Except.bind,pure,Except.pure]
    · simp_all [ThreadInv,assign,advance]
    · simp [assign,advance,hpc]
  | 8 =>
    have hactive : tid < c.n := hi.2.2.2.2.2.2.2.2.1 (by omega) (by omega)
    have hdst' : lookup "%rd1" t.regs = some (4*c.dst) := hi.2.2.2.2.1 (by omega)
    have hoff : lookup "%rd2" t.regs = some (4*tid) := hi.2.2.2.2.2.2.2.2.2.1 (by omega) (by omega)
    refine ⟨.bin .add 64 64 "%rd4" (.reg "%rd1") (.reg "%rd2"), assign t "%rd4" (4*(c.dst+tid)), ?_, rfl, ?_, ?_, ?_⟩
    · simp [code,Generated.copy.program]
    · simp [localStep,eval,hdst',hoff,dst64,offset64 c htid,← Nat.mul_add,dstAddr64 c hactive,
        bind,Except.bind,pure,Except.pure]
    · simp_all [ThreadInv,assign,advance]
    · simp [assign,advance,hpc]
  | 9 => exact (h9 hpc).elim
  | 10 => exact (h10 hpc).elim
  | 11 =>
    refine ⟨.ret, {t with status := .done}, ?_, rfl, rfl, ?_, ?_⟩
    · simp [code,Generated.copy.program]
    · simp_all [ThreadInv]
    · simp [hpc]
  | _ + 12 => omega

def owner (c : Config) (_ : Space) (addr : Nat) : Nat :=
  if c.src ≤ addr/4 ∧ addr/4 < c.src+c.n then addr/4-c.src else addr/4-c.dst
def ledger (c : Config) := ownerLedger (owner c)

theorem source_share (c : Config) {tid} (ht : tid < c.n) :
    (ledger c).share tid .global (4*(c.src+tid)) = 1 := by
  have hdiv : 4*(c.src+tid)/4 = c.src+tid := by omega
  have hin : c.src ≤ c.src+tid ∧ c.src+tid < c.src+c.n := by omega
  simp [ledger,ownerLedger,owner,hdiv,hin]

theorem destination_share (c : Config) {tid} (ht : tid < c.n) :
    (ledger c).share tid .global (4*(c.dst+tid)) = 1 := by
  have hdiv : 4*(c.dst+tid)/4 = c.dst+tid := by omega
  have hout : ¬ (c.src ≤ c.dst+tid ∧ c.dst+tid < c.src+c.n) := by
    rcases c.disjoint with h | h <;> omega
  simp [ledger,ownerLedger,owner,hdiv,hout]

def Outside (c : Config) (j : Nat) : Prop := j < c.dst ∨ c.dst+c.n ≤ j

structure Inv (c : Config) (m : Machine) : Prop where
  count : m.threads.length = c.count
  size : m.globalMem.length = c.before.length
  params : Params c m.params
  threads : ∀ tid t, m.threads[tid]? = some t → ThreadInv c tid t
  frame : ∀ j, Outside c j → m.globalMem[j]? = c.before[j]?
  committed : ∀ tid t, m.threads[tid]? = some t → tid < c.n → t.pc = 11 →
    m.globalMem[c.dst+tid]? = some (some (word (c.input tid)))
  history : HistoryOwned (ledger c) m

theorem source_value {c m} (hi : Inv c m) {tid} (ht : tid < c.n) :
    m.globalMem[c.src+tid]? = some (some (word (c.input tid))) := by
  have hout : Outside c (c.src+tid) := by
    rcases c.disjoint with h | h
    · left; omega
    · right; omega
  rw [hi.frame _ hout]
  exact c.initialized tid ht

/-- Changing a thread needs a value proof for any output it marks committed.
Other threads' commitments are retained at their original indices. -/
theorem inv_update {c m tid t'} (hi : Inv c m) (htid : tid < c.count)
    (hit : ThreadInv c tid t')
    (hcommit : tid < c.n → t'.pc = 11 →
      m.globalMem[c.dst+tid]? = some (some (word (c.input tid)))) :
    Inv c (updateThread m tid t') := by
  have hlt : tid < m.threads.length := by simpa [hi.count] using htid
  refine { count := by simpa [updateThread] using hi.count
           size := hi.size, params := hi.params, frame := hi.frame, history := hi.history
           threads := ?_, committed := ?_ }
  · intro j t hget
    by_cases hj : j = tid
    · subst j
      have heq : t' = t := by simpa [updateThread,List.getElem?_set_self hlt] using hget
      simpa [← heq] using hit
    · apply hi.threads j t
      simpa [updateThread,List.getElem?_set_ne (Ne.symm hj)] using hget
  · intro j t hget hjn hpc
    by_cases hj : j = tid
    · subst j
      have heq : t' = t := by simpa [updateThread,List.getElem?_set_self hlt] using hget
      exact hcommit hjn (heq ▸ hpc)
    · apply hi.committed j t _ hjn hpc
      simpa [updateThread,List.getElem?_set_ne (Ne.symm hj)] using hget

theorem inv_record {c m a} (hi : Inv c m) (hg : Granted (ledger c) a) :
    Inv c {m with history := a :: m.history} :=
  { hi with history := historyOwned_record hi.history hg }

/-- A real store modifies exactly its destination element; its issuer is still
at PC 10 here, so no earlier commitment is created or erased. -/
theorem inv_write {c m tid t} (hi : Inv c m) (ht : m.threads[tid]? = some t)
    (hpc : t.pc = 10) (hn : tid < c.n) :
    Inv c {m with globalMem := m.globalMem.set (c.dst+tid) (some (word (c.input tid)))} := by
  refine { count := hi.count, size := by simpa using hi.size
           params := hi.params, threads := hi.threads, history := hi.history
           frame := ?_, committed := ?_ }
  · intro j hj
    have hne : c.dst+tid ≠ j := by unfold Outside at hj; omega
    simpa [List.getElem?_set_ne hne] using hi.frame j hj
  · intro j u hget hjn h11
    have hne : c.dst+tid ≠ c.dst+j := by
      intro heq
      have heq' : tid = j := by omega
      subst j
      have hu : t = u := by simpa [ht] using hget
      have : t.pc = 11 := hu ▸ h11
      omega
    simpa [List.getElem?_set_ne hne] using hi.committed j u hget hjn h11

/-- Successful next step, invariant preservation, and the unchanged shared-memory
and epoch frame for any runnable thread, including excess launch threads. -/
theorem thread_rule {c m tid t} (hi : Inv c m)
    (ht : m.threads[tid]? = some t) (hr : t.status = .running) :
    ∃ m', threadStep code tid m = .ok m' ∧ Inv c m' ∧
      m'.sharedMem = m.sharedMem ∧ m'.epoch = m.epoch ∧ m'.params = m.params := by
  have htid : tid < c.count := by
    have hb : tid < m.threads.length := by
      by_cases hb : tid < m.threads.length
      · exact hb
      · have hn : m.threads[tid]? = none := List.getElem?_eq_none_iff.mpr (by omega)
        rw [hn] at ht
        cases ht
    simpa [hi.count] using hb
  have hit := hi.threads tid t ht
  by_cases h9 : t.pc = 9
  · have hactive : tid < c.n := hit.2.2.2.2.2.2.2.2.1 (by omega) (by omega)
    have hreg : lookup "%rd3" t.regs = some (4*(c.src+tid)) :=
      hit.2.2.2.2.2.2.2.2.2.2.1 (by omega) (by omega)
    have heval : evalAddr tid t {base := .reg "%rd3"} = .ok (4*(c.src+tid)) := by
      simp [evalAddr,eval,hreg,srcAddr64 c hactive,bind,Except.bind,pure,Except.pure]
    let a : Access := ⟨.global,4*(c.src+tid),tid,false,m.epoch⟩
    have hg : Granted (ledger c) a := by simp [Granted,a,source_share c hactive]
    have hdiv : 4*(c.src+tid)/4 = c.src+tid := by omega
    have hbound : 4*(c.src+tid)/4 < (memory m .global).length := by
      have hb := c.srcBound
      simp only [memory,hi.size,hdiv]
      omega
    have ha : AccessOK m a := permission_accessOK hi.history hg rfl (by dsimp [a]; omega) hbound
    have hv : (memory m .global)[4*(c.src+tid)/4]? = some (some (word (c.input tid))) := by
      simpa [memory,hdiv] using source_value hi hactive
    have hcode : code[t.pc]? = some (.load .global "%r2" {base := .reg "%rd3"}) := by
      simp [code,Generated.copy.program,h9]
    have hs := threadStep_load ht hr hcode heval ha hv
    have hw : wrap 32 (word (c.input tid)) = word (c.input tid) := word_word _
    have hit' : ThreadInv c tid (assign t "%r2" (word (c.input tid))) := by
      simp_all [ThreadInv,assign,advance]
    have hrec := inv_record hi hg
    have hinv : Inv c (updateThread {m with history := a::m.history} tid
        (assign t "%r2" (word (c.input tid)))) := by
      apply inv_update hrec htid hit'
      simp [assign,advance,h9]
    refine ⟨_,?_,hinv,rfl,rfl,rfl⟩
    simpa only [hw] using hs
  · by_cases h10 : t.pc = 10
    · have hactive : tid < c.n := hit.2.2.2.2.2.2.2.2.1 (by omega) (by omega)
      have hreg : lookup "%rd4" t.regs = some (4*(c.dst+tid)) :=
        hit.2.2.2.2.2.2.2.2.2.2.2.1 (by omega) (by omega)
      have hvalue : lookup "%r2" t.regs = some (word (c.input tid)) :=
        hit.2.2.2.2.2.2.2.2.2.2.2.2 h10
      have heval : evalAddr tid t {base := .reg "%rd4"} = .ok (4*(c.dst+tid)) := by
        simp [evalAddr,eval,hreg,dstAddr64 c hactive,bind,Except.bind,pure,Except.pure]
      have hoperand : eval tid t (.reg "%r2") = .ok (word (c.input tid)) := by simp [eval,hvalue]
      let a : Access := ⟨.global,4*(c.dst+tid),tid,true,m.epoch⟩
      have hg : Granted (ledger c) a := by simp [Granted,a,destination_share c hactive]
      have hdiv : 4*(c.dst+tid)/4 = c.dst+tid := by omega
      have hbound : 4*(c.dst+tid)/4 < (memory m .global).length := by
        have hb := c.dstBound
        simp only [memory,hi.size,hdiv]
        omega
      have ha : AccessOK m a := permission_accessOK hi.history hg rfl (by dsimp [a]; omega) hbound
      have hcode : code[t.pc]? = some (.store .global {base := .reg "%rd4"} (.reg "%r2")) := by
        simp [code,Generated.copy.program,h10]
      have hs := threadStep_store ht hr hcode heval hoperand ha
      have hw : wrap 32 (word (c.input tid)) = word (c.input tid) := word_word _
      have hit' : ThreadInv c tid (advance t) := by simp_all [ThreadInv,advance]
      have hwritten := inv_write hi ht h10 hactive
      have hrecorded := inv_record hwritten hg
      have hinv : Inv c (updateThread
          {m with globalMem := m.globalMem.set (c.dst+tid) (some (word (c.input tid))),
                  history := a::m.history} tid (advance t)) := by
        apply inv_update hrecorded htid hit'
        intro _ _
        apply List.getElem?_set_self
        simpa [memory,hdiv] using hbound
      refine ⟨_,?_,hinv,rfl,rfl,rfl⟩
      simpa [memory,setMemory,hdiv,hw,a] using hs
    · obtain ⟨i,t',hpc,hl,hs,hit',hnocommit⟩ := local_step c htid hi.params hit hr h9 h10
      have hinv : Inv c (updateThread m tid t') := by
        apply inv_update hi htid hit'
        intro hn hpc'
        exact hi.committed tid t ht hn (hnocommit hn hpc')
      refine ⟨_,?_,hinv,rfl,rfl,rfl⟩
      rw [threadStep_local ht hr hpc hl,hs]
      rfl

theorem step_rule {c m m' a} (hi : Inv c m) (hs : step code a m = .ok m') :
    Inv c m' ∧ m'.sharedMem = m.sharedMem ∧ m'.epoch = m.epoch ∧ m'.params = m.params := by
  cases a with
  | thread tid =>
    cases ht : m.threads[tid]? with
    | none => simp [step,threadStep,ht,bind,Except.bind] at hs
    | some t =>
      rcases (hi.threads tid t ht).1 with hr | hd
      · obtain ⟨mid,hmid,hInv,hshared,hepoch,hparams⟩ := thread_rule hi ht hr
        rw [step,hmid] at hs
        cases hs
        exact ⟨hInv,hshared,hepoch,hparams⟩
      · simp [step,threadStep,ht,hd,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs
  | release =>
    cases ht : m.threads.head? with
    | none => simp [step,release,ht,bind,Except.bind] at hs
    | some t =>
      obtain ⟨tid,hget⟩ := List.mem_iff_getElem?.mp (List.mem_of_head? ht)
      rcases (hi.threads tid t hget).1 with hr | hd
      · simp [step,release,ht,hr,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs
      · simp [step,release,ht,hd,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs

theorem invariant (c : Config) : InductiveInvariant code (Inv c) := by
  intro m a m' hi hs
  exact (step_rule hi hs).1

structure Pre (c : Config) (m : Machine) : Prop where
  count : m.threads.length = c.count
  memory : m.globalMem = c.before
  params : Params c m.params
  threads : ∀ t ∈ m.threads, t.pc = 0 ∧ t.status = .running
  history : m.history = []

/-- A witness for every valid configuration, with arbitrary shared memory. -/
def initial (c : Config) (shared : List (Option Nat) := []) : Machine := {
  threads := List.replicate c.count {}
  globalMem := c.before
  sharedMem := shared
  params := [("src",4*c.src),("dst",4*c.dst),("n",c.n)]
}

theorem initial_pre (c : Config) (shared : List (Option Nat)) : Pre c (initial c shared) := by
  refine {count := by simp [initial], memory := rfl, params := ?_, threads := ?_, history := rfl}
  · simp [initial,Params,lookup]
  · intro t ht
    simp only [initial,List.mem_replicate] at ht
    rcases ht with ⟨_,rfl⟩
    exact ⟨rfl,rfl⟩

theorem pre_invariant {c m} (hp : Pre c m) : Inv c m := by
  refine {count := hp.count, size := by simp [hp.memory], params := hp.params
          threads := ?_, frame := ?_, committed := ?_, history := ?_}
  · intro tid t ht
    obtain ⟨hpc,hr⟩ := hp.threads t (List.mem_of_getElem? ht)
    simp [ThreadInv,hpc,hr]
  · intro j _; rw [hp.memory]
  · intro tid t ht _ hpc
    have := (hp.threads t (List.mem_of_getElem? ht)).1
    omega
  · intro a ha _
    simp [hp.history] at ha

/-- All runnable threads are safe after every finite execution from the precondition. -/
theorem safe (c : Config) : Safe code (Pre c) := by
  intro m m' hp hs tid t ht hr
  have hi := invariant_steps (invariant c) hs (pre_invariant hp)
  obtain ⟨next,hnext,_⟩ := thread_rule hi ht hr
  exact ⟨next,hnext⟩

def Post (c : Config) (m : Machine) : Prop :=
  m.globalMem.length = c.before.length ∧ m.threads.length = c.count ∧
  (∀ i, i < c.n → m.globalMem[c.dst+i]? = some (some (word (c.input i)))) ∧
  (∀ j, Outside c j → m.globalMem[j]? = c.before[j]?)

theorem exit_post {c m} (hi : Inv c m)
    (hd : m.threads.all (fun t => t.status == .done) = true) : Post c m := by
  refine ⟨hi.size,hi.count,?_,hi.frame⟩
  intro i hin
  have hlt : i < m.threads.length := by have hc := c.coverage; rw [hi.count]; omega
  let t := m.threads[i]'hlt
  have ht : m.threads[i]? = some t := List.getElem?_eq_getElem hlt
  have hdone : t.status = .done := by
    have := List.all_eq_true.mp hd t (List.mem_of_getElem? ht)
    simpa using this
  have hpc := (hi.threads i t ht).2.2.1 hdone
  exact hi.committed i t ht hin hpc

/-- Exact output words and every cell outside the destination region, for any
finished finite interleaving. The source is unchanged because the regions are disjoint. -/
theorem correct (c : Config) : Triple code (Pre c) (Post c) :=
  invariant_rule (code := code) (P := Pre c) (Q := Post c) (I := Inv c)
    (fun _ hp => pre_invariant hp) (invariant c) (fun _ hi hd => exit_post hi hd)

theorem inv_frame {c m m'} (hi : Inv c m) (hs : Steps code m m') :
    m'.sharedMem = m.sharedMem ∧ m'.epoch = m.epoch ∧ m'.params = m.params := by
  induction hs with
  | refl => exact ⟨rfl,rfl,rfl⟩
  | next a hstep hrest ih =>
    obtain ⟨hinv,hshared,hepoch,hparams⟩ := step_rule hi hstep
    obtain ⟨hshared',hepoch',hparams'⟩ := ih hinv
    exact ⟨hshared'.trans hshared,hepoch'.trans hepoch,hparams'.trans hparams⟩

theorem frame {c m m'} (hp : Pre c m) (hs : Steps code m m') :
    m'.sharedMem = m.sharedMem ∧ m'.epoch = m.epoch ∧ m'.params = m.params :=
  inv_frame (pre_invariant hp) hs

theorem progress {c m m'} (hp : Pre c m) (hs : Steps code m m')
    (hn : m'.threads.all (fun t => t.status == .done) ≠ true) :
    ∃ tid next, threadStep code tid m' = .ok next := by
  have hi := invariant_steps (invariant c) hs (pre_invariant hp)
  have hf : m'.threads.all (fun t => t.status == .done) = false := by
    cases h : m'.threads.all (fun t => t.status == .done)
    · rfl
    · exact (hn h).elim
  obtain ⟨t,ht,hnd⟩ := List.all_eq_false.mp hf
  have hnd : t.status ≠ .done := by simpa using hnd
  obtain ⟨tid,hget⟩ := List.mem_iff_getElem?.mp ht
  have hr : t.status = .running := (hi.threads tid t hget).1.resolve_right hnd
  obtain ⟨next,hnext,_⟩ := thread_rule hi hget hr
  exact ⟨tid,next,hnext⟩

/-- A nonvacuous configuration family for every input array and covering launch:
source followed by an equally sized uninitialized destination. The general
contract above also supports other disjoint layouts and arbitrary frame cells. -/
def contiguous (xs : List Nat) (count : Nat) (hcover : xs.length ≤ count)
    (hcount : count < 2^32) : Config where
  src := 0
  dst := xs.length
  n := xs.length
  count := count
  input i := xs[i]?.getD 0
  before := xs.map (fun v => some (word v)) ++ List.replicate xs.length none
  coverage := hcover
  count32 := hcount
  src64 := by
    have h : 4*2^32 < 2^64 := by decide
    omega
  dst64 := by
    have h : 8*2^32 < 2^64 := by decide
    omega
  srcBound := by simp
  dstBound := by simp
  disjoint := Or.inl (by omega)
  initialized := by
    intro i hi
    have hget : xs[i]? = some (xs[i]'hi) := List.getElem?_eq_getElem hi
    rw [List.getElem?_append_left (by simpa using hi)]
    simp [List.getElem?_map,hget]

end Ptx.CopyContract
