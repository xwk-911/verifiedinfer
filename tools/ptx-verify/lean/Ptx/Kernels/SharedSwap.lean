import Ptx.Generated.SharedSwap
import Ptx.Kernels.Copy

/-! Specification of the actual two-thread shared-memory exchange kernel.
Values and disjoint global layouts are parameters. The CTA has exactly two
threads because the PTX uses 1-tid, not because a schedule is enumerated.
-/
namespace Ptx.SharedContract
open Permissions
open CopyContract (word word_word)
abbrev code := Generated.shared_swap.program

structure Config extends CopyContract.Config where
  n_two : n = 2
  count_two : count = 2

def other (tid : Nat) := 1-tid
theorem other_lt {tid} (h : tid < 2) : other tid < 2 := by unfold other; omega
theorem other_other {tid} (h : tid < 2) : other (other tid) = tid := by unfold other; omega
theorem small32 {n : Nat} (h : n ≤ 8) : wrap 32 n = n := by
  apply CopyContract.wrap_small
  have hb : 8 < 2^32 := by decide
  omega
theorem small64 {n : Nat} (h : n ≤ 8) : wrap 64 n = n := by
  apply CopyContract.wrap_small
  have hb : 8 < 2^64 := by decide
  omega
theorem sub_other {tid} (h : tid < 2) : wrap 32 (1+2^32-tid) = other tid := by
  have hc : tid = 0 ∨ tid = 1 := by omega
  rcases hc with rfl | rfl <;> decide

def Params (c : Config) (xs : Bindings) : Prop :=
  lookup "src" xs = some (4*c.src) ∧ lookup "dst" xs = some (4*c.dst)

def Control (epoch : Nat) (t : Thread) : Prop := t.pc ≤ 16 ∧
  ((t.status = .running ∧ ((t.pc ≤ 10 ∧ epoch = 0) ∨ (11 ≤ t.pc ∧ epoch = 1))) ∨
   (t.status = .waiting 0 ∧ t.pc = 11 ∧ epoch = 0) ∨
   (t.status = .done ∧ t.pc = 16 ∧ epoch = 1))

def Regs (c : Config) (tid : Nat) (t : Thread) : Prop :=
  (1 ≤ t.pc → lookup "%rd0" t.regs = some (4*c.src)) ∧
  (2 ≤ t.pc → lookup "%rd1" t.regs = some (4*c.dst)) ∧
  (3 ≤ t.pc → lookup "%r0" t.regs = some tid) ∧
  (4 ≤ t.pc → t.pc ≤ 12 → lookup "%rd2" t.regs = some (4*tid)) ∧
  (5 ≤ t.pc → lookup "%rd3" t.regs = some (4*(c.src+tid))) ∧
  (6 ≤ t.pc → lookup "%rd4" t.regs = some (4*(c.dst+tid))) ∧
  (7 ≤ t.pc → lookup "%rd5" t.regs = some 0) ∧
  (8 ≤ t.pc → lookup "%rd6" t.regs = some (4*tid)) ∧
  (9 ≤ t.pc → lookup "%r1" t.regs = some (word (c.input tid))) ∧
  (12 ≤ t.pc → lookup "%r2" t.regs = some (other tid)) ∧
  (13 ≤ t.pc → lookup "%rd2" t.regs = some (4*other tid)) ∧
  (14 ≤ t.pc → lookup "%rd7" t.regs = some (4*other tid)) ∧
  (15 ≤ t.pc → lookup "%r3" t.regs = some (word (c.input (other tid))))

def ThreadInv (c : Config) (epoch tid : Nat) (t : Thread) : Prop := Control epoch t ∧ Regs c tid t

theorem running_epoch {c e tid t} (hi : ThreadInv c e tid t) (hr : t.status = .running) :
    (t.pc ≤ 10 ∧ e = 0) ∨ (11 ≤ t.pc ∧ e = 1) := by
  simpa [Control,hr] using hi.1.2

theorem local_step (c : Config) {e tid t params} (htid : tid < 2)
    (hp : Params c params) (hi : ThreadInv c e tid t) (hr : t.status = .running)
    (h8 : t.pc ≠ 8) (h9 : t.pc ≠ 9) (h14 : t.pc ≠ 14) (h15 : t.pc ≠ 15) :
    ∃ i t', code[t.pc]? = some i ∧ isLocal i = true ∧
      localStep params tid t i = .ok t' ∧ ThreadInv c e tid t' ∧
      (10 ≤ t'.pc → 10 ≤ t.pc) ∧ (t'.pc = 16 → t.pc = 16) := by
  have hle := hi.1.1
  have he := running_epoch hi hr
  have htcount : tid < c.toConfig.count := by simpa [c.count_two] using htid
  have htn : tid < c.toConfig.n := by simpa [c.n_two] using htid
  have ht32 : wrap 32 tid = tid := small32 (by omega)
  have hoff : wrap 64 (4*tid) = 4*tid := small64 (by omega)
  have hother32 : wrap 32 (other tid) = other tid := small32 (by have := other_lt htid; omega)
  have hother64 : wrap 64 (4*other tid) = 4*other tid := small64 (by have := other_lt htid; omega)
  rcases hp with ⟨hsrc,hdst⟩
  match hpc : t.pc with
  | 0 =>
    refine ⟨.param 64 "%rd0" "src",assign t "%rd0" (4*c.src),?_,rfl,?_,?_,?_,?_⟩
    · simp [code,Generated.shared_swap.program]
    · simp [localStep,hsrc,CopyContract.src64,bind,Except.bind,pure,Except.pure]
    · simp_all [ThreadInv,Control,Regs,assign,advance]
    · simp [assign,advance,hpc]
    · simp [assign,advance,hpc]
  | 1 =>
    refine ⟨.param 64 "%rd1" "dst",assign t "%rd1" (4*c.dst),?_,rfl,?_,?_,?_,?_⟩
    · simp [code,Generated.shared_swap.program]
    · simp [localStep,hdst,CopyContract.dst64,bind,Except.bind,pure,Except.pure]
    · simp_all [ThreadInv,Control,Regs,assign,advance]
    · simp [assign,advance,hpc]
    · simp [assign,advance,hpc]
  | 2 =>
    refine ⟨.mov 32 "%r0" .tid,assign t "%r0" tid,?_,rfl,?_,?_,?_,?_⟩
    · simp [code,Generated.shared_swap.program]
    · simp [localStep,eval,ht32,bind,Except.bind,pure,Except.pure]
    · simp_all [ThreadInv,Control,Regs,assign,advance]
    · simp [assign,advance,hpc]
    · simp [assign,advance,hpc]
  | 3 =>
    have hv : lookup "%r0" t.regs = some tid := by have := hi.2; simp_all [Regs]
    have hw : wrap 64 (tid*4) = tid*4 := by simpa [Nat.mul_comm] using hoff
    refine ⟨.bin .mul 32 64 "%rd2" (.reg "%r0") (.imm 4),assign t "%rd2" (4*tid),?_,rfl,?_,?_,?_,?_⟩
    · simp [code,Generated.shared_swap.program]
    · simp [localStep,eval,hv,ht32,small32 (by decide : 4 ≤ 8),Nat.mul_comm,hw,bind,Except.bind,pure,Except.pure]
    · simp_all [ThreadInv,Control,Regs,assign,advance]
    · simp [assign,advance,hpc]
    · simp [assign,advance,hpc]
  | 4 =>
    have hb : lookup "%rd0" t.regs = some (4*c.src) := by have := hi.2; simp_all [Regs]
    have ho : lookup "%rd2" t.regs = some (4*tid) := by have := hi.2; simp_all [Regs]
    refine ⟨.bin .add 64 64 "%rd3" (.reg "%rd0") (.reg "%rd2"),assign t "%rd3" (4*(c.src+tid)),?_,rfl,?_,?_,?_,?_⟩
    · simp [code,Generated.shared_swap.program]
    · simp [localStep,eval,hb,ho,hoff,CopyContract.src64,← Nat.mul_add,
        CopyContract.srcAddr64 c.toConfig htn,bind,Except.bind,pure,Except.pure]
    · simp_all [ThreadInv,Control,Regs,assign,advance]
    · simp [assign,advance,hpc]
    · simp [assign,advance,hpc]
  | 5 =>
    have hb : lookup "%rd1" t.regs = some (4*c.dst) := by have := hi.2; simp_all [Regs]
    have ho : lookup "%rd2" t.regs = some (4*tid) := by have := hi.2; simp_all [Regs]
    refine ⟨.bin .add 64 64 "%rd4" (.reg "%rd1") (.reg "%rd2"),assign t "%rd4" (4*(c.dst+tid)),?_,rfl,?_,?_,?_,?_⟩
    · simp [code,Generated.shared_swap.program]
    · simp [localStep,eval,hb,ho,hoff,CopyContract.dst64,← Nat.mul_add,
        CopyContract.dstAddr64 c.toConfig htn,bind,Except.bind,pure,Except.pure]
    · simp_all [ThreadInv,Control,Regs,assign,advance]
    · simp [assign,advance,hpc]
    · simp [assign,advance,hpc]
  | 6 =>
    refine ⟨.mov 64 "%rd5" (.imm 0),assign t "%rd5" 0,?_,rfl,?_,?_,?_,?_⟩
    · simp [code,Generated.shared_swap.program]
    · simp [localStep,eval,wrap,bind,Except.bind,pure,Except.pure]
    · simp_all [ThreadInv,Control,Regs,assign,advance]
    · simp [assign,advance,hpc]
    · simp [assign,advance,hpc]
  | 7 =>
    have hb : lookup "%rd5" t.regs = some 0 := by have := hi.2; simp_all [Regs]
    have ho : lookup "%rd2" t.regs = some (4*tid) := by have := hi.2; simp_all [Regs]
    refine ⟨.bin .add 64 64 "%rd6" (.reg "%rd5") (.reg "%rd2"),assign t "%rd6" (4*tid),?_,rfl,?_,?_,?_,?_⟩
    · simp [code,Generated.shared_swap.program]
    · simp [localStep,eval,hb,ho,hoff,small64 (by decide : 0 ≤ 8),bind,Except.bind,pure,Except.pure]
    · simp_all [ThreadInv,Control,Regs,assign,advance]
    · simp [assign,advance,hpc]
    · simp [assign,advance,hpc]
  | 8 => exact (h8 hpc).elim
  | 9 => exact (h9 hpc).elim
  | 10 =>
    refine ⟨.barrier 0,{advance t with status := .waiting 0},?_,rfl,rfl,?_,?_,?_⟩
    · simp [code,Generated.shared_swap.program]
    · simp_all [ThreadInv,Control,Regs,advance]
    · simp [advance,hpc]
    · simp [advance,hpc]
  | 11 =>
    have hv : lookup "%r0" t.regs = some tid := by have := hi.2; simp_all [Regs]
    have hsub : wrap 32 (4294967297-tid) = other tid := sub_other htid
    refine ⟨.bin .sub 32 32 "%r2" (.imm 1) (.reg "%r0"),assign t "%r2" (other tid),?_,rfl,?_,?_,?_,?_⟩
    · simp [code,Generated.shared_swap.program]
    · simp [localStep,eval,hv,ht32,small32 (by decide : 1 ≤ 8),hsub,bind,Except.bind,pure,Except.pure]
    · simp_all [ThreadInv,Control,Regs,assign,advance]
    · simp [assign,advance,hpc]
    · simp [assign,advance,hpc]
  | 12 =>
    have hv : lookup "%r2" t.regs = some (other tid) := by have := hi.2; simp_all [Regs]
    refine ⟨.bin .mul 32 64 "%rd2" (.reg "%r2") (.imm 4),assign t "%rd2" (4*other tid),?_,rfl,?_,?_,?_,?_⟩
    · simp [code,Generated.shared_swap.program]
    · simp [localStep,eval,hv,hother32,small32 (by decide : 4 ≤ 8),Nat.mul_comm,hother64,bind,Except.bind,pure,Except.pure]
    · simp_all [ThreadInv,Control,Regs,assign,advance]
    · simp [assign,advance,hpc]
    · simp [assign,advance,hpc]
  | 13 =>
    have hb : lookup "%rd5" t.regs = some 0 := by have := hi.2; simp_all [Regs]
    have ho : lookup "%rd2" t.regs = some (4*other tid) := by have := hi.2; simp_all [Regs]
    refine ⟨.bin .add 64 64 "%rd7" (.reg "%rd5") (.reg "%rd2"),assign t "%rd7" (4*other tid),?_,rfl,?_,?_,?_,?_⟩
    · simp [code,Generated.shared_swap.program]
    · simp [localStep,eval,hb,ho,hother64,small64 (by decide : 0 ≤ 8),bind,Except.bind,pure,Except.pure]
    · simp_all [ThreadInv,Control,Regs,assign,advance]
    · simp [assign,advance,hpc]
    · simp [assign,advance,hpc]
  | 14 => exact (h14 hpc).elim
  | 15 => exact (h15 hpc).elim
  | 16 =>
    refine ⟨.ret,{t with status := .done},?_,rfl,rfl,?_,?_,?_⟩
    · simp [code,Generated.shared_swap.program]
    · simp_all [ThreadInv,Control,Regs]
    · simp [hpc]
    · simp [hpc]
  | _ + 17 => omega

def owner (c : Config) (epoch : Nat) (space : Space) (addr : Nat) : Nat :=
  match space with
  | .global => CopyContract.owner c.toConfig .global addr
  | .shared => if epoch = 0 then addr/4 else other (addr/4)
def ledger (c : Config) (epoch : Nat) := ownerLedger (owner c epoch)

theorem source_share (c : Config) (e : Nat) {tid} (ht : tid < 2) :
    (ledger c e).share tid .global (4*(c.src+tid)) = 1 := by
  have hn : tid < c.n := by simpa [c.n_two] using ht
  have ho : CopyContract.owner c.toConfig .global (4*(c.src+tid)) = tid := by
    simpa [CopyContract.ledger,ownerLedger] using CopyContract.source_share c.toConfig hn
  simp [ledger,ownerLedger,owner,ho]
theorem destination_share (c : Config) (e : Nat) {tid} (ht : tid < 2) :
    (ledger c e).share tid .global (4*(c.dst+tid)) = 1 := by
  have hn : tid < c.n := by simpa [c.n_two] using ht
  have ho : CopyContract.owner c.toConfig .global (4*(c.dst+tid)) = tid := by
    simpa [CopyContract.ledger,ownerLedger] using CopyContract.destination_share c.toConfig hn
  simp [ledger,ownerLedger,owner,ho]
theorem shared_write_share (c : Config) {tid : Nat} :
    (ledger c 0).share tid .shared (4*tid) = 1 := by
  have hd : 4*tid/4 = tid := by omega
  simp [ledger,ownerLedger,owner,hd]
theorem shared_read_share (c : Config) {tid} (ht : tid < 2) :
    (ledger c 1).share tid .shared (4*other tid) = 1 := by
  have hd : 4*other tid/4 = other tid := by omega
  simp [ledger,ownerLedger,owner,hd,other_other ht]

structure Inv (c : Config) (m : Machine) : Prop where
  count : m.threads.length = 2
  size : m.globalMem.length = c.before.length
  sharedSize : m.sharedMem.length = Generated.shared_swap.sharedBytes / 4
  params : Params c m.params
  phase : m.epoch ≤ 1
  threads : ∀ tid t, m.threads[tid]? = some t → ThreadInv c m.epoch tid t
  frame : ∀ j, CopyContract.Outside c.toConfig j → m.globalMem[j]? = c.before[j]?
  staged : ∀ tid t, m.threads[tid]? = some t → 10 ≤ t.pc →
    m.sharedMem[tid]? = some (some (word (c.input tid)))
  committed : ∀ tid t, m.threads[tid]? = some t → t.pc = 16 →
    m.globalMem[c.dst+tid]? = some (some (word (c.input (other tid))))
  history : HistoryOwned (ledger c m.epoch) m
  past : HistoryPast m

theorem index_lt {c m tid t} (hi : Inv c m) (ht : m.threads[tid]? = some t) : tid < 2 := by
  obtain ⟨hb,_⟩ := List.getElem?_eq_some_iff.mp ht
  simpa [hi.count] using hb

theorem source_value {c m} (hi : Inv c m) {tid} (ht : tid < 2) :
    m.globalMem[c.src+tid]? = some (some (word (c.input tid))) := by
  have hn : tid < c.n := by simpa [c.n_two] using ht
  have hout : CopyContract.Outside c.toConfig (c.src+tid) := by
    rcases c.disjoint with h | h
    · left; omega
    · right; omega
  rw [hi.frame _ hout]
  exact c.initialized tid hn

theorem after_pc {c e tid t} (hi : ThreadInv c e tid t) (he : e = 1) : 11 ≤ t.pc := by
  rcases hi.1.2 with ⟨_,hp⟩ | ⟨_,_,he0⟩ | ⟨_,hpc,_⟩
  · rcases hp with ⟨_,he0⟩ | ⟨hpc,_⟩ <;> omega
  · omega
  · omega

/-- Every shared value is initialized before the release, derived from all
threads' phase/PC invariants rather than assumed as a barrier postcondition. -/
theorem shared_value {c m} (hi : Inv c m) (he : m.epoch = 1) {idx} (hb : idx < 2) :
    m.sharedMem[idx]? = some (some (word (c.input idx))) := by
  have hlt : idx < m.threads.length := by simpa [hi.count] using hb
  let t := m.threads[idx]'hlt
  have ht : m.threads[idx]? = some t := List.getElem?_eq_getElem hlt
  exact hi.staged idx t ht (by have := after_pc (hi.threads idx t ht) he; omega)

theorem inv_update {c m tid t'} (hi : Inv c m) (htid : tid < 2)
    (hit : ThreadInv c m.epoch tid t')
    (hstaged : 10 ≤ t'.pc → m.sharedMem[tid]? = some (some (word (c.input tid))))
    (hcommit : t'.pc = 16 → m.globalMem[c.dst+tid]? = some (some (word (c.input (other tid))))) :
    Inv c (updateThread m tid t') := by
  have hlt : tid < m.threads.length := by simpa [hi.count] using htid
  refine {count := by simpa [updateThread] using hi.count
          size := hi.size, sharedSize := hi.sharedSize, params := hi.params, phase := hi.phase
          history := hi.history, past := hi.past, frame := hi.frame
          threads := ?_, staged := ?_, committed := ?_}
  · intro j t hget
    by_cases hj : j = tid
    · subst j
      have heq : t' = t := by simpa [updateThread,List.getElem?_set_self hlt] using hget
      simpa [← heq,updateThread] using hit
    · apply hi.threads j t
      simpa [updateThread,List.getElem?_set_ne (Ne.symm hj)] using hget
  · intro j t hget hpc
    by_cases hj : j = tid
    · subst j
      have heq : t' = t := by simpa [updateThread,List.getElem?_set_self hlt] using hget
      exact hstaged (heq ▸ hpc)
    · apply hi.staged j t _ hpc
      simpa [updateThread,List.getElem?_set_ne (Ne.symm hj)] using hget
  · intro j t hget hpc
    by_cases hj : j = tid
    · subst j
      have heq : t' = t := by simpa [updateThread,List.getElem?_set_self hlt] using hget
      exact hcommit (heq ▸ hpc)
    · apply hi.committed j t _ hpc
      simpa [updateThread,List.getElem?_set_ne (Ne.symm hj)] using hget

theorem inv_record {c m a} (hi : Inv c m) (hg : Granted (ledger c m.epoch) a)
    (he : a.epoch = m.epoch) : Inv c {m with history := a::m.history} :=
  {hi with history := historyOwned_record hi.history hg, past := historyPast_record hi.past he}

theorem inv_shared_write {c m tid t} (hi : Inv c m) (ht : m.threads[tid]? = some t)
    (hpc : t.pc = 9) :
    Inv c {m with sharedMem := m.sharedMem.set tid (some (word (c.input tid)))} := by
  refine {count := hi.count, size := hi.size, sharedSize := by simpa using hi.sharedSize
          params := hi.params, phase := hi.phase, threads := hi.threads, frame := hi.frame
          committed := hi.committed, history := hi.history, past := hi.past, staged := ?_}
  intro j u hget h10
  have hne : tid ≠ j := by
    intro heq
    subst j
    have hu : t = u := by simpa [ht] using hget
    have : 10 ≤ t.pc := hu ▸ h10
    omega
  simpa [List.getElem?_set_ne hne] using hi.staged j u hget h10

theorem inv_global_write {c m tid t} (hi : Inv c m) (ht : m.threads[tid]? = some t)
    (hpc : t.pc = 15) (hn : tid < 2) :
    Inv c {m with globalMem := m.globalMem.set (c.dst+tid) (some (word (c.input (other tid))))} := by
  refine {count := hi.count, size := by simpa using hi.size, sharedSize := hi.sharedSize
          params := hi.params, phase := hi.phase, threads := hi.threads, staged := hi.staged
          history := hi.history, past := hi.past, frame := ?_, committed := ?_}
  · intro j hj
    have hne : c.dst+tid ≠ j := by unfold CopyContract.Outside at hj; have := c.n_two; omega
    simpa [List.getElem?_set_ne hne] using hi.frame j hj
  · intro j u hget h16
    have hne : c.dst+tid ≠ c.dst+j := by
      intro heq
      have heq' : tid = j := by omega
      subst j
      have hu : t = u := by simpa [ht] using hget
      have : t.pc = 16 := hu ▸ h16
      omega
    simpa [List.getElem?_set_ne hne] using hi.committed j u hget h16

theorem thread_rule {c m tid t} (hi : Inv c m) (ht : m.threads[tid]? = some t)
    (hr : t.status = .running) :
    ∃ m', threadStep code tid m = .ok m' ∧ Inv c m' ∧
      m'.epoch = m.epoch ∧ m'.params = m.params := by
  have htid := index_lt hi ht
  have hit := hi.threads tid t ht
  have hphase := running_epoch hit hr
  have hn : tid < c.n := by simpa [c.n_two] using htid
  have hshared : m.sharedMem.length = 2 := hi.sharedSize
  by_cases h8 : t.pc = 8
  · have hreg : lookup "%rd3" t.regs = some (4*(c.src+tid)) := by have := hit.2; simp_all [Regs]
    have heval : evalAddr tid t {base := .reg "%rd3"} = .ok (4*(c.src+tid)) := by
      simp [evalAddr,eval,hreg,CopyContract.srcAddr64 c.toConfig hn,bind,Except.bind,pure,Except.pure]
    let a : Access := ⟨.global,4*(c.src+tid),tid,false,m.epoch⟩
    have hg : Granted (ledger c m.epoch) a := by simp [Granted,a,source_share c m.epoch htid]
    have hd : 4*(c.src+tid)/4 = c.src+tid := by omega
    have hb : 4*(c.src+tid)/4 < (memory m .global).length := by
      have := c.srcBound
      simp only [memory,hi.size,hd]
      omega
    have ha : AccessOK m a := permission_accessOK hi.history hg rfl (by dsimp [a]; omega) hb
    have hv : (memory m .global)[4*(c.src+tid)/4]? = some (some (word (c.input tid))) := by
      simpa [memory,hd] using source_value hi htid
    have hcode : code[t.pc]? = some (.load .global "%r1" {base := .reg "%rd3"}) := by
      simp [code,Generated.shared_swap.program,h8]
    have hs := threadStep_load ht hr hcode heval ha hv
    have hw : wrap 32 (word (c.input tid)) = word (c.input tid) := word_word _
    have hit' : ThreadInv c m.epoch tid (assign t "%r1" (word (c.input tid))) := by
      simp_all [ThreadInv,Control,Regs,assign,advance]
    have hinv : Inv c (updateThread {m with history := a::m.history} tid
        (assign t "%r1" (word (c.input tid)))) := by
      apply inv_update (inv_record hi hg rfl) htid hit'
      · simp [assign,advance,h8]
      · simp [assign,advance,h8]
    refine ⟨_,?_,hinv,rfl,rfl⟩
    simpa only [hw] using hs
  · by_cases h9 : t.pc = 9
    · have he : m.epoch = 0 := by omega
      have hreg : lookup "%rd6" t.regs = some (4*tid) := by have := hit.2; simp_all [Regs]
      have hvalue : lookup "%r1" t.regs = some (word (c.input tid)) := by have := hit.2; simp_all [Regs]
      have heval : evalAddr tid t {base := .reg "%rd6"} = .ok (4*tid) := by
        simp [evalAddr,eval,hreg,small64 (by omega : 4*tid ≤ 8),bind,Except.bind,pure,Except.pure]
      have hop : eval tid t (.reg "%r1") = .ok (word (c.input tid)) := by simp [eval,hvalue]
      let a : Access := ⟨.shared,4*tid,tid,true,m.epoch⟩
      have hg : Granted (ledger c m.epoch) a := by simp [Granted,a,he,shared_write_share]
      have hd : 4*tid/4 = tid := by omega
      have hb : 4*tid/4 < (memory m .shared).length := by simp [memory,hshared,hd]; omega
      have ha : AccessOK m a := permission_accessOK hi.history hg rfl (by dsimp [a]; omega) hb
      have hcode : code[t.pc]? = some (.store .shared {base := .reg "%rd6"} (.reg "%r1")) := by
        simp [code,Generated.shared_swap.program,h9]
      have hs := threadStep_store ht hr hcode heval hop ha
      have hw : wrap 32 (word (c.input tid)) = word (c.input tid) := word_word _
      have hit' : ThreadInv c m.epoch tid (advance t) := by simp_all [ThreadInv,Control,Regs,advance]
      have hinv : Inv c (updateThread
          {m with sharedMem := m.sharedMem.set tid (some (word (c.input tid))),history := a::m.history}
          tid (advance t)) := by
        apply inv_update (inv_record (inv_shared_write hi ht h9) hg rfl) htid hit'
        · intro _; exact List.getElem?_set_self (by omega)
        · simp [advance,h9]
      refine ⟨_,?_,hinv,rfl,rfl⟩
      simpa [memory,setMemory,hd,hw,a] using hs
    · by_cases h14 : t.pc = 14
      · have he : m.epoch = 1 := by omega
        have hreg : lookup "%rd7" t.regs = some (4*other tid) := by have := hit.2; simp_all [Regs]
        have heval : evalAddr tid t {base := .reg "%rd7"} = .ok (4*other tid) := by
          have ho := other_lt htid
          simp [evalAddr,eval,hreg,small64 (by omega : 4*other tid ≤ 8),bind,Except.bind,pure,Except.pure]
        let a : Access := ⟨.shared,4*other tid,tid,false,m.epoch⟩
        have hg : Granted (ledger c m.epoch) a := by simp [Granted,a,he,shared_read_share c htid]
        have hd : 4*other tid/4 = other tid := by omega
        have hb : 4*other tid/4 < (memory m .shared).length := by
          simpa [memory,hshared,hd] using other_lt htid
        have ha : AccessOK m a := permission_accessOK hi.history hg rfl (by dsimp [a]; omega) hb
        have hv : (memory m .shared)[4*other tid/4]? = some (some (word (c.input (other tid)))) := by
          simpa [memory,hd] using shared_value hi he (other_lt htid)
        have hcode : code[t.pc]? = some (.load .shared "%r3" {base := .reg "%rd7"}) := by
          simp [code,Generated.shared_swap.program,h14]
        have hs := threadStep_load ht hr hcode heval ha hv
        have hw : wrap 32 (word (c.input (other tid))) = word (c.input (other tid)) := word_word _
        have hit' : ThreadInv c m.epoch tid (assign t "%r3" (word (c.input (other tid)))) := by
          simp_all [ThreadInv,Control,Regs,assign,advance]
        have hinv : Inv c (updateThread {m with history := a::m.history} tid
            (assign t "%r3" (word (c.input (other tid))))) := by
          apply inv_update (inv_record hi hg rfl) htid hit'
          · intro _; exact hi.staged tid t ht (by omega)
          · simp [assign,advance,h14]
        refine ⟨_,?_,hinv,rfl,rfl⟩
        simpa only [hw] using hs
      · by_cases h15 : t.pc = 15
        · have hreg : lookup "%rd4" t.regs = some (4*(c.dst+tid)) := by have := hit.2; simp_all [Regs]
          have hvalue : lookup "%r3" t.regs = some (word (c.input (other tid))) := by have := hit.2; simp_all [Regs]
          have heval : evalAddr tid t {base := .reg "%rd4"} = .ok (4*(c.dst+tid)) := by
            simp [evalAddr,eval,hreg,CopyContract.dstAddr64 c.toConfig hn,bind,Except.bind,pure,Except.pure]
          have hop : eval tid t (.reg "%r3") = .ok (word (c.input (other tid))) := by simp [eval,hvalue]
          let a : Access := ⟨.global,4*(c.dst+tid),tid,true,m.epoch⟩
          have hg : Granted (ledger c m.epoch) a := by simp [Granted,a,destination_share c m.epoch htid]
          have hd : 4*(c.dst+tid)/4 = c.dst+tid := by omega
          have hb : 4*(c.dst+tid)/4 < (memory m .global).length := by
            have := c.dstBound
            simp only [memory,hi.size,hd]
            omega
          have ha : AccessOK m a := permission_accessOK hi.history hg rfl (by dsimp [a]; omega) hb
          have hcode : code[t.pc]? = some (.store .global {base := .reg "%rd4"} (.reg "%r3")) := by
            simp [code,Generated.shared_swap.program,h15]
          have hs := threadStep_store ht hr hcode heval hop ha
          have hw : wrap 32 (word (c.input (other tid))) = word (c.input (other tid)) := word_word _
          have hit' : ThreadInv c m.epoch tid (advance t) := by simp_all [ThreadInv,Control,Regs,advance]
          have hinv : Inv c (updateThread
              {m with globalMem := m.globalMem.set (c.dst+tid) (some (word (c.input (other tid)))),
                      history := a::m.history} tid (advance t)) := by
            apply inv_update (inv_record (inv_global_write hi ht h15 htid) hg rfl) htid hit'
            · intro _; exact hi.staged tid t ht (by omega)
            · intro _; exact List.getElem?_set_self (by simpa [memory,hd] using hb)
          refine ⟨_,?_,hinv,rfl,rfl⟩
          simpa [memory,setMemory,hd,hw,a] using hs
        · obtain ⟨i,t',hpc,hl,hs,hit',hstage,hcommit⟩ := local_step c htid hi.params hit hr h8 h9 h14 h15
          have hinv : Inv c (updateThread m tid t') := by
            apply inv_update hi htid hit'
            · intro hp; exact hi.staged tid t ht (hstage hp)
            · intro hp; exact hi.committed tid t ht (hcommit hp)
          refine ⟨_,?_,hinv,rfl,rfl⟩
          rw [threadStep_local ht hr hpc hl,hs]
          rfl

def released (m : Machine) : Machine := {
  m with threads := m.threads.map (fun t => {t with status := .running}), epoch := m.epoch+1
}

theorem release_shape {c m m'} (hi : Inv c m) (hs : release m = .ok m') :
    m.epoch = 0 ∧ m.threads.all (fun t => t.status == .waiting 0) = true ∧ m' = released m := by
  unfold release at hs
  cases ht : m.threads.head? with
  | none => simp [ht,bind,Except.bind] at hs
  | some t =>
    obtain ⟨tid,hget⟩ := List.mem_iff_getElem?.mp (List.mem_of_head? ht)
    have hc := (hi.threads tid t hget).1
    cases hstatus : t.status with
    | running => simp [ht,hstatus,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs
    | done => simp [ht,hstatus,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs
    | waiting id =>
      have hid : id = 0 := by simp_all [Control]
      have he : m.epoch = 0 := by simp_all [Control]
      subst id
      by_cases hall : m.threads.all (fun t => t.status == .waiting 0) = true
      · simp [ht,hstatus,hall,bind,Except.bind,pure,Except.pure] at hs
        exact ⟨he,hall,hs.symm⟩
      · simp [ht,hstatus,hall,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs

/-- Collective barrier proof: the actual rendezvous establishes initialized
shared values and permits the read ownership to move to the opposite thread.
The generic event/epoch regrant theorem is reused with no new axiom. -/
theorem release_rule {c m m'} (hi : Inv c m) (hs : release m = .ok m') :
    Inv c m' ∧ m'.params = m.params := by
  have hprotocol := barrier_regrant hi.past hs (ledger c m'.epoch)
  obtain ⟨he,hall,hshape⟩ := release_shape hi hs
  subst m'
  have hwait : ∀ t ∈ m.threads, t.status = .waiting 0 := by
    intro t ht
    have := List.all_eq_true.mp hall t ht
    simpa using this
  refine ⟨{count := by simpa [released] using hi.count
           size := hi.size, sharedSize := hi.sharedSize, params := hi.params
           phase := by simp [released,he], frame := hi.frame
           history := hprotocol.2, past := hprotocol.1
           threads := ?_, staged := ?_, committed := ?_},rfl⟩
  · intro j u hnew
    cases hold : m.threads[j]? with
    | none => simp [released,List.getElem?_map,hold] at hnew
    | some t =>
      have hu : {t with status := .running} = u := by simpa [released,List.getElem?_map,hold] using hnew
      subst u
      have hw := hwait t (List.mem_of_getElem? hold)
      have hpc : t.pc = 11 := by have := (hi.threads j t hold).1; simp_all [Control]
      refine ⟨?_,?_⟩
      · simp [Control,released,he,hpc]
      · exact (hi.threads j t hold).2
  · intro j u hnew h10
    cases hold : m.threads[j]? with
    | none => simp [released,List.getElem?_map,hold] at hnew
    | some t =>
      have hu : {t with status := .running} = u := by simpa [released,List.getElem?_map,hold] using hnew
      apply hi.staged j t hold
      simpa [← hu] using h10
  · intro j u hnew h16
    cases hold : m.threads[j]? with
    | none => simp [released,List.getElem?_map,hold] at hnew
    | some t =>
      have hu : {t with status := .running} = u := by simpa [released,List.getElem?_map,hold] using hnew
      apply hi.committed j t hold
      simpa [← hu] using h16

theorem step_rule {c m m' a} (hi : Inv c m) (hs : step code a m = .ok m') :
    Inv c m' ∧ m'.params = m.params := by
  cases a with
  | thread tid =>
    cases ht : m.threads[tid]? with
    | none => simp [step,threadStep,ht,bind,Except.bind] at hs
    | some t =>
      cases hstatus : t.status with
      | running =>
        obtain ⟨mid,hmid,hinv,_,hparams⟩ := thread_rule hi ht hstatus
        rw [step,hmid] at hs
        cases hs
        exact ⟨hinv,hparams⟩
      | done => simp [step,threadStep,ht,hstatus,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs
      | waiting id => simp [step,threadStep,ht,hstatus,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs
  | release => exact release_rule hi hs

theorem invariant (c : Config) : InductiveInvariant code (Inv c) := by
  intro m a m' hi hs
  exact (step_rule hi hs).1

structure Pre (c : Config) (m : Machine) : Prop where
  count : m.threads.length = 2
  memory : m.globalMem = c.before
  sharedSize : m.sharedMem.length = Generated.shared_swap.sharedBytes / 4
  params : Params c m.params
  phase : m.epoch = 0
  threads : ∀ t ∈ m.threads, t.pc = 0 ∧ t.status = .running
  history : m.history = []

def initial (c : Config) : Machine := {
  threads := [{},{}]
  globalMem := c.before
  sharedMem := List.replicate (Generated.shared_swap.sharedBytes / 4) none
  params := [("src",4*c.src),("dst",4*c.dst)]
}

theorem initial_pre (c : Config) : Pre c (initial c) := by
  refine {count := rfl, memory := rfl, sharedSize := by simp [initial]
          params := by simp [initial,Params,lookup], phase := rfl, history := rfl, threads := ?_}
  intro t ht
  simp only [initial,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl <;> exact ⟨rfl,rfl⟩

theorem pre_invariant {c m} (hp : Pre c m) : Inv c m := by
  refine {count := hp.count, size := by simp [hp.memory], sharedSize := hp.sharedSize
          params := hp.params, phase := by simp [hp.phase]
          threads := ?_, frame := ?_, staged := ?_, committed := ?_, history := ?_, past := ?_}
  · intro tid t ht
    obtain ⟨hpc,hr⟩ := hp.threads t (List.mem_of_getElem? ht)
    simp [ThreadInv,Control,Regs,hpc,hr,hp.phase]
  · intro j _; rw [hp.memory]
  · intro tid t ht h10
    have := (hp.threads t (List.mem_of_getElem? ht)).1
    omega
  · intro tid t ht h16
    have := (hp.threads t (List.mem_of_getElem? ht)).1
    omega
  · intro a ha _; simp [hp.history] at ha
  · intro a ha; simp [hp.history] at ha

theorem safe (c : Config) : Safe code (Pre c) := by
  intro m m' hp hs tid t ht hr
  have hi := invariant_steps (invariant c) hs (pre_invariant hp)
  obtain ⟨next,hnext,_⟩ := thread_rule hi ht hr
  exact ⟨next,hnext⟩

theorem finished_at {c m} (hi : Inv c m)
    (hd : m.threads.all (fun t => t.status == .done) = true) {tid} (htid : tid < 2) :
    ∃ t, m.threads[tid]? = some t ∧ t.pc = 16 ∧ m.epoch = 1 := by
  have hlt : tid < m.threads.length := by simpa [hi.count] using htid
  let t := m.threads[tid]'hlt
  have ht : m.threads[tid]? = some t := List.getElem?_eq_getElem hlt
  have hdone : t.status = .done := by
    have := List.all_eq_true.mp hd t (List.mem_of_getElem? ht)
    simpa using this
  have hc := (hi.threads tid t ht).1
  refine ⟨t,ht,?_,?_⟩ <;> simp_all [Control]

structure Post (c : Config) (m : Machine) : Prop where
  count : m.threads.length = 2
  size : m.globalMem.length = c.before.length
  sharedSize : m.sharedMem.length = Generated.shared_swap.sharedBytes / 4
  phase : m.epoch = 1
  values : ∀ tid, tid < 2 → m.globalMem[c.dst+tid]? = some (some (word (c.input (other tid))))
  staging : ∀ tid, tid < 2 → m.sharedMem[tid]? = some (some (word (c.input tid)))
  frame : ∀ j, CopyContract.Outside c.toConfig j → m.globalMem[j]? = c.before[j]?

theorem exit_post {c m} (hi : Inv c m)
    (hd : m.threads.all (fun t => t.status == .done) = true) : Post c m := by
  obtain ⟨_,_,_,he⟩ := finished_at hi hd (by decide : 0 < 2)
  refine {count := hi.count, size := hi.size, sharedSize := hi.sharedSize
          phase := he, frame := hi.frame, staging := ?_, values := ?_}
  · intro tid htid
    obtain ⟨t,ht,hpc,_⟩ := finished_at hi hd htid
    exact hi.committed tid t ht hpc
  · intro tid htid; exact shared_value hi he htid

/-- Universal safety/correctness over all finite CTA interleavings, with the
original full-CTA barrier. There is no change to the PTX or its synchronization. -/
theorem correct (c : Config) : Triple code (Pre c) (Post c) :=
  invariant_rule (code := code) (P := Pre c) (Q := Post c) (I := Inv c)
    (fun _ hp => pre_invariant hp) (invariant c) (fun _ hi hd => exit_post hi hd)

theorem params_frame {c m m'} (hi : Inv c m) (hs : Steps code m m') : m'.params = m.params := by
  induction hs with
  | refl => rfl
  | next a hstep hrest ih =>
    obtain ⟨hinv,hparams⟩ := step_rule hi hstep
    exact (ih hinv).trans hparams

theorem frame {c m m'} (hp : Pre c m) (hs : Steps code m m') :
    m'.params = m.params ∧ m'.threads.length = m.threads.length ∧
    m'.globalMem.length = m.globalMem.length ∧ m'.sharedMem.length = m.sharedMem.length ∧
    ∀ j, CopyContract.Outside c.toConfig j → m'.globalMem[j]? = m.globalMem[j]? := by
  have hstart := pre_invariant hp
  have hfinal := invariant_steps (invariant c) hs hstart
  refine ⟨params_frame hstart hs,hfinal.count.trans hp.count.symm,
    hfinal.size.trans hstart.size.symm,hfinal.sharedSize.trans hp.sharedSize.symm,?_⟩
  intro j hj
  rw [hfinal.frame j hj,hp.memory]

theorem release_ready {m : Machine} (hc : m.threads.length = 2)
    (hw : ∀ t ∈ m.threads, t.status = .waiting 0) : release m = .ok (released m) := by
  cases ht : m.threads with
  | nil => simp [ht] at hc
  | cons t ts =>
    have hhead : t.status = .waiting 0 := hw t (by simp [ht])
    have htail : ts.all (fun u => u.status == .waiting 0) = true := by
      apply List.all_eq_true.mpr
      intro u hu
      have := hw u (by simp [ht,hu])
      simp [this]
    simp [release,ht,hhead,htail,released,bind,Except.bind,pure,Except.pure]

/-- A nonfinished state can execute a thread or the actual collective release.
This explicitly excludes barrier deadlock within the stated precondition; it
does not assume that an external scheduler will choose an enabled action. -/
theorem progress {c m m'} (hp : Pre c m) (hs : Steps code m m')
    (hn : m'.threads.all (fun t => t.status == .done) ≠ true) :
    ∃ a next, step code a m' = .ok next := by
  have hi := invariant_steps (invariant c) hs (pre_invariant hp)
  by_cases hrun : m'.threads.any (fun t => t.status == .running) = true
  · obtain ⟨t,ht,hr⟩ := List.any_eq_true.mp hrun
    have hr : t.status = .running := by simpa using hr
    obtain ⟨tid,hget⟩ := List.mem_iff_getElem?.mp ht
    obtain ⟨next,hnext,_⟩ := thread_rule hi hget hr
    exact ⟨.thread tid,next,hnext⟩
  · have hnorun : ∀ t ∈ m'.threads, t.status ≠ .running := by
      intro t ht hr
      apply hrun
      apply List.any_eq_true.mpr
      exact ⟨t,ht,by simp [hr]⟩
    have hf : m'.threads.all (fun t => t.status == .done) = false := by
      cases h : m'.threads.all (fun t => t.status == .done)
      · rfl
      · exact (hn h).elim
    obtain ⟨t,ht,hnd⟩ := List.all_eq_false.mp hf
    have hnd : t.status ≠ .done := by simpa using hnd
    obtain ⟨tid,hget⟩ := List.mem_iff_getElem?.mp ht
    have he : m'.epoch = 0 := by
      rcases (hi.threads tid t hget).1.2 with ⟨hr,_⟩ | ⟨_,_,he⟩ | ⟨hd,_⟩
      · exact (hnorun t ht hr).elim
      · exact he
      · exact (hnd hd).elim
    have hwait : ∀ u ∈ m'.threads, u.status = .waiting 0 := by
      intro u hu
      obtain ⟨j,hget⟩ := List.mem_iff_getElem?.mp hu
      rcases (hi.threads j u hget).1.2 with ⟨hr,_⟩ | ⟨hw,_⟩ | ⟨_,_,he1⟩
      · exact (hnorun u hu hr).elim
      · exact hw
      · omega
    exact ⟨.release,released m',release_ready hi.count hwait⟩

def pairConfig (x y : Nat) : Config := {
  toConfig := CopyContract.contiguous [x,y] 2 (by simp) (by decide)
  n_two := rfl
  count_two := rfl
}

end Ptx.SharedContract
