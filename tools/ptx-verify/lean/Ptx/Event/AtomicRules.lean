import Ptx.Event.Consistency

/-! Scope and atomicity consequences of the common memory predicates. These
rules do not add ticket values, a total GPU schedule or inter-CTA causality as
kernel preconditions. Source provenance and global execution existence remain
independent obligations. -/
namespace Ptx.Event
open Ptx.ISA
variable {ByteValue Answers : Type}

theorem morally_strong_symmetric {c : Candidate ByteValue Answers} {a b}
    (hs : MorallyStrong c a b) : MorallyStrong c b a := by
  obtain ⟨he,hfoot,ha,hb⟩ := hs
  refine ⟨?_,hfoot,hb,ha⟩
  rcases he with he | ⟨sa,sb,ha,hb,hsa,hsb⟩
  · exact Or.inl he.symm
  · exact Or.inr ⟨sb,sa,hb,ha,hsb,hsa⟩

theorem rmw_morally_strong {c : Candidate ByteValue Answers} {a b : EventId}
    {sa sb : Scope} {base : Location} {pa pb : RmwBytes ByteValue}
    (ha : c.eventAt a = some (.rmw sa base pa)) (hb : c.eventAt b = some (.rmw sb base pb))
    (hlen : pa.before.length = pb.before.length)
    (hsa : sa.Includes a.thread b.thread) (hsb : sb.Includes b.thread a.thread) : MorallyStrong c a b := by
  exact ⟨Or.inr ⟨sa,sb,by simp [ha,Kind.strongScope],by simp [hb,Kind.strongScope],hsa,hsb⟩,
    (base,pa.before.length),by simp [ha,Kind.footprint],by simp [hb,Kind.footprint,hlen]⟩

theorem mixed_size_free_of_footprint {c : Candidate ByteValue Answers} {rf common}
    (hf : ∀ event, c.Present event → (c.eventAt event).bind Kind.footprint = some common) : ¬ MixedSizeRace c rf := by
  rintro ⟨a,b,hr,hn⟩
  obtain ⟨loc,ha,hb⟩ := hr.overlap
  exact hn ⟨common,hf a (accesses_present ha),hf b (accesses_present hb)⟩

/-- SC-per-location excludes an RMW sourcing its own write. -/
theorem rmw_no_self_read {c : Candidate ByteValue Answers} {initial rf co event loc vr vw}
    (hm : GenericMemoryConditions c initial rf co) (hn : ¬ MixedSizeRace c rf)
    (hr : c.readByte event loc = some vr) (hw : c.writeByte event loc = some vw) :
    rf event loc ≠ .write event := by
  intro hs
  have ha : c.Accesses event loc := Or.inl (by rw [hr]; rfl)
  have hp := accesses_present ha
  have hstrong := write_self_strong hw
  have hoverlap : c.Overlap event event := ⟨loc,ha,ha⟩
  have hsc := hm.scPerLocation hn (fun e => e = event)
    (by intro e he; subst e; exact hp)
    (by intro a b he hf; rw [he,hf]; exact ⟨hstrong,hoverlap⟩) event rfl
  apply hsc
  exact .single ⟨rfl,rfl,Or.inr (Or.inl ⟨loc,vr,hr,hs,by rw [hw]; rfl⟩)⟩

theorem rmw_predecessor_excludes_initial {c : Candidate ByteValue Answers} {initial rf co atomic writer loc vr vw va}
    (hm : GenericMemoryConditions c initial rf co) (hn : ¬ MixedSizeRace c rf)
    (ha : c.IsRMW atomic) (hs : MorallyStrong c atomic writer)
    (hr : c.readByte atomic loc = some vr) (hw : c.writeByte writer loc = some vw)
    (hwa : c.writeByte atomic loc = some va) (hc : co loc (.write writer) (.write atomic)) :
    rf atomic loc ≠ .initial := by
  intro hi
  have hinit := (hm.coherence hn).initialization loc writer vw hw
  exact hm.rmwAtomicity hn atomic writer ha hs loc vr vw hr hw (hi ▸ hinit) loc va vw hwa hw hc

/-- Both mutually scoped RMWs cannot read initialization at an overlapping byte.
Coherence chooses their order; no CTA is assigned a fixed place in that order. -/
theorem two_rmw_not_both_initial {c : Candidate ByteValue Answers} {initial rf co a b loc ra rb wa wb}
    (hm : GenericMemoryConditions c initial rf co) (hn : ¬ MixedSizeRace c rf)
    (hab : a ≠ b) (ha : c.IsRMW a) (hb : c.IsRMW b) (hs : MorallyStrong c a b)
    (hra : c.readByte a loc = some ra) (hrb : c.readByte b loc = some rb)
    (hwa : c.writeByte a loc = some wa) (hwb : c.writeByte b loc = some wb) :
    ¬ (rf a loc = .initial ∧ rf b loc = .initial) := by
  rintro ⟨hia,hib⟩
  rcases (hm.coherence hn).comparable loc a b wa wb hab hwa hwb (Or.inl hs) with hc | hc
  · exact rmw_predecessor_excludes_initial hm hn hb (morally_strong_symmetric hs) hrb hwa hwb hc hib
  · exact rmw_predecessor_excludes_initial hm hn ha hs hra hwb hwa hc hia

/-- Coherence at one byte excludes reading a later modification at ANY shared
byte of the same morally strong operations. This avoids assuming bytewise source
uniformity before it has been proved. -/
theorem coherence_before_cannot_read_after {c : Candidate ByteValue Answers}
    {initial rf co a b orderLoc readLoc va vb vr vw}
    (hm : GenericMemoryConditions c initial rf co) (hn : ¬ MixedSizeRace c rf)
    (hs : MorallyStrong c a b)
    (hwa : c.writeByte a orderLoc = some va) (hwb : c.writeByte b orderLoc = some vb)
    (hc : co orderLoc (.write a) (.write b))
    (hr : c.readByte a readLoc = some vr) (hw : c.writeByte b readLoc = some vw) :
    rf a readLoc ≠ .write b := by
  intro hrf
  have haa : c.Accesses a orderLoc := Or.inr (by rw [hwa]; rfl)
  have hab : c.Accesses b orderLoc := Or.inr (by rw [hwb]; rfl)
  have hpair : ∀ x y, (x = a ∨ x = b) → (y = a ∨ y = b) → MorallyStrong c x y ∧ c.Overlap x y := by
    intro x y hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact ⟨write_self_strong hwa,orderLoc,haa,haa⟩
    · exact ⟨hs,orderLoc,haa,hab⟩
    · exact ⟨morally_strong_symmetric hs,orderLoc,hab,haa⟩
    · exact ⟨write_self_strong hwb,orderLoc,hab,hab⟩
  have hsc := hm.scPerLocation hn (fun e => e = a ∨ e = b)
    (by intro e he; rcases he with rfl | rfl; exact accesses_present haa; exact accesses_present hab)
    hpair a (Or.inl rfl)
  apply hsc
  apply Path.trans
  · exact .single ⟨Or.inl rfl,Or.inr rfl,Or.inr (Or.inr (Or.inl ⟨orderLoc,hc⟩))⟩
  · exact .single ⟨Or.inr rfl,Or.inl rfl,Or.inr (Or.inl ⟨readLoc,vr,hr,hrf,by rw [hw]; rfl⟩)⟩

theorem rmw_predecessor_excludes_initial_any_byte {c : Candidate ByteValue Answers}
    {initial rf co atomic writer readLoc orderLoc vr vw va vb}
    (hm : GenericMemoryConditions c initial rf co) (hn : ¬ MixedSizeRace c rf)
    (ha : c.IsRMW atomic) (hs : MorallyStrong c atomic writer)
    (hr : c.readByte atomic readLoc = some vr) (hwr : c.writeByte writer readLoc = some vw)
    (hwa : c.writeByte atomic orderLoc = some va) (hwb : c.writeByte writer orderLoc = some vb)
    (hc : co orderLoc (.write writer) (.write atomic)) : rf atomic readLoc ≠ .initial := by
  intro hi
  have hinit := (hm.coherence hn).initialization readLoc writer vw hwr
  exact hm.rmwAtomicity hn atomic writer ha hs readLoc vr vw hr hwr (hi ▸ hinit) orderLoc va vb hwa hwb hc

end Ptx.Event
