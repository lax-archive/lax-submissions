/-
The output positions of the mso transduction built from a two-way transducer.

Part of the proof of Theorem `thm:logic-regular-functions` of *Transducers* (M. Bojańczyk).  The
output of a two-way transducer is the concatenation of the strings produced by the successive steps
of its run, so its positions are indexed by pairs `(t, i)` where `t` is a step of the run and `i` a
position inside the string produced at that step.  The elements of the mso transduction are (state,
index) copies of the input positions, and this file contains the purely combinatorial half of the
correspondence: given an abstract type `E` of elements equipped with the state, the position, the
index and the semantic predicates of the transduction, it produces the list of elements required by
`MSOTransduction.Outputs` and checks the requirements of Definition `def:mso-transduction`. -/
import Lax916827Proofs.Source.PartC.RunProbe
import Lax314295Proofs.Source.PartC.FlatIndex
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers
namespace RunElts

open TwoWay FlatIndex

variable {A B Q : Type}

/-! ## Times of the run -/

variable (M : TwoWay A B Q) (w : List A)

lemma runAt_lt_of_halt {T : ℕ} (hT : cfgAt M w T = some Cfg.halt) {q : Q} {p t : ℕ}
    (h : RunAt M w q p t) : t < T := by
  rcases Nat.lt_or_ge t T with h' | h'
  · exact h'
  · exfalso
    obtain ⟨x, y, hc, -⟩ := h
    rcases Nat.eq_or_lt_of_le h' with rfl | hlt
    · rw [hT] at hc; simp at hc
    · have : cfgAt M w t = none := cfgAt_none_mono M w (by omega) (cfgAt_halt_succ M w hT)
      rw [this] at hc; simp at hc

lemma exists_runAt_of_lt {T : ℕ} (hT : cfgAt M w T = some Cfg.halt) {t : ℕ} (ht : t < T) :
    ∃ q p, RunAt M w q p t := by
  have hsome : (cfgAt M w t).isSome :=
    cfgAt_isSome_of_le M w (le_of_lt ht) (by rw [hT]; simp)
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hsome
  cases c with
  | halt =>
      exact absurd (halt_time_unique M w hc hT) (by omega)
  | conf x q y => exact ⟨q, x.length, x, y, hc, rfl⟩

/-! ## The list of elements -/

/-- The strings produced by the successive steps of a halting run. -/
def outs (M : TwoWay A B Q) (w : List A) (T : ℕ) : List (List B) :=
  (List.range T).map (outAt M w)

lemma outs_length (T : ℕ) : (outs M w T).length = T := by simp [outs]

lemma outs_getElem? {T t : ℕ} (ht : t < T) : (outs M w T)[t]? = some (outAt M w t) := by
  rw [outs, List.getElem?_map, List.getElem?_range ht]
  rfl

lemma outs_flatten (T : ℕ) : (outs M w T).flatten = outRange M w 0 T := by
  rw [outRange, outs, Nat.sub_zero, List.range_eq_range']

lemma mem_pairs_outs (T t i : ℕ) :
    (t, i) ∈ pairs (outs M w T) ↔ (t < T ∧ i < (outAt M w t).length) := by
  rw [mem_pairs]
  constructor
  · rintro ⟨l, hl, hi⟩
    have ht : t < T := by
      by_contra hcon
      rw [outs, List.getElem?_map, List.getElem?_eq_none (by simp; omega)] at hl
      simp at hl
    rw [outs_getElem? M w ht] at hl
    exact ⟨ht, by rwa [(Option.some.inj hl).symm] at hi⟩
  · rintro ⟨ht, hi⟩
    exact ⟨outAt M w t, outs_getElem? M w ht, hi⟩

/-- The list of elements, in the order of the run. -/
def elts (M : TwoWay A B Q) (w : List A) (T : ℕ) {E : Type} (mk : ℕ × ℕ → E) : List E :=
  (pairs (outs M w T)).map mk

section Abstract

variable {T : ℕ} (hT : cfgAt M w T = some Cfg.halt)
  {E : Type} (st : E → Q) (pos ix : E → ℕ) (mk : ℕ × ℕ → E)
  (sel : E → Prop) (ord : E → E → Prop) (lab : E → B → Prop)

/-- The hypotheses relating the abstract elements to the run. -/
structure Spec : Prop where
  /-- An element is selected exactly when it is a letter produced by the run. -/
  sel_iff : ∀ e, sel e ↔ ∃ t, RunAt M w (st e) (pos e) t ∧ ix e < (outAt M w t).length
  /-- A *selected* element is determined by its state, position and index. -/
  inj : ∀ e e', sel e → sel e' → st e = st e' → pos e = pos e' → ix e = ix e' → e = e'
  /-- The element attached to a step of the run and an index. -/
  mk_eq : ∀ (t i : ℕ) (q : Q) (p : ℕ), RunAt M w q p t → i < (outAt M w t).length →
      st (mk (t, i)) = q ∧ pos (mk (t, i)) = p ∧ ix (mk (t, i)) = i
  /-- The order of the transduction is the order of the run. -/
  ord_iff : ∀ e e', sel e → sel e' → ∀ t t', RunAt M w (st e) (pos e) t →
      RunAt M w (st e') (pos e') t' → (ord e e' ↔ (t < t' ∨ (t = t' ∧ ix e ≤ ix e')))
  /-- The label of an element is the letter produced by the run. -/
  lab_iff : ∀ e b, sel e → ∀ t, RunAt M w (st e) (pos e) t →
      (lab e b ↔ (outAt M w t)[ix e]? = some b)

variable {M w st pos ix mk sel ord lab}

include hT

lemma mem_elts_iff (hs : Spec M w st pos ix mk sel ord lab) (e : E) :
    e ∈ elts M w T mk ↔ sel e := by
  constructor
  · intro he
    obtain ⟨ti, hti, rfl⟩ := List.mem_map.1 he
    obtain ⟨t, i⟩ := ti
    rw [mem_pairs_outs] at hti
    obtain ⟨ht, hi⟩ := hti
    obtain ⟨q, p, hrun⟩ := exists_runAt_of_lt M w hT ht
    obtain ⟨hst, hpos, hix⟩ := hs.mk_eq t i q p hrun hi
    rw [hs.sel_iff]
    exact ⟨t, by rw [hst, hpos]; exact hrun, by rw [hix]; exact hi⟩
  · intro he
    obtain ⟨t, hrun, hi⟩ := (hs.sel_iff e).1 he
    have ht : t < T := runAt_lt_of_halt M w hT hrun
    refine List.mem_map.2 ⟨(t, ix e), (mem_pairs_outs M w T t (ix e)).2 ⟨ht, hi⟩, ?_⟩
    obtain ⟨hst, hpos, hix⟩ := hs.mk_eq t (ix e) (st e) (pos e) hrun hi
    have hselm : sel (mk (t, ix e)) := by
      rw [hs.sel_iff]
      exact ⟨t, by rw [hst, hpos]; exact hrun, by rw [hix]; exact hi⟩
    exact hs.inj _ _ hselm he hst hpos hix

lemma nodup_elts (hs : Spec M w st pos ix mk sel ord lab) :
    (elts M w T mk).Nodup := by
  refine List.Nodup.map_on ?_ (nodup_pairs _)
  rintro ⟨t, i⟩ hti ⟨t', i'⟩ hti' heq
  rw [mem_pairs_outs] at hti hti'
  obtain ⟨q, p, hrun⟩ := exists_runAt_of_lt M w hT hti.1
  obtain ⟨q', p', hrun'⟩ := exists_runAt_of_lt M w hT hti'.1
  obtain ⟨hst, hpos, hix⟩ := hs.mk_eq t i q p hrun hti.2
  obtain ⟨hst', hpos', hix'⟩ := hs.mk_eq t' i' q' p' hrun' hti'.2
  have hi : i = i' := by rw [← hix, ← hix', heq]
  have hq : q = q' := by rw [← hst, ← hst', heq]
  have hp : p = p' := by rw [← hpos, ← hpos', heq]
  subst hq; subst hp
  have := hrun.time_unique hT hrun'
  subst this
  rw [hi]

omit hT in
lemma length_elts : (elts M w T mk).length = (outRange M w 0 T).length := by
  rw [elts, List.length_map, length_pairs, outs_flatten]

omit hT in
lemma getElem_elts {j : ℕ} (hj : j < (elts M w T mk).length) :
    (elts M w T mk)[j] = mk ((pairs (outs M w T))[j]'(by
      simpa [elts] using hj)) := by
  simp [elts]

omit hT in
lemma pairs_mem {j : ℕ} (hj : j < (pairs (outs M w T)).length) :
    (pairs (outs M w T))[j] ∈ pairs (outs M w T) := List.getElem_mem hj

lemma ord_elts (hs : Spec M w st pos ix mk sel ord lab) (j k : ℕ)
    (hj : j < (elts M w T mk).length)
    (hk : k < (elts M w T mk).length) (hjk : j < k) :
    ord ((elts M w T mk)[j]) ((elts M w T mk)[k]) := by
  have hj' : j < (pairs (outs M w T)).length := by simpa [elts] using hj
  have hk' : k < (pairs (outs M w T)).length := by simpa [elts] using hk
  have hlex := (List.pairwise_iff_getElem.1 (pairwise_pairs (outs M w T))) j k hj' hk' hjk
  set a := (pairs (outs M w T))[j] with ha
  set b := (pairs (outs M w T))[k] with hb
  have hma : a ∈ pairs (outs M w T) := List.getElem_mem hj'
  have hmb : b ∈ pairs (outs M w T) := List.getElem_mem hk'
  rw [show a = (a.1, a.2) from rfl, mem_pairs_outs] at hma
  rw [show b = (b.1, b.2) from rfl, mem_pairs_outs] at hmb
  obtain ⟨q, p, hrun⟩ := exists_runAt_of_lt M w hT hma.1
  obtain ⟨q', p', hrun'⟩ := exists_runAt_of_lt M w hT hmb.1
  obtain ⟨hst, hpos, hix⟩ := hs.mk_eq a.1 a.2 q p hrun hma.2
  obtain ⟨hst', hpos', hix'⟩ := hs.mk_eq b.1 b.2 q' p' hrun' hmb.2
  have hea : (elts M w T mk)[j] = mk (a.1, a.2) := by simp [elts, ← ha]
  have heb : (elts M w T mk)[k] = mk (b.1, b.2) := by simp [elts, ← hb]
  rw [hea, heb]
  have hsela : sel (mk (a.1, a.2)) := by
    rw [hs.sel_iff]
    exact ⟨a.1, by rw [hst, hpos]; exact hrun, by rw [hix]; exact hma.2⟩
  have hselb : sel (mk (b.1, b.2)) := by
    rw [hs.sel_iff]
    exact ⟨b.1, by rw [hst', hpos']; exact hrun', by rw [hix']; exact hmb.2⟩
  refine (hs.ord_iff _ _ hsela hselb a.1 b.1 (by rw [hst, hpos]; exact hrun)
    (by rw [hst', hpos']; exact hrun')).2 ?_
  rcases hlex with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, by rw [hix, hix']; omega⟩

lemma lab_elts (hs : Spec M w st pos ix mk sel ord lab) (j : ℕ)
    (hj : j < (elts M w T mk).length)
    (hj' : j < (outRange M w 0 T).length) :
    lab ((elts M w T mk)[j]) ((outRange M w 0 T)[j]) := by
  have hj'' : j < (pairs (outs M w T)).length := by simpa [elts] using hj
  set a := (pairs (outs M w T))[j] with ha
  have hma : a ∈ pairs (outs M w T) := List.getElem_mem hj''
  rw [show a = (a.1, a.2) from rfl, mem_pairs_outs] at hma
  obtain ⟨q, p, hrun⟩ := exists_runAt_of_lt M w hT hma.1
  obtain ⟨hst, hpos, hix⟩ := hs.mk_eq a.1 a.2 q p hrun hma.2
  have hea : (elts M w T mk)[j] = mk (a.1, a.2) := by simp [elts, ← ha]
  have hsela : sel (mk (a.1, a.2)) := by
    rw [hs.sel_iff]
    exact ⟨a.1, by rw [hst, hpos]; exact hrun, by rw [hix]; exact hma.2⟩
  -- the letter at the position `j` of the output
  have hflat := map_get2_pairs (outs M w T)
  have hgj : get2 (outs M w T) a = some ((outs M w T).flatten[j]'(by
      rw [← length_pairs]; exact hj'')) := by
    have h1 : ((pairs (outs M w T)).map (get2 (outs M w T)))[j]? =
        ((outs M w T).flatten.map some)[j]? := by rw [hflat]
    rw [List.getElem?_map, List.getElem?_map,
      List.getElem?_eq_getElem hj'', List.getElem?_eq_getElem (by rw [← length_pairs]; exact hj'')]
      at h1
    simpa using h1
  rw [get2, outs_getElem? M w hma.1] at hgj
  simp only [Option.bind_some] at hgj
  rw [hea]
  refine (hs.lab_iff _ _ hsela a.1 (by rw [hst, hpos]; exact hrun)).2 ?_
  rw [hix, hgj]
  congr 1
  have : (outs M w T).flatten = outRange M w 0 T := outs_flatten M w T
  simp [this]

/-- **The list of output positions.**  It is exactly the list required by
`MSOTransduction.Outputs` for the output of the run. -/
theorem exists_elts (hs : Spec M w st pos ix mk sel ord lab) :
    ∃ es : List E, es.Nodup ∧ (∀ e, e ∈ es ↔ sel e) ∧
      (∀ (j k : ℕ) (hj : j < es.length) (hk : k < es.length), j < k → ord es[j] es[k]) ∧
      es.length = (outRange M w 0 T).length ∧
      ∀ (j : ℕ) (hj : j < es.length) (hj' : j < (outRange M w 0 T).length),
        lab es[j] ((outRange M w 0 T)[j]) :=
  ⟨elts M w T mk, nodup_elts hT hs, mem_elts_iff hT hs,
    ord_elts hT hs, length_elts, lab_elts hT hs⟩

omit hT in
/-- **The requirements of Definition `def:mso-transduction`.** -/
theorem proper_props (hs : Spec M w st pos ix mk sel ord lab) :
    (∀ e, sel e → ∃! b, lab e b) ∧
    (∀ e, sel e → ord e e) ∧
    (∀ e e', sel e → sel e' → ord e e' → ord e' e → e = e') ∧
    (∀ e e' e'', sel e → sel e' → sel e'' → ord e e' → ord e' e'' → ord e e'') ∧
    (∀ e e', sel e → sel e' → ord e e' ∨ ord e' e) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨t, hrun, hi⟩ := (hs.sel_iff e).1 he
    refine ⟨(outAt M w t)[ix e], (hs.lab_iff e _ he t hrun).2 (List.getElem?_eq_getElem hi), ?_⟩
    intro b hb
    have := (hs.lab_iff e b he t hrun).1 hb
    rw [List.getElem?_eq_getElem hi] at this
    exact (Option.some.inj this).symm
  · intro e he
    obtain ⟨t, hrun, -⟩ := (hs.sel_iff e).1 he
    exact (hs.ord_iff e e he he t t hrun hrun).2 (Or.inr ⟨rfl, le_refl _⟩)
  · intro e e' he he' h1 h2
    obtain ⟨t, hrun, -⟩ := (hs.sel_iff e).1 he
    obtain ⟨t', hrun', -⟩ := (hs.sel_iff e').1 he'
    have k1 := (hs.ord_iff e e' he he' t t' hrun hrun').1 h1
    have k2 := (hs.ord_iff e' e he' he t' t hrun' hrun).1 h2
    have htt : t = t' := by
      rcases k1 with h | ⟨h, -⟩ <;> rcases k2 with h' | ⟨h', -⟩ <;> omega
    subst htt
    have hix : ix e = ix e' := by
      rcases k1 with h | ⟨-, h⟩
      · omega
      · rcases k2 with h' | ⟨-, h'⟩
        · omega
        · omega
    obtain ⟨hq, hp⟩ := hrun.unique hrun'
    exact hs.inj e e' he he' hq hp hix
  · intro e e' e'' he he' he'' h1 h2
    obtain ⟨t, hrun, -⟩ := (hs.sel_iff e).1 he
    obtain ⟨t', hrun', -⟩ := (hs.sel_iff e').1 he'
    obtain ⟨t'', hrun'', -⟩ := (hs.sel_iff e'').1 he''
    have k1 := (hs.ord_iff e e' he he' t t' hrun hrun').1 h1
    have k2 := (hs.ord_iff e' e'' he' he'' t' t'' hrun' hrun'').1 h2
    refine (hs.ord_iff e e'' he he'' t t'' hrun hrun'').2 ?_
    rcases k1 with h | ⟨h, hi⟩ <;> rcases k2 with h' | ⟨h', hi'⟩
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, by omega⟩
  · intro e e' he he'
    obtain ⟨t, hrun, -⟩ := (hs.sel_iff e).1 he
    obtain ⟨t', hrun', -⟩ := (hs.sel_iff e').1 he'
    rcases Nat.lt_trichotomy t t' with h | rfl | h
    · exact Or.inl ((hs.ord_iff e e' he he' t t' hrun hrun').2 (Or.inl h))
    · rcases Nat.le_total (ix e) (ix e') with h | h
      · exact Or.inl ((hs.ord_iff e e' he he' t t hrun hrun').2 (Or.inr ⟨rfl, h⟩))
      · exact Or.inr ((hs.ord_iff e' e he' he t t hrun' hrun).2 (Or.inr ⟨rfl, h⟩))
    · exact Or.inr ((hs.ord_iff e' e he' he t' t hrun' hrun).2 (Or.inl h))

end Abstract

end RunElts
end Lax314295Proofs.Transducers
