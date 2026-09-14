/-
The *explicit* decomposition of a looping part of a walk into excursions, and of
each excursion into its two halves.

`RequestProject/PartC/SnakeLoop.lean` proves that a looping part of a walk can be
cut into finitely many pieces of smaller width (`Walk.loop_splitsInto`), but the
cutting points are produced by a recursion whose result is not visible in the
statement.  For the induction step of the book's snake lemma the cutting points
have to be *named*, because the rational function of the book's first stage has
to mark them in the input.  This file therefore introduces

* `Walk.visSeq`, the sequence of the successive visits to the base column of a
  loop -- the cutting points of the loop into *excursions*;
* `Walk.excCol`, the column of an excursion that is furthest away from the base
  column, and `Walk.excSplit`, the first visit to it -- the cutting point of an
  excursion into its two halves.

The results are: the sequence of visits stabilises after `k` steps if the loop
visits every column at most `k` times (`Walk.visSeq_stab`), an excursion stays
on one side of its base column and between the base column and `excCol`
(`Walk.exc_range_right`, `Walk.exc_range_left`), and both halves of an excursion
visit every column at most `k - 1` times (`Walk.exc_halves_visitsLe`).
-/
import Lax916827Proofs.Source.PartC.SnakeLoop
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace Walk

variable {p : ℕ → ℕ} {T : ℕ}

/-! ### The successive visits to the base column of a loop -/

/-- The set of times in `(t, b0]` at which the walk is at the column `c`. -/
def visAfter (p : ℕ → ℕ) (c b0 t : ℕ) : Set ℕ := {s | t < s ∧ s ≤ b0 ∧ p s = c}

open scoped Classical in
/-- The next visit to the column `c` strictly after the time `t`, or `b0` if
there is none. -/
noncomputable def nextVis (p : ℕ → ℕ) (c b0 t : ℕ) : ℕ :=
  if (visAfter p c b0 t).Nonempty then sInf (visAfter p c b0 t) else b0

lemma nextVis_mem {c b0 t : ℕ} (h : (visAfter p c b0 t).Nonempty) :
    nextVis p c b0 t ∈ visAfter p c b0 t := by
  rw [nextVis, if_pos h]
  exact Nat.sInf_mem h

lemma nextVis_le {c b0 t : ℕ} : nextVis p c b0 t ≤ b0 := by
  by_cases h : (visAfter p c b0 t).Nonempty
  · exact (nextVis_mem h).2.1
  · rw [nextVis, if_neg h]

lemma le_nextVis {c b0 t : ℕ} (ht : t ≤ b0) : t ≤ nextVis p c b0 t := by
  by_cases h : (visAfter p c b0 t).Nonempty
  · exact le_of_lt (nextVis_mem h).1
  · rw [nextVis, if_neg h]; exact ht

lemma pos_nextVis {c b0 t : ℕ} (hb : p b0 = c) : p (nextVis p c b0 t) = c := by
  by_cases h : (visAfter p c b0 t).Nonempty
  · exact (nextVis_mem h).2.2
  · rw [nextVis, if_neg h]; exact hb

/-- Between a time and the next visit to `c`, the walk is not at `c`. -/
lemma nextVis_no_mid {c b0 t : ℕ} {s : ℕ} (h1 : t < s) (h2 : s < nextVis p c b0 t) :
    p s ≠ c := by
  by_cases h : (visAfter p c b0 t).Nonempty
  · rw [nextVis, if_pos h] at h2
    intro hs
    have hmem : s ∈ visAfter p c b0 t := by
      refine ⟨h1, ?_, hs⟩
      have : sInf (visAfter p c b0 t) ≤ b0 := (Nat.sInf_mem h).2.1
      omega
    have := Nat.sInf_le hmem
    omega
  · rw [nextVis, if_neg h] at h2
    intro hs
    exact h ⟨s, h1, le_of_lt h2, hs⟩

/-- If the walk is at `c` at a time `> t`, the next visit to `c` after `t` comes
strictly after `t`. -/
lemma lt_nextVis {c b0 t : ℕ} (hb : p b0 = c) (ht : t < b0) : t < nextVis p c b0 t := by
  have h : (visAfter p c b0 t).Nonempty := ⟨b0, ht, le_refl _, hb⟩
  exact (nextVis_mem h).1

/-- The successive visits to the base column `c` of the loop `[a0, b0]`. -/
noncomputable def visSeq (p : ℕ → ℕ) (c b0 a0 : ℕ) : ℕ → ℕ
  | 0 => a0
  | (j + 1) => nextVis p c b0 (visSeq p c b0 a0 j)

@[simp] lemma visSeq_zero (p : ℕ → ℕ) (c b0 a0 : ℕ) : visSeq p c b0 a0 0 = a0 := rfl

@[simp] lemma visSeq_succ (p : ℕ → ℕ) (c b0 a0 : ℕ) (j : ℕ) :
    visSeq p c b0 a0 (j + 1) = nextVis p c b0 (visSeq p c b0 a0 j) := rfl

lemma visSeq_le {c b0 a0 : ℕ} (hab : a0 ≤ b0) : ∀ j, visSeq p c b0 a0 j ≤ b0 := by
  intro j
  induction j with
  | zero => exact hab
  | succ j _ => exact nextVis_le

lemma visSeq_mono_step {c b0 a0 : ℕ} (hab : a0 ≤ b0) (j : ℕ) :
    visSeq p c b0 a0 j ≤ visSeq p c b0 a0 (j + 1) :=
  le_nextVis (visSeq_le hab j)

lemma visSeq_mono {c b0 a0 : ℕ} (hab : a0 ≤ b0) : Monotone (visSeq p c b0 a0) :=
  monotone_nat_of_le_succ (visSeq_mono_step hab)

lemma pos_visSeq {c b0 a0 : ℕ} (ha : p a0 = c) (hb : p b0 = c) :
    ∀ j, p (visSeq p c b0 a0 j) = c := by
  intro j
  cases j with
  | zero => exact ha
  | succ j => exact pos_nextVis hb

/-- Between two consecutive visits to the base column, the walk is not at the
base column. -/
lemma visSeq_no_mid {c b0 a0 : ℕ} {j s : ℕ} (h1 : visSeq p c b0 a0 j < s)
    (h2 : s < visSeq p c b0 a0 (j + 1)) : p s ≠ c :=
  nextVis_no_mid h1 h2

/-- As long as the loop is not over, the visits strictly increase. -/
lemma visSeq_lt {c b0 a0 : ℕ} (hb : p b0 = c) {j : ℕ}
    (hj : visSeq p c b0 a0 j < b0) : visSeq p c b0 a0 j < visSeq p c b0 a0 (j + 1) :=
  lt_nextVis hb hj

/-- **The visits to the base column stabilise.**  If the loop `[a0, b0]` visits
every column at most `k` times, then after `k` steps the sequence of visits to
the base column has reached `b0`. -/
lemma visSeq_stab {c b0 a0 k : ℕ} (hab : a0 ≤ b0) (ha : p a0 = c) (hb : p b0 = c)
    (hk : VisitsLe p a0 b0 k) : visSeq p c b0 a0 k = b0 := by
  classical
  by_contra hne
  have hlt : visSeq p c b0 a0 k < b0 := lt_of_le_of_ne (visSeq_le hab k) hne
  -- the first `k + 1` visits are pairwise distinct
  have hstrict : ∀ j, j < k → visSeq p c b0 a0 j < visSeq p c b0 a0 (j + 1) := by
    intro j hj
    have : visSeq p c b0 a0 j ≤ visSeq p c b0 a0 k := visSeq_mono hab (le_of_lt hj)
    exact visSeq_lt hb (by omega)
  have hmono : StrictMonoOn (visSeq p c b0 a0) (Set.Iic k) := by
    intro x hx y hy hxy
    have : ∀ d, ∀ x, x + d ≤ k → 0 < d → visSeq p c b0 a0 x < visSeq p c b0 a0 (x + d) := by
      intro d
      induction d with
      | zero => intro x _ h; omega
      | succ d ih =>
          intro x hx hd
          rcases Nat.eq_zero_or_pos d with rfl | hdpos
          · simpa using hstrict x (by omega)
          · have h1 := ih x (by omega) hdpos
            have h2 := hstrict (x + d) (by omega)
            rw [show x + (d + 1) = x + d + 1 by omega]
            omega
    have := this (y - x) x (by simp only [Set.mem_Iic] at hy; omega) (by omega)
    rwa [show x + (y - x) = y by omega] at this
  set s : Finset ℕ := (Finset.range (k + 1)).image (visSeq p c b0 a0) with hs
  have hcard : s.card = k + 1 := by
    rw [hs, Finset.card_image_of_injOn, Finset.card_range]
    intro x hx y hy hxy
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    rcases lt_trichotomy x y with h | h | h
    · exact absurd hxy (ne_of_lt (hmono (by simp only [Set.mem_Iic]; omega)
        (by simp only [Set.mem_Iic]; omega) h))
    · exact h
    · exact absurd hxy.symm (ne_of_lt (hmono (by simp only [Set.mem_Iic]; omega)
        (by simp only [Set.mem_Iic]; omega) h))
  have hall : ∀ t ∈ s, a0 ≤ t ∧ t ≤ b0 ∧ p t = c := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ht
    exact ⟨by simpa using visSeq_mono hab (Nat.zero_le j), visSeq_le hab j,
      pos_visSeq ha hb j⟩
  have := hk c s hall
  omega

/-! ### The furthest column of an excursion -/

/-- The rightmost column visited by the walk during `[a, b]`. -/
noncomputable def excMax (p : ℕ → ℕ) (a b : ℕ) : ℕ := sSup (p '' Set.Icc a b)

/-- The leftmost column visited by the walk during `[a, b]`. -/
noncomputable def excMin (p : ℕ → ℕ) (a b : ℕ) : ℕ := sInf (p '' Set.Icc a b)

lemma image_Icc_nonempty {a b : ℕ} (hab : a ≤ b) : (p '' Set.Icc a b).Nonempty :=
  ⟨p a, a, by simp [hab], rfl⟩

lemma image_Icc_bddAbove (p : ℕ → ℕ) (a b : ℕ) : BddAbove (p '' Set.Icc a b) :=
  ((Set.finite_Icc a b).image p).bddAbove

lemma excMax_mem {a b : ℕ} (hab : a ≤ b) : excMax p a b ∈ p '' Set.Icc a b :=
  Nat.sSup_mem (image_Icc_nonempty hab) (image_Icc_bddAbove p a b)

lemma excMin_mem {a b : ℕ} (hab : a ≤ b) : excMin p a b ∈ p '' Set.Icc a b :=
  Nat.sInf_mem (image_Icc_nonempty hab)

lemma le_excMax {a b t : ℕ} (h1 : a ≤ t) (h2 : t ≤ b) : p t ≤ excMax p a b :=
  le_csSup (image_Icc_bddAbove p a b) ⟨t, by simp [h1, h2], rfl⟩

lemma excMin_le {a b t : ℕ} (h1 : a ≤ t) (h2 : t ≤ b) : excMin p a b ≤ p t :=
  Nat.sInf_le ⟨t, by simp [h1, h2], rfl⟩

lemma visited_excMax {a b : ℕ} (hab : a ≤ b) : Visited p a b (excMax p a b) := by
  obtain ⟨t, ht, hpt⟩ := excMax_mem (p := p) hab
  simp only [Set.mem_Icc] at ht
  exact ⟨t, ht.1, ht.2, hpt⟩

lemma visited_excMin {a b : ℕ} (hab : a ≤ b) : Visited p a b (excMin p a b) := by
  obtain ⟨t, ht, hpt⟩ := excMin_mem (p := p) hab
  simp only [Set.mem_Icc] at ht
  exact ⟨t, ht.1, ht.2, hpt⟩

/-- The column of the excursion `[a, b]` that is furthest from its base column:
the rightmost one if the excursion goes to the right, the leftmost one if it
goes to the left. -/
noncomputable def excCol (p : ℕ → ℕ) (a b : ℕ) : ℕ :=
  if p a < p (a + 1) then excMax p a b else excMin p a b

/-- The cutting point of the excursion `[a, b]`: the first visit to the column
furthest from the base column. -/
noncomputable def excSplit (p : ℕ → ℕ) (a b : ℕ) : ℕ := firstV p a b (excCol p a b)

lemma visited_excCol {a b : ℕ} (hab : a ≤ b) : Visited p a b (excCol p a b) := by
  rw [excCol]
  split
  · exact visited_excMax hab
  · exact visited_excMin hab

lemma excSplit_bounds {a b : ℕ} (hab : a ≤ b) : a ≤ excSplit p a b ∧ excSplit p a b ≤ b :=
  le_firstV_bounds (visited_excCol hab)

lemma pos_excSplit {a b : ℕ} (hab : a ≤ b) : p (excSplit p a b) = excCol p a b :=
  pos_firstV (visited_excCol hab)

/-- Before the cutting point, the excursion has not reached its furthest
column. -/
lemma excSplit_first {a b : ℕ} (hab : a ≤ b) {t : ℕ} (h1 : a ≤ t) (h2 : t < excSplit p a b) :
    p t ≠ excCol p a b := by
  intro h
  have hb := (excSplit_bounds (p := p) hab).2
  have : excSplit p a b ≤ t := firstV_le ⟨h1, by omega, h⟩
  omega

/-! ### Characterising the furthest column -/

lemma excMax_eq {a b m : ℕ} (hbd : ∀ t, a ≤ t → t ≤ b → p t ≤ m)
    (hatt : ∃ t, a ≤ t ∧ t ≤ b ∧ p t = m) : excMax p a b = m := by
  obtain ⟨t, ht1, ht2, ht3⟩ := hatt
  refine le_antisymm ?_ ?_
  · obtain ⟨s, hs, hps⟩ := excMax_mem (p := p) (le_trans ht1 ht2)
    simp only [Set.mem_Icc] at hs
    rw [← hps]
    exact hbd s hs.1 hs.2
  · rw [← ht3]
    exact le_excMax ht1 ht2

lemma excMin_eq {a b m : ℕ} (hbd : ∀ t, a ≤ t → t ≤ b → m ≤ p t)
    (hatt : ∃ t, a ≤ t ∧ t ≤ b ∧ p t = m) : excMin p a b = m := by
  obtain ⟨t, ht1, ht2, ht3⟩ := hatt
  refine le_antisymm ?_ ?_
  · rw [← ht3]
    exact excMin_le ht1 ht2
  · obtain ⟨s, hs, hps⟩ := excMin_mem (p := p) (le_trans ht1 ht2)
    simp only [Set.mem_Icc] at hs
    rw [← hps]
    exact hbd s hs.1 hs.2

/-- A one-sided excursion to the right has its furthest column to the right. -/
lemma excCol_right (hw : IsWalk p T) {a b c : ℕ} (hbT : b ≤ T) (hab : a < b) (ha : p a = c)
    (hb : p b = c) (hside : ∀ t, a < t → t < b → c < p t) :
    excCol p a b = excMax p a b := by
  have hne1 : a + 1 < b := by
    rcases eq_or_lt_of_le (show a + 1 ≤ b by omega) with h | h
    · exfalso
      rcases hw a (by omega) with hstep | hstep <;> rw [← h] at hb <;> omega
    · exact h
  have h1 := hside (a + 1) (by omega) (by omega)
  rw [excCol, if_pos (by omega)]

/-- A one-sided excursion to the left has its furthest column to the left. -/
lemma excCol_left (hw : IsWalk p T) {a b c : ℕ} (hbT : b ≤ T) (hab : a < b) (ha : p a = c)
    (hb : p b = c) (hside : ∀ t, a < t → t < b → p t < c) :
    excCol p a b = excMin p a b := by
  have hne1 : a + 1 < b := by
    rcases eq_or_lt_of_le (show a + 1 ≤ b by omega) with h | h
    · exfalso
      rcases hw a (by omega) with hstep | hstep <;> rw [← h] at hb <;> omega
    · exact h
  have h1 := hside (a + 1) (by omega) (by omega)
  rw [excCol, if_neg (by omega)]

/-! ### The two halves of an excursion -/

/-- A one-sided excursion to the right stays between its base column and its
furthest column. -/
lemma exc_range_right {a b c : ℕ} (hab : a ≤ b) (ha : p a = c) (hb : p b = c)
    (hside : ∀ t, a < t → t < b → c < p t) {t : ℕ} (h1 : a ≤ t) (h2 : t ≤ b) :
    c ≤ p t ∧ p t ≤ excMax p a b := by
  refine ⟨?_, le_excMax h1 h2⟩
  rcases eq_or_lt_of_le h1 with h | h
  · subst h; omega
  · rcases eq_or_lt_of_le h2 with h' | h'
    · subst h'; omega
    · exact le_of_lt (hside t h h')

/-- A one-sided excursion to the left stays between its furthest column and its
base column. -/
lemma exc_range_left {a b c : ℕ} (hab : a ≤ b) (ha : p a = c) (hb : p b = c)
    (hside : ∀ t, a < t → t < b → p t < c) {t : ℕ} (h1 : a ≤ t) (h2 : t ≤ b) :
    excMin p a b ≤ p t ∧ p t ≤ c := by
  refine ⟨excMin_le h1 h2, ?_⟩
  rcases eq_or_lt_of_le h1 with h | h
  · subst h; omega
  · rcases eq_or_lt_of_le h2 with h' | h'
    · subst h'; omega
    · exact le_of_lt (hside t h h')

/-- **The two halves of a one-sided excursion to the right have smaller
width.**  This is `Walk.loop_first_half_visits` and
`Walk.loop_second_half_visits`, with the cutting point named. -/
lemma exc_halves_visitsLe_right (hw : IsWalk p T) {a b c k : ℕ} (hbT : b ≤ T) (hab : a < b)
    (hk : VisitsLe p a b k) (ha : p a = c) (hb : p b = c)
    (hside : ∀ t, a < t → t < b → c < p t) :
    VisitsLe p a (excSplit p a b) (k - 1) ∧ VisitsLe p (excSplit p a b) b (k - 1) := by
  have hab' : a ≤ b := le_of_lt hab
  have hcol : excCol p a b = excMax p a b := excCol_right hw hbT hab ha hb hside
  have hmvis : Visited p a b (excMax p a b) := visited_excMax hab'
  have hmax : ∀ t, a ≤ t → t ≤ b → p t ≤ excMax p a b := fun _ h1 h2 => le_excMax h1 h2
  have hne1 : a + 1 < b := by
    rcases eq_or_lt_of_le (show a + 1 ≤ b by omega) with h | h
    · exfalso
      rcases hw a (by omega) with hstep | hstep <;> rw [← h] at hb <;> omega
    · exact h
  have hcm : c < excMax p a b := by
    have h1 := hside (a + 1) (by omega) (by omega)
    have h2 := le_excMax (p := p) (a := a) (b := b) (t := a + 1) (by omega) (by omega)
    omega
  have hsplit : excSplit p a b = firstV p a b (excMax p a b) := by rw [excSplit, hcol]
  refine ⟨?_, ?_⟩
  · intro y s hs
    rw [hsplit] at hs
    have := loop_first_half_visits hw hbT hab' hk ha hb hcm hmvis hside hmax hs
    omega
  · intro y s hs
    rw [hsplit] at hs
    have := loop_second_half_visits hw hbT hab' hk ha hb hcm hmvis hside hmax hs
    omega

/-! ### Mirroring an excursion -/

lemma visitSet_mir {D a b x : ℕ} (hD : ∀ t, a ≤ t → t ≤ b → p t ≤ D) (hx : x ≤ D) :
    visitSet (mir D p) a b (D - x) = visitSet p a b x := by
  ext t
  simp only [visitSet, Set.mem_setOf_eq, mir]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have := hD t h1 h2
    exact ⟨h1, h2, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by omega⟩

lemma firstV_mir {D a b x : ℕ} (hD : ∀ t, a ≤ t → t ≤ b → p t ≤ D) (hx : x ≤ D) :
    firstV (mir D p) a b (D - x) = firstV p a b x := by
  rw [firstV, firstV, visitSet_mir hD hx]

lemma excMax_mir {D a b : ℕ} (hab : a ≤ b) :
    excMax (mir D p) a b = D - excMin p a b := by
  refine excMax_eq ?_ ?_
  · intro t h1 h2
    have h3 := excMin_le (p := p) h1 h2
    simp only [mir]
    omega
  · obtain ⟨t, ht, hpt⟩ := excMin_mem (p := p) hab
    simp only [Set.mem_Icc] at ht
    exact ⟨t, ht.1, ht.2, by simp only [mir, hpt]⟩

/-- **The two halves of an excursion have smaller width.**  An excursion is a
piece of the walk that starts and ends at the base column `c` and does not
visit `c` in between; cut at the first visit to the column furthest from `c`,
both halves visit every column at most `k - 1` times. -/
theorem exc_halves_visitsLe (hw : IsWalk p T) {a b c k : ℕ} (hbT : b ≤ T) (hab : a < b)
    (hk : VisitsLe p a b k) (ha : p a = c) (hb : p b = c)
    (hmid : ∀ t, a < t → t < b → p t ≠ c) :
    VisitsLe p a (excSplit p a b) (k - 1) ∧ VisitsLe p (excSplit p a b) b (k - 1) := by
  rcases loop_one_sided hw hbT ha hmid with hside | hside
  · exact exc_halves_visitsLe_right hw hbT hab hk ha hb hside
  · obtain ⟨D, -, hD0⟩ := exists_max_col p (show (0 : ℕ) ≤ b from Nat.zero_le _)
    have hD' : ∀ t, t ≤ b → p t ≤ D := fun t ht => hD0 t (Nat.zero_le _) ht
    have hDab : ∀ t, a ≤ t → t ≤ b → p t ≤ D := fun t _ ht => hD' t ht
    have hwm : IsWalk (mir D p) b := isWalk_mir (hw.of_le hbT) hD'
    have hkm : VisitsLe (mir D p) a b k := visitsLe_mir hDab hk
    have ham : mir D p a = D - c := by simp [mir, ha]
    have hbm : mir D p b = D - c := by simp [mir, hb]
    have hsidem : ∀ t, a < t → t < b → D - c < mir D p t := by
      intro t h1 h2
      have h3 := hside t h1 h2
      have h4 := hD' t (by omega)
      have h5 : c ≤ D := by rw [← ha]; exact hD' a (by omega)
      simp only [mir]
      omega
    have hsb : excSplit p a b ≤ b := (excSplit_bounds (p := p) (le_of_lt hab)).2
    have heq : excSplit (mir D p) a b = excSplit p a b := by
      have hcolm : excCol (mir D p) a b = excMax (mir D p) a b :=
        excCol_right hwm (le_refl b) hab ham hbm hsidem
      have hcolp : excCol p a b = excMin p a b := excCol_left hw hbT hab ha hb hside
      have hmm : excMax (mir D p) a b = D - excMin p a b := excMax_mir (le_of_lt hab)
      have hminD : excMin p a b ≤ D := by
        have h1 := excMin_le (p := p) (a := a) (b := b) (t := a) (le_refl a) (le_of_lt hab)
        have h2 := hD' a (by omega)
        omega
      rw [excSplit, excSplit, hcolm, hcolp, hmm, firstV_mir hDab hminD]
    obtain ⟨h1, h2⟩ := exc_halves_visitsLe_right hwm (le_refl b) hab hkm ham hbm hsidem
    rw [heq] at h1 h2
    exact ⟨visitsLe_of_mir (fun t _ ht => hD' t (le_trans ht hsb)) h1,
      visitsLe_of_mir (fun t _ ht => hD' t ht) h2⟩

end Walk

end Lax916827Proofs.Transducers
