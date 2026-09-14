/-
The combinatorics of the trajectory of a two-way run: *walks*.

This file is part of the proof of the hard half of Theorem `thm:2dfa-decomposition-into-primes` of
*Transducers* (M. Bojańczyk): the missing ingredient there is the book's snake
lemma (`Transducers.boundedWidth_isRegular`, stated in
`RequestProject/PartC/SnakeWidth.lean`), whose proof decomposes a run of width
`k` into *looping* parts and *progressing* parts along the *record-breaking*
columns.  That decomposition, together with the bounds on the widths of the
parts, is a statement about the sequence of columns visited by the run, and
about nothing else.  This file develops it for an arbitrary *walk*: a sequence
`p 0, p 1, …, p T` of natural numbers in which consecutive entries differ by
exactly one.

The main definitions are `Transducers.Walk.firstV` and `Transducers.Walk.lastV`
(the first and the last time a walk is at a given column, inside a given time
interval), `Transducers.Walk.recNext` (the next record-breaking column) and
`Transducers.Walk.recCol` (the sequence of record-breaking columns).  The main
results are:

* `recCol_tiling`: the time interval of the walk is tiled by the *loop* parts
  `[firstV xᵢ, lastV xᵢ]` and the *progress* parts `[lastV xᵢ, firstV xᵢ₊₁]` of
  the record-breaking columns;
* `loop_columns_lt` and `loop_columns_gt`: the loop part of `xᵢ` stays strictly
  between `xᵢ₋₁` and `xᵢ₊₁`;
* `progress_columns`: the progress part of `xᵢ` stays between `xᵢ` and `xᵢ₊₁`;
* `progress_visits_le`: the progress part of `xᵢ` visits every column at most
  `k - 1` times, if the whole walk visits every column at most `k` times.
-/
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Finite.Basic

namespace Lax916827Proofs.Transducers

namespace Walk

/-- A walk of length `T`: at each time `t < T` the position moves by one, either
to the right or to the left. -/
def IsWalk (p : ℕ → ℕ) (T : ℕ) : Prop :=
  ∀ t, t < T → p (t + 1) = p t + 1 ∨ p t = p (t + 1) + 1

variable {p : ℕ → ℕ} {T : ℕ}

lemma IsWalk.of_le (hw : IsWalk p T) {S : ℕ} (hS : S ≤ T) : IsWalk p S :=
  fun t ht => hw t (lt_of_lt_of_le ht hS)

/-! ### Intermediate values -/

/-- A walk that starts below `x` and ends above `x` is at `x` at some time in
between. -/
lemma exists_eq_up (hw : IsWalk p T) :
    ∀ (n a x : ℕ), a + n ≤ T → p a ≤ x → x ≤ p (a + n) →
      ∃ t, a ≤ t ∧ t ≤ a + n ∧ p t = x := by
  intro n
  induction n with
  | zero =>
      intro a x _ h1 h2
      simp only [Nat.add_zero] at h2
      exact ⟨a, le_refl _, by omega, by omega⟩
  | succ n ih =>
      intro a x hT h1 h2
      rcases eq_or_lt_of_le h1 with h | h
      · exact ⟨a, le_refl _, by omega, h⟩
      · have hstep := hw a (by omega)
        have h1' : p (a + 1) ≤ x := by rcases hstep with h' | h' <;> omega
        have h2' : x ≤ p (a + 1 + n) := by rw [show a + 1 + n = a + (n + 1) by omega]; exact h2
        obtain ⟨t, ht1, ht2, ht3⟩ := ih (a + 1) x (by omega) h1' h2'
        exact ⟨t, by omega, by omega, ht3⟩

/-- A walk that starts above `x` and ends below `x` is at `x` at some time in
between. -/
lemma exists_eq_down (hw : IsWalk p T) :
    ∀ (n a x : ℕ), a + n ≤ T → p (a + n) ≤ x → x ≤ p a →
      ∃ t, a ≤ t ∧ t ≤ a + n ∧ p t = x := by
  intro n
  induction n with
  | zero =>
      intro a x _ h1 h2
      simp only [Nat.add_zero] at h1
      exact ⟨a, le_refl _, by omega, by omega⟩
  | succ n ih =>
      intro a x hT h1 h2
      rcases eq_or_lt_of_le h2 with h | h
      · exact ⟨a, le_refl _, by omega, h.symm⟩
      · have hstep := hw a (by omega)
        have h2' : x ≤ p (a + 1) := by rcases hstep with h' | h' <;> omega
        have h1' : p (a + 1 + n) ≤ x := by rw [show a + 1 + n = a + (n + 1) by omega]; exact h1
        obtain ⟨t, ht1, ht2, ht3⟩ := ih (a + 1) x (by omega) h1' h2'
        exact ⟨t, by omega, by omega, ht3⟩

/-- Intermediate value theorem for walks. -/
lemma exists_eq_between (hw : IsWalk p T) {a b x : ℕ} (hab : a ≤ b) (hbT : b ≤ T)
    (h : (p a ≤ x ∧ x ≤ p b) ∨ (p b ≤ x ∧ x ≤ p a)) :
    ∃ t, a ≤ t ∧ t ≤ b ∧ p t = x := by
  obtain ⟨n, rfl⟩ : ∃ n, b = a + n := ⟨b - a, by omega⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact exists_eq_up hw n a x hbT h1 h2
  · exact exists_eq_down hw n a x hbT h1 h2

/-! ### First and last visit -/

/-- The set of times in the interval `[a, b]` at which the walk is at the
column `x`. -/
def visitSet (p : ℕ → ℕ) (a b x : ℕ) : Set ℕ := {t | a ≤ t ∧ t ≤ b ∧ p t = x}

/-- The walk visits the column `x` during the time interval `[a, b]`. -/
def Visited (p : ℕ → ℕ) (a b x : ℕ) : Prop := (visitSet p a b x).Nonempty

lemma visited_of (p : ℕ → ℕ) {a b x t : ℕ} (h1 : a ≤ t) (h2 : t ≤ b) (h3 : p t = x) :
    Visited p a b x := ⟨t, h1, h2, h3⟩

lemma visitSet_subset (p : ℕ → ℕ) (a b x : ℕ) : visitSet p a b x ⊆ Set.Iic b :=
  fun _ ht => ht.2.1

lemma bddAbove_visitSet (p : ℕ → ℕ) (a b x : ℕ) : BddAbove (visitSet p a b x) :=
  ⟨b, fun _ ht => ht.2.1⟩

/-- The first time in `[a, b]` at which the walk is at the column `x`. -/
noncomputable def firstV (p : ℕ → ℕ) (a b x : ℕ) : ℕ := sInf (visitSet p a b x)

/-- The last time in `[a, b]` at which the walk is at the column `x`. -/
noncomputable def lastV (p : ℕ → ℕ) (a b x : ℕ) : ℕ := sSup (visitSet p a b x)

lemma firstV_mem {a b x : ℕ} (h : Visited p a b x) : firstV p a b x ∈ visitSet p a b x :=
  Nat.sInf_mem h

lemma lastV_mem {a b x : ℕ} (h : Visited p a b x) : lastV p a b x ∈ visitSet p a b x :=
  Nat.sSup_mem h (bddAbove_visitSet p a b x)

lemma firstV_le {a b x t : ℕ} (ht : t ∈ visitSet p a b x) : firstV p a b x ≤ t :=
  Nat.sInf_le ht

lemma le_lastV {a b x t : ℕ} (ht : t ∈ visitSet p a b x) : t ≤ lastV p a b x :=
  le_csSup (bddAbove_visitSet p a b x) ht

lemma firstV_le_lastV {a b x : ℕ} (h : Visited p a b x) : firstV p a b x ≤ lastV p a b x :=
  le_lastV (firstV_mem h)

lemma pos_firstV {a b x : ℕ} (h : Visited p a b x) : p (firstV p a b x) = x :=
  (firstV_mem h).2.2

lemma pos_lastV {a b x : ℕ} (h : Visited p a b x) : p (lastV p a b x) = x :=
  (lastV_mem h).2.2

lemma le_firstV_bounds {a b x : ℕ} (h : Visited p a b x) :
    a ≤ firstV p a b x ∧ firstV p a b x ≤ b :=
  ⟨(firstV_mem h).1, (firstV_mem h).2.1⟩

lemma lastV_bounds {a b x : ℕ} (h : Visited p a b x) :
    a ≤ lastV p a b x ∧ lastV p a b x ≤ b :=
  ⟨(lastV_mem h).1, (lastV_mem h).2.1⟩

/-! ### Monotonicity of the first and the last visit -/

/-- Every column between the starting column and a visited column is visited. -/
lemma visited_of_between (hw : IsWalk p T) {a b x : ℕ} (hbT : b ≤ T)
    {t : ℕ} (ht1 : a ≤ t) (ht2 : t ≤ b)
    (h : (p a ≤ x ∧ x ≤ p t) ∨ (p t ≤ x ∧ x ≤ p a)) : Visited p a b x := by
  obtain ⟨s, hs1, hs2, hs3⟩ := exists_eq_between hw ht1 (le_trans ht2 hbT) h
  exact ⟨s, hs1, by omega, hs3⟩

/-- To the right of the starting column, the first visit is increasing. -/
lemma firstV_lt_firstV (hw : IsWalk p T) {a b x y : ℕ} (hbT : b ≤ T)
    (hax : p a ≤ x) (hxy : x < y) (hy : Visited p a b y) :
    Visited p a b x ∧ firstV p a b x < firstV p a b y := by
  have hfy := firstV_mem hy
  obtain ⟨s, hs1, hs2, hs3⟩ :=
    exists_eq_between hw hfy.1 (le_trans hfy.2.1 hbT)
      (Or.inl ⟨hax, by rw [hfy.2.2]; omega⟩)
  have hsx : s ∈ visitSet p a b x := ⟨hs1, le_trans hs2 hfy.2.1, hs3⟩
  refine ⟨⟨s, hsx⟩, ?_⟩
  have h1 : firstV p a b x ≤ s := firstV_le hsx
  have hne : s ≠ firstV p a b y := by
    intro h; rw [h, hfy.2.2] at hs3; omega
  omega

/-- To the left of the final column, the last visit is increasing. -/
lemma lastV_lt_lastV (hw : IsWalk p T) {a b x y : ℕ} (hbT : b ≤ T)
    (hby : y ≤ p b) (hxy : x < y) (hx : Visited p a b x) :
    Visited p a b y ∧ lastV p a b x < lastV p a b y := by
  have hlx := lastV_mem hx
  obtain ⟨s, hs1, hs2, hs3⟩ :=
    exists_eq_between hw hlx.2.1 hbT (Or.inl ⟨by rw [hlx.2.2]; omega, hby⟩)
  have hsy : s ∈ visitSet p a b y := ⟨le_trans hlx.1 hs1, hs2, hs3⟩
  refine ⟨⟨s, hsy⟩, ?_⟩
  have h1 : s ≤ lastV p a b y := le_lastV hsy
  have hne : s ≠ lastV p a b x := by
    intro h; rw [h, hlx.2.2] at hs3; omega
  omega


/-! ### Visit counts -/

/-- During the time interval `[a, b]`, the walk visits every column at most `k`
times. -/
def VisitsLe (p : ℕ → ℕ) (a b k : ℕ) : Prop :=
  ∀ x : ℕ, ∀ s : Finset ℕ, (∀ t ∈ s, a ≤ t ∧ t ≤ b ∧ p t = x) → s.card ≤ k

/-! ### The progress part between two consecutive record-breaking columns

Let `x < x'` be columns such that `x'` is first visited only after the last
visit to `x`.  The *progress part* is the piece of the walk between the last
visit to `x` and the first visit to `x'`. -/

/-- The progress part between `x` and `x'` stays between the columns `x` and
`x'`. -/
lemma progress_columns (hw : IsWalk p T) {a b x x' : ℕ} (hbT : b ≤ T)
    (hx : Visited p a b x) (hx' : Visited p a b x') (hxx' : x < x')
    {t : ℕ} (ht1 : lastV p a b x ≤ t) (ht2 : t ≤ firstV p a b x') :
    x ≤ p t ∧ p t ≤ x' := by
  obtain ⟨hl1, hl2, hl3⟩ := lastV_mem hx
  obtain ⟨hf1, hf2, hf3⟩ := firstV_mem hx'
  constructor
  · by_contra hcon
    push_neg at hcon
    have htne : lastV p a b x < t := by
      rcases eq_or_lt_of_le ht1 with h | h
      · exfalso; rw [← h] at hcon; omega
      · exact h
    obtain ⟨σ, hσ1, hσ2, hσ3⟩ := exists_eq_between hw ht2 (le_trans hf2 hbT)
        (Or.inl ⟨le_of_lt hcon, by omega⟩)
    have hσle : σ ≤ lastV p a b x := le_lastV ⟨by omega, by omega, hσ3⟩
    omega
  · by_contra hcon
    push_neg at hcon
    obtain ⟨τ, hτ1, hτ2, hτ3⟩ := exists_eq_between hw ht1 (le_trans ht2 (le_trans hf2 hbT))
        (Or.inl ⟨by omega, le_of_lt hcon⟩)
    have hτge : firstV p a b x' ≤ τ := firstV_le ⟨by omega, by omega, hτ3⟩
    have hτt : τ = t := by omega
    subst hτt
    omega

/-- The progress part between `x` and `x'` visits the column `x` only at its
first moment. -/
lemma progress_visits_left {a b x x' : ℕ} (hx : Visited p a b x)
    {s : Finset ℕ} (hs : ∀ t ∈ s, lastV p a b x ≤ t ∧ t ≤ firstV p a b x' ∧ p t = x)
    (hb : firstV p a b x' ≤ b) : s.card ≤ 1 := by
  classical
  obtain ⟨hl1, hl2, hl3⟩ := lastV_mem hx
  have hsub : s ⊆ {lastV p a b x} := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ := hs t ht
    have hle : t ≤ lastV p a b x := le_lastV ⟨by omega, le_trans h2 hb, h3⟩
    simp only [Finset.mem_singleton]
    omega
  simpa using Finset.card_le_card hsub

/-- The progress part between `x` and `x'` visits the column `x'` only at its
last moment. -/
lemma progress_visits_right {a b x x' : ℕ} (hx' : Visited p a b x')
    {s : Finset ℕ} (hs : ∀ t ∈ s, lastV p a b x ≤ t ∧ t ≤ firstV p a b x' ∧ p t = x')
    (ha : a ≤ lastV p a b x) : s.card ≤ 1 := by
  classical
  obtain ⟨hf1, hf2, hf3⟩ := firstV_mem hx'
  have hsub : s ⊆ {firstV p a b x'} := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ := hs t ht
    have hge : firstV p a b x' ≤ t := firstV_le ⟨by omega, by omega, h3⟩
    simp only [Finset.mem_singleton]
    omega
  simpa using Finset.card_le_card hsub

/-- The progress part between `x` and `x'` visits a column strictly between `x`
and `x'` at most `k - 1` times, if the walk visits every column at most `k`
times: such a column is already visited during the loop part of `x`, which is
over before the progress part starts. -/
lemma progress_visits_mid {a b x x' y k : ℕ} (hk : VisitsLe p a b k)
    (hy : Visited p a b y) (hyloop : firstV p a b y < lastV p a b x)
    {s : Finset ℕ} (hs : ∀ t ∈ s, lastV p a b x ≤ t ∧ t ≤ firstV p a b x' ∧ p t = y)
    (hb : firstV p a b x' ≤ b) : s.card + 1 ≤ k := by
  classical
  obtain ⟨hf1, hf2, hf3⟩ := firstV_mem hy
  have hnot : firstV p a b y ∉ s := by
    intro hmem
    have := (hs _ hmem).1
    omega
  have hcard : (insert (firstV p a b y) s).card = s.card + 1 :=
    Finset.card_insert_of_notMem hnot
  have hall : ∀ t ∈ insert (firstV p a b y) s, a ≤ t ∧ t ≤ b ∧ p t = y := by
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact ⟨hf1, hf2, hf3⟩
    · obtain ⟨h1, h2, h3⟩ := hs t ht
      exact ⟨by omega, le_trans h2 hb, h3⟩
  have := hk y _ hall
  omega

/-! ### The loop part of a record-breaking column

The *loop part* of a column `x` is the piece of the walk between the first and
the last visit to `x`. -/

/-- The loop part of `x` stays strictly to the right of a column `xm < x` whose
visits are all over before the loop part starts. -/
lemma loop_columns_gt (hw : IsWalk p T) {a b x xm : ℕ} (hbT : b ≤ T)
    (hx : Visited p a b x) (hlt : xm < x)
    (hover : lastV p a b xm < firstV p a b x)
    {t : ℕ} (ht1 : firstV p a b x ≤ t) (ht2 : t ≤ lastV p a b x) :
    xm < p t := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hf1, hf2, hf3⟩ := firstV_mem hx
  obtain ⟨hl1, hl2, hl3⟩ := lastV_mem hx
  obtain ⟨τ, hτ1, hτ2, hτ3⟩ := exists_eq_between hw ht1 (le_trans ht2 (le_trans hl2 hbT))
      (Or.inr ⟨hcon, by omega⟩)
  have hle : τ ≤ lastV p a b xm := le_lastV ⟨by omega, by omega, hτ3⟩
  omega

/-- Up to the end of the loop part of `x`, the walk stays strictly to the left
of a column `xp > x` that is first visited only after that loop part is over. -/
lemma loop_columns_lt (hw : IsWalk p T) {a b x xp : ℕ} (hbT : b ≤ T)
    (hx : Visited p a b x) (hlt : x < xp) (hsrc : p a ≤ x)
    (hafter : lastV p a b x < firstV p a b xp)
    {t : ℕ} (ht1 : a ≤ t) (ht2 : t ≤ lastV p a b x) :
    p t < xp := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hl1, hl2, hl3⟩ := lastV_mem hx
  have htb : t ≤ b := le_trans ht2 hl2
  have hy : Visited p a b (p t) := ⟨t, ht1, htb, rfl⟩
  have hfle : firstV p a b (p t) ≤ t := firstV_le ⟨ht1, htb, rfl⟩
  rcases eq_or_lt_of_le hcon with heq | hgt
  · rw [← heq] at hfle
    omega
  · obtain ⟨-, hmono⟩ := firstV_lt_firstV hw (x := xp) (y := p t) hbT
      (by omega) hgt hy
    omega


/-! ### An extra visit outside a subinterval -/

/-- If the walk visits the column `y` at a time outside the subinterval
`[u, v]`, then it visits `y` at most `k - 1` times inside `[u, v]`. -/
lemma visits_le_of_extra {a b k u v y τ : ℕ} (hk : VisitsLe p a b k)
    (hτ1 : a ≤ τ) (hτ2 : τ ≤ b) (hτ3 : p τ = y) (hout : τ < u ∨ v < τ)
    {s : Finset ℕ} (hs : ∀ t ∈ s, u ≤ t ∧ t ≤ v ∧ p t = y) (hu : a ≤ u) (hv : v ≤ b) :
    s.card + 1 ≤ k := by
  classical
  have hnot : τ ∉ s := by
    intro hmem
    obtain ⟨h1, h2, -⟩ := hs τ hmem
    omega
  have hcard : (insert τ s).card = s.card + 1 := Finset.card_insert_of_notMem hnot
  have hall : ∀ t ∈ insert τ s, a ≤ t ∧ t ≤ b ∧ p t = y := by
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact ⟨hτ1, hτ2, hτ3⟩
    · obtain ⟨h1, h2, h3⟩ := hs t ht
      exact ⟨by omega, by omega, h3⟩
  have := hk y _ hall
  omega

/-! ### Record-breaking columns

Following the book, the record-breaking columns of a walk that progresses from
left to right are defined greedily: the first one is the starting column, and
the one after `x` is the leftmost column to the right of `x` that is visited
only after the loop part of `x` is over. -/

/-- The candidates for the record-breaking column after `x`. -/
def recSet (p : ℕ → ℕ) (a b x : ℕ) : Set ℕ :=
  {y | x < y ∧ Visited p a b y ∧ lastV p a b x < firstV p a b y}

/-- The record-breaking column after `x`. -/
noncomputable def recNext (p : ℕ → ℕ) (a b x : ℕ) : ℕ := sInf (recSet p a b x)

lemma recNext_mem {a b x : ℕ} (h : (recSet p a b x).Nonempty) :
    recNext p a b x ∈ recSet p a b x := Nat.sInf_mem h

lemma recNext_le {a b x y : ℕ} (hy : y ∈ recSet p a b x) : recNext p a b x ≤ y :=
  Nat.sInf_le hy

lemma lt_recNext {a b x : ℕ} (h : (recSet p a b x).Nonempty) : x < recNext p a b x :=
  (recNext_mem h).1

lemma visited_recNext {a b x : ℕ} (h : (recSet p a b x).Nonempty) :
    Visited p a b (recNext p a b x) := (recNext_mem h).2.1

lemma lastV_lt_firstV_recNext {a b x : ℕ} (h : (recSet p a b x).Nonempty) :
    lastV p a b x < firstV p a b (recNext p a b x) := (recNext_mem h).2.2

/-- Every column strictly between `x` and the record-breaking column after `x`
is visited, and is already visited during the loop part of `x`. -/
lemma loop_of_lt_recNext (hw : IsWalk p T) {a b x y : ℕ} (hbT : b ≤ T)
    (h : (recSet p a b x).Nonempty) (hx : Visited p a b x)
    (hxy : x < y) (hy : y < recNext p a b x) :
    Visited p a b y ∧ firstV p a b y < lastV p a b x := by
  obtain ⟨-, hvis, hlt⟩ := recNext_mem h
  obtain ⟨hf1, hf2, hf3⟩ := firstV_mem hx
  obtain ⟨hl1, hl2, hl3⟩ := lastV_mem hx
  obtain ⟨g1, g2, g3⟩ := firstV_mem hvis
  have hfl := firstV_le_lastV hx
  obtain ⟨τ, hτ1, hτ2, hτ3⟩ :=
    exists_eq_between (x := y) hw
      (show firstV p a b x ≤ firstV p a b (recNext p a b x) by omega)
      (le_trans g2 hbT) (Or.inl ⟨by omega, by omega⟩)
  have hyv : Visited p a b y := ⟨τ, by omega, by omega, hτ3⟩
  refine ⟨hyv, ?_⟩
  have hnm : y ∉ recSet p a b x := fun hmem => absurd (recNext_le hmem) (by omega)
  have hnlt : ¬ (lastV p a b x < firstV p a b y) := fun hcon => hnm ⟨hxy, hyv, hcon⟩
  rcases eq_or_lt_of_le (not_lt.1 hnlt) with heq | hlt2
  · exfalso
    obtain ⟨e1, e2, e3⟩ := firstV_mem hyv
    rw [heq] at e3
    omega
  · exact hlt2

/-- If there is no record-breaking column after `x`, then every column to the
right of `x` is already visited during the loop part of `x`. -/
lemma loop_of_recSet_empty {a b x y : ℕ} (hempty : ¬ (recSet p a b x).Nonempty)
    (hx : Visited p a b x) (hxy : x < y) (hy : Visited p a b y) :
    firstV p a b y < lastV p a b x := by
  obtain ⟨hl1, hl2, hl3⟩ := lastV_mem hx
  have hnm : y ∉ recSet p a b x := fun hmem => hempty ⟨y, hmem⟩
  have hnlt : ¬ (lastV p a b x < firstV p a b y) := fun hcon => hnm ⟨hxy, hy, hcon⟩
  rcases eq_or_lt_of_le (not_lt.1 hnlt) with heq | hlt2
  · exfalso
    obtain ⟨e1, e2, e3⟩ := firstV_mem hy
    rw [heq] at e3
    omega
  · exact hlt2

/-! ### Looping parts

A *looping* part of a walk is a piece whose two endpoints are at the same
column `c`, the *base column*.  If the base column is not visited in between,
the piece stays on one side of it. -/

/-- A loop that does not return to its base column in between stays on one side
of the base column. -/
lemma loop_one_sided (hw : IsWalk p T) {a0 b0 c : ℕ} (hb0 : b0 ≤ T) (ha : p a0 = c)
    (hmid : ∀ t, a0 < t → t < b0 → p t ≠ c) :
    (∀ t, a0 < t → t < b0 → c < p t) ∨ (∀ t, a0 < t → t < b0 → p t < c) := by
  rcases Nat.lt_or_ge (a0 + 1) b0 with hlt | hge
  · rcases hw a0 (by omega) with hstep | hstep
    · left
      intro t ht1 ht2
      by_contra hcon
      push_neg at hcon
      obtain ⟨τ, hτ1, hτ2, hτ3⟩ :=
        exists_eq_between hw (show a0 + 1 ≤ t by omega) (le_trans (le_of_lt ht2) hb0)
          (Or.inr ⟨hcon, by omega⟩)
      exact (hmid τ (by omega) (by omega)) hτ3
    · right
      intro t ht1 ht2
      by_contra hcon
      push_neg at hcon
      obtain ⟨τ, hτ1, hτ2, hτ3⟩ :=
        exists_eq_between hw (show a0 + 1 ≤ t by omega) (le_trans (le_of_lt ht2) hb0)
          (Or.inl ⟨by omega, hcon⟩)
      exact (hmid τ (by omega) (by omega)) hτ3
  · left
    intro t ht1 ht2
    omega

/-- The furthest column of a loop is visited strictly fewer times than the
column just before it, and hence at most `k - 1` times. -/
lemma visits_furthest_lt (hw : IsWalk p T) {a0 b0 c m k : ℕ} (hb0 : b0 ≤ T) (hab : a0 ≤ b0)
    (hk : VisitsLe p a0 b0 k) (ha : p a0 = c) (hb : p b0 = c) (hcm : c < m)
    (hmax : ∀ t, a0 ≤ t → t ≤ b0 → p t ≤ m)
    {s : Finset ℕ} (hs : ∀ t ∈ s, a0 ≤ t ∧ t ≤ b0 ∧ p t = m) : s.card + 1 ≤ k := by
  classical
  have hk1 : 1 ≤ k := by
    have := hk c {a0} (by
      intro t ht
      simp only [Finset.mem_singleton] at ht
      subst ht
      exact ⟨le_refl _, hab, ha⟩)
    simpa using this
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simpa using hk1
  -- every visit to `m` is interior, and its neighbours are visits to `m - 1`
  have hint : ∀ t ∈ s, a0 < t ∧ t < b0 := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ := hs t ht
    constructor
    · rcases eq_or_lt_of_le h1 with h | h
      · exfalso; rw [← h] at h3; omega
      · exact h
    · rcases eq_or_lt_of_le h2 with h | h
      · exfalso; rw [h] at h3; omega
      · exact h
  have hnb : ∀ t ∈ s, p (t + 1) + 1 = m := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ := hs t ht
    obtain ⟨hi1, hi2⟩ := hint t ht
    rcases hw t (by omega) with hstep | hstep
    · exfalso
      have := hmax (t + 1) (by omega) (by omega)
      omega
    · omega
  have hnb' : ∀ t ∈ s, p (t - 1) + 1 = m := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ := hs t ht
    obtain ⟨hi1, hi2⟩ := hint t ht
    have hstep := hw (t - 1) (by omega)
    rw [show t - 1 + 1 = t by omega] at hstep
    rcases hstep with hstep | hstep
    · omega
    · exfalso
      have := hmax (t - 1) (by omega) (by omega)
      omega
  set t₀ := s.min' hne with ht₀
  have ht₀s : t₀ ∈ s := s.min'_mem hne
  have ht₀le : ∀ t ∈ s, t₀ ≤ t := fun t ht => s.min'_le t ht
  set s' : Finset ℕ := insert (t₀ - 1) (s.image (fun t => t + 1)) with hs'
  have hnotmem : (t₀ - 1) ∉ s.image (fun t => t + 1) := by
    intro hmem
    obtain ⟨t, ht, heq⟩ := Finset.mem_image.1 hmem
    have := ht₀le t ht
    omega
  have hcard : s'.card = s.card + 1 := by
    rw [hs', Finset.card_insert_of_notMem hnotmem,
      Finset.card_image_of_injective _ (fun x y h => by omega)]
  have hall : ∀ t ∈ s', a0 ≤ t ∧ t ≤ b0 ∧ p t = m - 1 := by
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · obtain ⟨hi1, hi2⟩ := hint t₀ ht₀s
      have := hnb' t₀ ht₀s
      exact ⟨by omega, by omega, by omega⟩
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ht
      obtain ⟨hi1, hi2⟩ := hint u hu
      have := hnb u hu
      exact ⟨by omega, by omega, by omega⟩
  have := hk (m - 1) s' hall
  omega


/-! ### The two halves of a one-sided loop

A one-sided loop is cut in two at the first visit to its furthest column.  Both
halves have smaller width than the loop itself: this is the induction step for
looping snakes in the book. -/

/-- A one-sided loop stays between its base column and its furthest column. -/
lemma loop_range {a0 b0 c m : ℕ} (ha : p a0 = c) (hb : p b0 = c)
    (hside : ∀ t, a0 < t → t < b0 → c < p t)
    (hmax : ∀ t, a0 ≤ t → t ≤ b0 → p t ≤ m)
    {t : ℕ} (ht1 : a0 ≤ t) (ht2 : t ≤ b0) : c ≤ p t ∧ p t ≤ m := by
  refine ⟨?_, hmax t ht1 ht2⟩
  rcases eq_or_lt_of_le ht1 with h | h
  · subst h; omega
  · rcases eq_or_lt_of_le ht2 with h' | h'
    · subst h'; omega
    · exact le_of_lt (hside t h h')

/-- A walk that is somewhere visits some column at least once. -/
lemma one_le_of_visitsLe {a0 b0 k : ℕ} (hk : VisitsLe p a0 b0 k) (hab : a0 ≤ b0) : 1 ≤ k := by
  classical
  have := hk (p a0) {a0} (by
    intro t ht
    simp only [Finset.mem_singleton] at ht
    subst ht
    exact ⟨le_refl _, hab, rfl⟩)
  simpa using this

/-- The first half of a one-sided loop -- from the base column to the first
visit of the furthest column -- visits every column at most `k - 1` times. -/
lemma loop_first_half_visits (hw : IsWalk p T) {a0 b0 c m k : ℕ} (hb0 : b0 ≤ T) (hab : a0 ≤ b0)
    (hk : VisitsLe p a0 b0 k) (ha : p a0 = c) (hb : p b0 = c) (hcm : c < m)
    (hmvis : Visited p a0 b0 m)
    (hside : ∀ t, a0 < t → t < b0 → c < p t)
    (hmax : ∀ t, a0 ≤ t → t ≤ b0 → p t ≤ m)
    {y : ℕ} {s : Finset ℕ}
    (hs : ∀ t ∈ s, a0 ≤ t ∧ t ≤ firstV p a0 b0 m ∧ p t = y) : s.card + 1 ≤ k := by
  classical
  obtain ⟨hf1, hf2, hf3⟩ := firstV_mem hmvis
  have hfb : firstV p a0 b0 m < b0 := by
    rcases eq_or_lt_of_le hf2 with h | h
    · exfalso; rw [h] at hf3; omega
    · exact h
  have h2k : 2 ≤ k := by
    have := visits_furthest_lt hw hb0 hab hk ha hb hcm hmax (s := {firstV p a0 b0 m})
      (by
        intro t ht
        simp only [Finset.mem_singleton] at ht
        subst ht
        exact ⟨hf1, hf2, hf3⟩)
    simpa using this
  by_cases hym : y = m
  · subst hym
    have hsub : s ⊆ {firstV p a0 b0 y} := by
      intro t ht
      obtain ⟨h1, h2, h3⟩ := hs t ht
      have := firstV_le (a := a0) (b := b0) (x := y) ⟨h1, le_trans h2 hf2, h3⟩
      simp only [Finset.mem_singleton]
      omega
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hcard
    omega
  by_cases hyc : y = c
  · subst hyc
    exact visits_le_of_extra hk hab (le_refl b0) hb (Or.inr hfb) hs (le_refl a0) hf2
  by_cases hyrange : c < y ∧ y < m
  · obtain ⟨hy1, hy2⟩ := hyrange
    obtain ⟨τ, hτ1, hτ2, hτ3⟩ :=
      exists_eq_between (x := y) hw hf2 hb0 (Or.inr ⟨by omega, by omega⟩)
    have hne : τ ≠ firstV p a0 b0 m := by
      intro h; rw [h] at hτ3; omega
    exact visits_le_of_extra hk (le_trans hf1 hτ1) hτ2 hτ3 (Or.inr (by omega)) hs
      (le_refl a0) hf2
  · have hsempty : s = ∅ := by
      by_contra hcon
      obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.2 hcon
      obtain ⟨h1, h2, h3⟩ := hs t ht
      have hr := loop_range ha hb hside hmax h1 (le_trans h2 hf2)
      rcases not_and_or.1 hyrange with h | h <;> omega
    subst hsempty
    simpa using (by omega : 1 ≤ k)

/-- The second half of a one-sided loop -- from the first visit of the furthest
column back to the base column -- visits every column at most `k - 1` times. -/
lemma loop_second_half_visits (hw : IsWalk p T) {a0 b0 c m k : ℕ} (hb0 : b0 ≤ T) (hab : a0 ≤ b0)
    (hk : VisitsLe p a0 b0 k) (ha : p a0 = c) (hb : p b0 = c) (hcm : c < m)
    (hmvis : Visited p a0 b0 m)
    (hside : ∀ t, a0 < t → t < b0 → c < p t)
    (hmax : ∀ t, a0 ≤ t → t ≤ b0 → p t ≤ m)
    {y : ℕ} {s : Finset ℕ}
    (hs : ∀ t ∈ s, firstV p a0 b0 m ≤ t ∧ t ≤ b0 ∧ p t = y) : s.card + 1 ≤ k := by
  classical
  obtain ⟨hf1, hf2, hf3⟩ := firstV_mem hmvis
  have hfa : a0 < firstV p a0 b0 m := by
    rcases eq_or_lt_of_le hf1 with h | h
    · exfalso; rw [← h] at hf3; omega
    · exact h
  by_cases hym : y = m
  · subst hym
    exact visits_furthest_lt hw hb0 hab hk ha hb hcm hmax
      (by
        intro t ht
        obtain ⟨h1, h2, h3⟩ := hs t ht
        exact ⟨by omega, h2, h3⟩)
  by_cases hyc : y = c
  · subst hyc
    exact visits_le_of_extra hk (le_refl a0) hab ha (Or.inl hfa) hs hf1 (le_refl b0)
  by_cases hyrange : c < y ∧ y < m
  · obtain ⟨hy1, hy2⟩ := hyrange
    obtain ⟨τ, hτ1, hτ2, hτ3⟩ :=
      exists_eq_between (x := y) hw hf1 (le_trans hf2 hb0) (Or.inl ⟨by omega, by omega⟩)
    have hne : τ ≠ firstV p a0 b0 m := by
      intro h; rw [h] at hτ3; omega
    exact visits_le_of_extra hk hτ1 (le_trans hτ2 hf2) hτ3 (Or.inl (by omega)) hs hf1
      (le_refl b0)
  · have hsempty : s = ∅ := by
      by_contra hcon
      obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.2 hcon
      obtain ⟨h1, h2, h3⟩ := hs t ht
      have hr := loop_range ha hb hside hmax (le_trans hf1 h1) h2
      rcases not_and_or.1 hyrange with h | h <;> omega
    subst hsempty
    have := one_le_of_visitsLe hk hab
    simpa using this

end Walk

end Lax916827Proofs.Transducers
