/-
Confinement of the pieces of the record-breaker decomposition of a walk.

This file continues `RequestProject/PartC/SnakeRec.lean`.  There the trajectory
of a run of width at most `k` was cut, at the record-breaking columns

  `x₀ < x₁ < ⋯ < x_N`  (`x i = Walk.recSeq p a b i`),

into the *loop parts* `[f i, l i]` and the *progress parts* `[l i, f (i+1)]`,
where `f i` and `l i` are the first and the last visit to `x i`
(`Walk.recFirst`, `Walk.recLast`), and each of these pieces was shown to have
width at most `k - 1` (`Walk.walk_splitsInto_pred`).

For the induction step of the book's snake lemma one needs more: the pieces must
not only be narrow, they must also be *confined* to a bounded part of the input,
so that the rational function that produces one copy of the input for each piece
has linear growth.  This is the point of the book's step 4 in the proof of the
lemma "the output of a snake graph is regular": *the loop and the progress parts
of the `i`-th record-breaker are contained in the block `wᵢ₋₁ # wᵢ`*, i.e. in
the columns strictly between `x (i-1)` and `x (i+1)`, inclusive of the right
endpoint.  The three ingredients are proved here:

* `Walk.recSeq_lt_of_recLast_lt`: after the last visit to a record-breaking
  column the walk stays strictly to the right of it — this is the book's "after
  visiting this record-breaker, the previous one is never visited";
* `Walk.le_recSeq_of_le_recFirst`: up to the first visit to a record-breaking
  column the walk stays weakly to its left;
* `Walk.lt_recSeq_succ_of_le_recLast`: up to the last visit to the `i`-th
  record-breaking column the walk stays strictly to the left of the
  `(i+1)`-st one.

They are assembled in `Walk.loop_confined` and `Walk.progress_confined`, and
transported to the trajectory of a run in `TwoWay.run_loop_confined` and
`TwoWay.run_progress_confined`.
-/
import Lax916827Proofs.Source.PartC.SnakeRec
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace Walk

variable {p : ℕ → ℕ} {T : ℕ}

/-! ### The record-breaking columns increase -/

lemma recSeq_le_succ (a b i : ℕ) : recSeq p a b i ≤ recSeq p a b (i + 1) := by
  by_cases h : RecStable p a b i
  · rw [recSeq_succ_of_stable h]
  · exact le_of_lt (lt_recSeq_succ h)

lemma recSeq_mono {a b : ℕ} : Monotone (recSeq p a b) :=
  monotone_nat_of_le_succ (recSeq_le_succ a b)

/-- Every record-breaking column is at least the starting column. -/
lemma start_le_recSeq (a b i : ℕ) : p a ≤ recSeq p a b i := by
  simpa using recSeq_mono (p := p) (a := a) (b := b) (Nat.zero_le i)

/-- The last visit to the `i`-th record-breaking column is strictly before the
first visit to the `(i+1)`-st one. -/
lemma recLast_lt_recFirst_succ {a b i : ℕ} (h : ¬ RecStable p a b i) :
    recLast p a b i < recFirst p a b (i + 1) := by
  have := lastV_lt_firstV_recNext (p := p) (a := a) (b := b) (not_not.1 h)
  rw [recFirst, recSeq_succ_of_not_stable h, recLast]
  omega

/-! ### Confinement on the left: the previous record-breaker is never revisited -/

/-- **After the last visit to a record-breaking column the walk stays strictly
to the right of it.**  This is the book's "after visiting this record-breaker,
the previous one is never visited", and it is what confines the loop and the
progress parts of the `(i+1)`-st record-breaker to the right of `x i`. -/
theorem recSeq_lt_of_recLast_lt (hw : IsWalk p T) {a b i : ℕ} (hab : a ≤ b) (hbT : b ≤ T)
    (hns : ¬ RecStable p a b i) {t : ℕ} (ht1 : recLast p a b i < t) (ht2 : t ≤ b) :
    recSeq p a b i < p t := by
  set x := recSeq p a b i with hx
  set g := recFirst p a b (i + 1) with hg
  have hvis : Visited p a b x := visited_recSeq hab i
  have hlasta : a ≤ recLast p a b i :=
    (le_firstV_bounds hvis).1.trans (recFirst_le_recLast hab i)
  have hgt : recLast p a b i < g := recLast_lt_recFirst_succ hns
  have hgb : g ≤ b := (le_firstV_bounds (visited_recSeq hab (i + 1))).2
  have hgp : p g = recSeq p a b (i + 1) := pos_firstV (visited_recSeq hab (i + 1))
  have hxlt : x < recSeq p a b (i + 1) := lt_recSeq_succ hns
  -- no visit to `x` after its last visit
  have hne : ∀ s, recLast p a b i < s → s ≤ b → p s ≠ x := by
    intro s hs1 hs2 hs3
    have : s ≤ lastV p a b x := le_lastV ⟨by omega, hs2, hs3⟩
    rw [← recLast] at this
    omega
  by_contra hcon
  push_neg at hcon
  have hlt : p t < x := lt_of_le_of_ne hcon (hne t ht1 ht2)
  rcases Nat.lt_or_ge t g with hlt2 | hge2
  · -- `t` is before the first visit to the next record-breaker: cross `x` upwards
    obtain ⟨τ, hτ1, hτ2, hτ3⟩ := exists_eq_between (x := x) hw (le_of_lt hlt2)
      (le_trans hgb hbT) (Or.inl ⟨le_of_lt hlt, by rw [hgp]; omega⟩)
    exact hne τ (by omega) (by omega) hτ3
  · -- `t` is after the first visit to the next record-breaker: cross `x` downwards
    obtain ⟨τ, hτ1, hτ2, hτ3⟩ := exists_eq_between (x := x) hw hge2
      (le_trans ht2 hbT) (Or.inr ⟨le_of_lt hlt, by rw [hgp]; omega⟩)
    exact hne τ (by omega) (by omega) hτ3

/-! ### Confinement on the right -/

/-- Up to the first visit to a record-breaking column the walk stays weakly to
the left of it. -/
theorem le_recSeq_of_le_recFirst (hw : IsWalk p T) {a b j : ℕ} (hab : a ≤ b) (hbT : b ≤ T)
    {t : ℕ} (ht1 : a ≤ t) (ht2 : t ≤ recFirst p a b j) :
    p t ≤ recSeq p a b j := by
  by_contra hcon
  push_neg at hcon
  have hvis : Visited p a b (recSeq p a b j) := visited_recSeq hab j
  have htb : t ≤ b := le_trans ht2 (le_firstV_bounds hvis).2
  obtain ⟨τ, hτ1, hτ2, hτ3⟩ := exists_eq_between (x := recSeq p a b j) hw ht1
    (le_trans htb hbT) (Or.inl ⟨start_le_recSeq a b j, le_of_lt hcon⟩)
  have hge : recFirst p a b j ≤ τ := firstV_le ⟨hτ1, by omega, hτ3⟩
  have hτt : τ = t := by omega
  subst hτt
  omega

/-- Up to the last visit to the `i`-th record-breaking column the walk stays
strictly to the left of the `(i+1)`-st one. -/
theorem lt_recSeq_succ_of_le_recLast (hw : IsWalk p T) {a b i : ℕ} (hab : a ≤ b) (hbT : b ≤ T)
    (hns : ¬ RecStable p a b i) {t : ℕ} (ht1 : a ≤ t) (ht2 : t ≤ recLast p a b i) :
    p t < recSeq p a b (i + 1) := by
  refine loop_columns_lt hw hbT (visited_recSeq hab i) (lt_recSeq_succ hns)
    (start_le_recSeq a b i) ?_ ht1 ht2
  have := recLast_lt_recFirst_succ hns
  rw [recFirst] at this
  rw [← recLast]
  exact this

/-! ### The pieces of the decomposition are confined to two consecutive blocks -/

/-- **The loop part of the `(i+1)`-st record-breaking column is confined to the
columns `x i < · < x (i+2)`.**  Together with `progress_confined` this is the
book's statement that the loop and the progress parts of a record-breaker are
contained in the block `wᵢ₋₁ # wᵢ`. -/
theorem loop_confined (hw : IsWalk p T) {a b i : ℕ} (hab : a ≤ b) (hbT : b ≤ T)
    (hns : ¬ RecStable p a b i) (hns' : ¬ RecStable p a b (i + 1))
    {t : ℕ} (ht1 : recFirst p a b (i + 1) ≤ t) (ht2 : t ≤ recLast p a b (i + 1)) :
    recSeq p a b i < p t ∧ p t < recSeq p a b (i + 2) := by
  have hgt := recLast_lt_recFirst_succ hns
  have hb : t ≤ b := le_trans ht2 (recLast_le hab (i + 1))
  refine ⟨recSeq_lt_of_recLast_lt hw hab hbT hns (by omega) hb, ?_⟩
  exact lt_recSeq_succ_of_le_recLast hw hab hbT hns'
    (le_trans (le_recFirst hab (i + 1)) ht1) ht2

/-- **The progress part of the `(i+1)`-st record-breaking column is confined to
the columns `x i < · ≤ x (i+2)`.** -/
theorem progress_confined (hw : IsWalk p T) {a b i : ℕ} (hab : a ≤ b) (hbT : b ≤ T)
    (hns : ¬ RecStable p a b i)
    {t : ℕ} (ht1 : recLast p a b (i + 1) ≤ t) (ht2 : t ≤ recFirst p a b (i + 2)) :
    recSeq p a b i < p t ∧ p t ≤ recSeq p a b (i + 2) := by
  have hgt := recLast_lt_recFirst_succ hns
  have h1 : recFirst p a b (i + 1) ≤ recLast p a b (i + 1) := recFirst_le_recLast hab (i + 1)
  have hb : t ≤ b := le_trans ht2 (le_firstV_bounds (visited_recSeq hab (i + 2))).2
  refine ⟨recSeq_lt_of_recLast_lt hw hab hbT hns (by omega) hb, ?_⟩
  exact le_recSeq_of_le_recFirst hw hab hbT
    (le_trans (le_recFirst hab (i + 1)) (le_trans h1 ht1)) ht2

/-- The very first piece, the loop part of the source column together with the
following progress part, is confined to the columns `· ≤ x 1`; on the left it is
confined by the assumption, in `walk_splitsInto_pred`, that the source column is
the leftmost one. -/
theorem loop_confined_zero (hw : IsWalk p T) {a b : ℕ} (hab : a ≤ b) (hbT : b ≤ T)
    {t : ℕ} (ht1 : a ≤ t) (ht2 : t ≤ recFirst p a b 1) :
    p t ≤ recSeq p a b 1 :=
  le_recSeq_of_le_recFirst hw hab hbT ht1 ht2

end Walk

namespace TwoWay

variable {A B Q : Type}

/-- The confinement of the loop parts, for the trajectory of a run. -/
theorem run_loop_confined (M : TwoWay A B Q) (w : List A) {T : ℕ}
    (hT : cfgAt M w T = some Cfg.halt) {i : ℕ}
    (hns : ¬ Walk.RecStable (traj M w) 0 (T - 1) i)
    (hns' : ¬ Walk.RecStable (traj M w) 0 (T - 1) (i + 1))
    {t : ℕ} (ht1 : Walk.recFirst (traj M w) 0 (T - 1) (i + 1) ≤ t)
    (ht2 : t ≤ Walk.recLast (traj M w) 0 (T - 1) (i + 1)) :
    Walk.recSeq (traj M w) 0 (T - 1) i < traj M w t ∧
      traj M w t < Walk.recSeq (traj M w) 0 (T - 1) (i + 2) :=
  Walk.loop_confined (isWalk_traj M w hT) (Nat.zero_le _) (le_refl _) hns hns' ht1 ht2

/-- The confinement of the progress parts, for the trajectory of a run. -/
theorem run_progress_confined (M : TwoWay A B Q) (w : List A) {T : ℕ}
    (hT : cfgAt M w T = some Cfg.halt) {i : ℕ}
    (hns : ¬ Walk.RecStable (traj M w) 0 (T - 1) i)
    {t : ℕ} (ht1 : Walk.recLast (traj M w) 0 (T - 1) (i + 1) ≤ t)
    (ht2 : t ≤ Walk.recFirst (traj M w) 0 (T - 1) (i + 2)) :
    Walk.recSeq (traj M w) 0 (T - 1) i < traj M w t ∧
      traj M w t ≤ Walk.recSeq (traj M w) 0 (T - 1) (i + 2) :=
  Walk.progress_confined (isWalk_traj M w hT) (Nat.zero_le _) (le_refl _) hns ht1 ht2

end TwoWay

end Lax916827Proofs.Transducers
