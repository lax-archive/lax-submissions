import Lax185574.TypeTreeSizes
import Lax185574.ResolveLift
import Lax185574.Width
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Lax185574Proofs.Legacy

/-!
Size bounds for the trees along a construction sequence (proof of
thm:mc, model-checking.tex, the paragraphs after "Now let t < m").

Resolved pairs only grow along a construction sequence, so balls only
grow, and the number of types realized in a set only grows with the
set. With lem:ball-tree-bound (`TypeTreeSizes`) this bounds the trees
of every partial graph of the sequence but the last by a polynomial in
the width, and the parameter `T` of lem:resolve-lift by
`(q + 1) (k + q) K`.
-/

namespace Lax185574Proofs.MC

open Lax185574.PartialGraphs Lax185574.ConstructionSequences Lax185574.Width
open Lax185574.TypeTrees Lax185574.WordEncoding Lax185574.FirstOrderTypes
open Lax185574.GaifmanGraph
open Lax3.DistFO (rhoMinus rhoPlus)

variable {n : ℕ}

theorem resolved_le_of_step {G H : PartialGraph (Fin n)} (h : IsStep G H) :
    G.resolved ≤ H.resolved := by
  obtain ⟨P, Q, (⟨-, rfl⟩ | rfl | rfl)⟩ := h
  · exact le_rfl
  · exact sup_le_sup_right le_sup_left _
  · exact sup_le_sup_left le_sup_left _

theorem ball_mono {G H : PartialGraph (Fin n)} (h : G.resolved ≤ H.resolved) (r : ℕ)
    (v : Fin n) : G.ball r v ⊆ H.ball r v := by
  rintro u ⟨p, hp⟩
  exact ⟨p.mapLe h, by rw [SimpleGraph.Walk.length_mapLe]; exact hp⟩

theorem partialTypeCount_mono (G : PartialGraph (Fin n)) (k q : ℕ) {X Y : Set (Fin n)}
    (h : X ⊆ Y) : partialTypeCount G k q X ≤ partialTypeCount G k q Y := by
  unfold partialTypeCount typeCount types
  apply Set.ncard_le_ncard
  · exact Set.image_mono fun v hv i => h (hv i)
  · exact (Set.toFinite _).image _

/-- Every term of the maximum defining the width is at most the width. -/
theorem le_width (r q : ℕ) (s : List (PartialGraph (Fin n))) {t : ℕ} (ht : t + 1 < s.length)
    (v : Fin n) : partialTypeCount s[t] q q (s[t + 1].ball r v) ≤ width r q s := by
  classical
  refine le_csSup ?_ ⟨t, ht, v, rfl⟩
  refine ⟨(Finset.univ : Finset (Fin s.length × Fin n)).sup fun p =>
    if h : p.1.val + 1 < s.length then partialTypeCount s[p.1.val] q q (s[p.1.val + 1].ball r p.2)
    else 0, ?_⟩
  rintro K ⟨t', ht', v', rfl⟩
  have := Finset.le_sup (f := fun p : Fin s.length × Fin n =>
    if h : p.1.val + 1 < s.length then partialTypeCount s[p.1.val] q q (s[p.1.val + 1].ball r p.2)
    else 0) (Finset.mem_univ (⟨t', by omega⟩, v'))
  simpa [ht'] using this

/-- The type count of a ball of `s[t]` is at most the width, for every
`t` but the last. -/
theorem typeCount_ball_le_width {s : List (PartialGraph (Fin n))} (hstep : ∀ (t : ℕ)
    (ht : t + 1 < s.length), IsStep s[t] s[t + 1]) {r d : ℕ} {t : ℕ} (ht : t + 1 < s.length)
    {ρ : ℕ} (hρ : ρ ≤ r) (v : Fin n) :
    partialTypeCount s[t] d d (s[t].ball ρ v) ≤ width r d s := by
  refine le_trans (partialTypeCount_mono _ _ _ ?_) (le_width r d s ht v)
  intro u hu
  obtain ⟨p, hp⟩ := ball_mono (resolved_le_of_step (hstep t ht)) ρ v hu
  exact ⟨p, by omega⟩

/-- **Tree sizes along a construction sequence.** For every partial graph
of the sequence but the last, the tree of every vertex has size
polynomial in the width, at radius `ρ⁺(1, q)` and depth
`ρ⁺(1, q) + 1 + q`. -/
theorem tree_length_le_width (q : ℕ) : ∃ c a : ℕ, ∀ (n : ℕ) (s : List (PartialGraph (Fin n))),
    (∀ (t : ℕ) (ht : t + 1 < s.length), IsStep s[t] s[t + 1]) →
    ∀ (t : ℕ) (ht : t + 1 < s.length) (v : Fin n),
      wordLength (tree s[t] 1 q ![v]) ≤
        c * (width (rhoPlus 1 q) (rhoPlus 1 q + 1 + q) s + 1) ^ a := by
  obtain ⟨c, a, h⟩ := Lax185574.TypeTreeSizes.tree_length_le 1 q le_rfl
  refine ⟨c, a, fun n s hstep t ht v => le_trans (h n s[t] v) ?_⟩
  gcongr
  exact typeCount_ball_le_width hstep ht le_rfl v

/-- The sets of trees counted by the parameter `T`, for one rank and
one arity. -/
theorem ncard_trees_finite (G : PartialGraph (Fin n)) (k q i ℓ : ℕ) (X : Set (Fin n)) :
    {τ : TypeTree | ∃ v : Fin ℓ → Fin n, (∀ j, v j ∈ X) ∧ τ = tree G (k + i) (q - i) v}.Finite := by
  refine ((Set.finite_range fun v : Fin ℓ → Fin n => tree G (k + i) (q - i) v)).subset ?_
  rintro τ ⟨v, -, rfl⟩
  exact ⟨v, rfl⟩

/-- **The parameter `T` of lem:resolve-lift.** For a step `G → H` of a
construction sequence, `T ≤ (q + 1) (k + q) K` where `K` bounds the
type counts of the balls of radius `ρ⁺(k, q)` of `H` in `G`. -/
theorem treeCount_le_count (G H : PartialGraph (Fin n)) (k q : ℕ) (hk : 1 ≤ k) (K : ℕ)
    (hK : ∀ a : Fin n, partialTypeCount G (rhoPlus k q + k + q) (rhoPlus k q + k + q)
      (H.ball (rhoPlus k q) a) ≤ K) :
    Lax185574.ResolveLift.treeCount G H k q ≤ (q + 1) * (k + q) * K := by
  classical
  unfold Lax185574.ResolveLift.treeCount
  refine Finset.sup_le fun a _ => ?_
  set X := H.ball (rhoPlus k q) a
  set S : ℕ × ℕ → Set TypeTree := fun p => if p.2 + 1 ≤ k + p.1 then
    {τ | ∃ v : Fin (p.2 + 1) → Fin n, (∀ j, v j ∈ X) ∧ τ = tree G (k + p.1) (q - p.1) v} else ∅
  set I := Finset.range (q + 1) ×ˢ Finset.range (k + q)
  have hsub : {τ : TypeTree | ∃ (i ℓ : ℕ) (v : Fin ℓ → Fin n), i ≤ q ∧ 1 ≤ ℓ ∧ ℓ ≤ k + i ∧
      (∀ j, v j ∈ X) ∧ τ = tree G (k + i) (q - i) v} ⊆ ⋃ p ∈ I, S p := by
    rintro τ ⟨i, ℓ, v, hi, h1, hℓ, hv, rfl⟩
    obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
    simp only [Set.mem_iUnion]
    refine ⟨(i, m), by simp only [I, Finset.mem_product, Finset.mem_range]; omega, ?_⟩
    simp only [S, if_pos (show m + 1 ≤ k + i by omega)]
    exact ⟨v, hv, rfl⟩
  have hfin : (⋃ p ∈ I, S p).Finite :=
    Set.Finite.biUnion I.finite_toSet fun p _ => by
      simp only [S]; split_ifs
      · exact ncard_trees_finite G k q p.1 (p.2 + 1) X
      · exact Set.finite_empty
  refine le_trans (Set.ncard_le_ncard hsub hfin) (le_trans (Finset.set_ncard_biUnion_le I S) ?_)
  have hterm : ∀ p ∈ I, (S p).ncard ≤ K := by
    intro p hp
    simp only [I, Finset.mem_product, Finset.mem_range] at hp
    by_cases hℓ : p.2 + 1 ≤ k + p.1
    · simp only [S, if_pos hℓ]
      exact le_trans (Lax185574.TypeTreeSizes.treeCount_le G k q hk p.1 (p.2 + 1) (by omega)
        (by omega) hℓ X) (hK a)
    · simp only [S, if_neg hℓ, Set.ncard_empty]; exact Nat.zero_le _
  calc ∑ p ∈ I, (S p).ncard ≤ ∑ _p ∈ I, K := Finset.sum_le_sum hterm
    _ = (q + 1) * (k + q) * K := by simp [I, Finset.card_product]

end Lax185574Proofs.MC
