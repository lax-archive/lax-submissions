import Mathlib.Tactic
import Lax17Proofs.Source.AppendixA3ClusterSplit

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy Lemma 7.5: the minimum initial set

This module formalizes the setup of the proof of Lemma 7.5.  The source first
chooses a minimum-cardinality set whose augmented boundary is large enough and
is `1/9`-well-linked.  The subsequent balanced-cut iteration is kept in a
separate module.
-/

namespace SimpleGraph
namespace AppendixA3Lemma75


open Finset

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}

/-! ## Augmented boundary at the whole vertex set -/

@[simp] theorem boundaryVertices_univ [Fintype V] :
    AppendixA3ClusterSplit.boundaryVertices G (Finset.univ : Finset V) = ∅ := by
  classical
  ext v
  simp [AppendixA3ClusterSplit.boundaryVertices]

@[simp] theorem augmentedBoundaryVertices_univ [Fintype V]
    (T : Finset V) :
    AppendixA3ClusterSplit.augmentedBoundaryVertices
        G (Finset.univ : Finset V) T = T := by
  classical
  simp [AppendixA3ClusterSplit.augmentedBoundaryVertices]

/-! ## Weakening the well-linkedness ratio -/

/-- Increasing the denominator weakens scaled cut well-linkedness. -/
theorem scaledEdgeWellLinkedIn_weaken_denominator [Fintype V]
    {C T : Finset V} {alphaNum alphaDen alphaDen' : ℕ}
    (h : Section46.ScaledEdgeWellLinkedIn
      G C T alphaNum alphaDen)
    (hden : alphaDen ≤ alphaDen') :
    Section46.ScaledEdgeWellLinkedIn
      G C T alphaNum alphaDen' := by
  classical
  refine ⟨h.1, h.2.1.trans hden, h.2.2.1, ?_⟩
  intro X Y hXC hYC hcover hdisj
  exact (h.2.2.2 X Y hXC hYC hcover hdisj).trans
    (Nat.mul_le_mul_right
      (Section44.edgeBoundary G X Y).card hden)

/-- The ratio conversion used after Lemma 2.11 in Observation 7.6.  Its exact
conclusion has denominator `2 * alphaDen + alphaNum`; because a scaled ratio
already satisfies `alphaNum <= alphaDen`, it can be weakened to the next
source denominator `3 * alphaDen`. -/
theorem scaledEdgeWellLinkedIn_weaken_two_add_to_three [Fintype V]
    {C T : Finset V} {alphaNum alphaDen : ℕ}
    (h : Section46.ScaledEdgeWellLinkedIn
      G C T alphaNum (2 * alphaDen + alphaNum))
    (halpha : alphaNum ≤ alphaDen) :
    Section46.ScaledEdgeWellLinkedIn
      G C T alphaNum (3 * alphaDen) := by
  apply scaledEdgeWellLinkedIn_weaken_denominator h
  omega

/-! ## The source's minimum initial set -/

/-- The two properties required of the initial set `S0` in Chuzhoy's proof of
Lemma 7.5.  The ratio-cleared inequality records the source threshold
`rho / 4` without an incorrect natural-number floor. -/
structure InitialSetConditions [Fintype V]
    (G : _root_.SimpleGraph V) (T : Finset V) (rho : ℕ)
    (S : Finset V) : Prop where
  augmentedBoundary_large :
    rho ≤ 4 *
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card
  augmentedBoundary_wellLinked :
    Section46.ScaledEdgeWellLinkedIn G S
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T) 1 9

/-- A candidate initial set of minimum cardinality.  Minimum cardinality is a
slightly stronger, finite choice than the inclusion-minimal choice used in the
paper and supplies exactly the same proper-subset contradiction. -/
structure IsMinimumInitialSet [Fintype V]
    (G : _root_.SimpleGraph V) (T : Finset V) (rho : ℕ)
    (S : Finset V) : Prop extends InitialSetConditions G T rho S where
  card_minimal :
    ∀ ⦃S' : Finset V⦄,
      InitialSetConditions G T rho S' → S.card ≤ S'.card

/-- A minimum initial set exists from any explicit candidate. -/
theorem exists_minimumInitialSet [Fintype V]
    {T U : Finset V} {rho : ℕ}
    (hU : InitialSetConditions G T rho U) :
    ∃ S : Finset V, IsMinimumInitialSet G T rho S := by
  classical
  let HasCard : ℕ → Prop := fun n =>
    ∃ S : Finset V, InitialSetConditions G T rho S ∧ S.card = n
  have hExists : ∃ n : ℕ, HasCard n :=
    ⟨U.card, U, hU, rfl⟩
  rcases Nat.find_spec hExists with ⟨S, hS, hScard⟩
  refine ⟨S, hS, ?_⟩
  intro S' hS'
  have hS'Card : HasCard S'.card := ⟨S', hS', rfl⟩
  have hmin : Nat.find hExists ≤ S'.card :=
    Nat.find_min' (H := hExists) hS'Card
  simpa [hScard] using hmin

/-- The minimum initial set has no proper subset satisfying the same source
conditions. -/
theorem IsMinimumInitialSet.not_conditions_of_ssubset [Fintype V]
    {T S S' : Finset V} {rho : ℕ}
    (hS : IsMinimumInitialSet G T rho S)
    (hproper : S' ⊂ S) :
    ¬ InitialSetConditions G T rho S' := by
  intro hS'
  have hle : S.card ≤ S'.card := hS.card_minimal hS'
  have hlt : S'.card < S.card := Finset.card_lt_card hproper
  omega

/-- The whole vertex set supplies the initial candidate whenever its terminal
set already has the required size and `1/9` cut well-linkedness. -/
theorem exists_minimumInitialSet_of_univ [Fintype V]
    {T : Finset V} {rho : ℕ}
    (hlarge : rho ≤ 4 * T.card)
    (hwell : Section46.ScaledEdgeWellLinkedIn
      G (Finset.univ : Finset V) T 1 9) :
    ∃ S : Finset V, IsMinimumInitialSet G T rho S := by
  apply exists_minimumInitialSet (G := G)
    (U := (Finset.univ : Finset V))
  constructor
  · simpa using hlarge
  · simpa using hwell

/-- Observation 7.1 at the whole vertex set supplies the `1/9` premise needed
to start Lemma 7.5. -/
theorem exists_minimumInitialSet_of_nodeLinked_union [Fintype V]
    {A B : Finset V} {rho : ℕ}
    (hlarge : rho ≤ 4 * (A ∪ B).card)
    (hA : NodeWellLinkedIn G (Finset.univ : Finset V) A)
    (hB : NodeWellLinkedIn G (Finset.univ : Finset V) B)
    (hAB : NodeLinkedIn G (Finset.univ : Finset V) A B) :
    ∃ S : Finset V, IsMinimumInitialSet G (A ∪ B) rho S := by
  apply exists_minimumInitialSet_of_univ (G := G) hlarge
  exact scaledEdgeWellLinkedIn_weaken_denominator
    (AppendixA3ClusterSplit.observation_7_1_union_scaledEdgeWellLinkedIn
      hA hB hAB) (by norm_num)

end AppendixA3Lemma75
end SimpleGraph

end Lax17Proofs
