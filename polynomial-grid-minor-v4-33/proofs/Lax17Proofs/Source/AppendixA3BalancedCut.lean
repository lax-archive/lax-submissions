import Lax17Proofs.Source.AppendixA3AugmentedBoundary

namespace Lax17Proofs

universe u v w

/-!
# Minimum quarter-balanced edge cuts for Chuzhoy Section 7

This module records the minimum-cut setup used by Chuzhoy's Observation 7.6.
The bandwidth conclusion itself is Chuzhoy Lemma 2.11 (Lemma 2.14 in the
journal version) and is not proved here.

A cut of `S` is represented by one retained side `A`; its other side is
`S \ A`.  Quarter-balance is written with ratio-cleared natural-number
inequalities.  Minimum-cut existence requires an explicit balanced candidate,
since such a candidate need not exist for a singleton terminal set.
-/

namespace SimpleGraph
namespace AppendixA3BalancedCut


variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- A one-sided representation of a `1/4`-balanced partition of `S` with
respect to `Gamma`. -/
structure QuarterBalanced (S Gamma A : Finset V) : Prop where
  subset : A ⊆ S
  retained_quarter : Gamma.card ≤ 4 * (A ∩ Gamma).card
  complement_quarter : Gamma.card ≤ 4 * ((S \ A) ∩ Gamma).card

/-- Reversing the orientation of a quarter-balanced cut preserves
quarter-balance. -/
theorem QuarterBalanced.sdiff {S Gamma A : Finset V}
    (hA : QuarterBalanced S Gamma A) :
    QuarterBalanced S Gamma (S \ A) := by
  refine ⟨Finset.sdiff_subset, hA.complement_quarter, ?_⟩
  simpa [Finset.sdiff_sdiff_eq_self hA.subset] using hA.retained_quarter

/-- Reversing a cut represented inside `S` gives the same undirected edge
boundary. -/
theorem edgeBoundary_sdiff [Fintype V] {S A : Finset V} (hAS : A ⊆ S) :
    Section44.edgeBoundary G (S \ A) (S \ (S \ A)) =
      Section44.edgeBoundary G A (S \ A) := by
  rw [Finset.sdiff_sdiff_eq_self hAS,
    Section44.edgeBoundary_comm (G := G)]

/-- A quarter-balanced side whose crossing-edge count is minimum among all
quarter-balanced sides of the same `(S, Gamma)`. -/
structure IsMinimumQuarterBalancedEdgeCut [Fintype V]
    (G : _root_.SimpleGraph V) (S Gamma A : Finset V) : Prop
    extends QuarterBalanced S Gamma A where
  cut_card_minimal :
    ∀ ⦃B : Finset V⦄, QuarterBalanced S Gamma B →
      (Section44.edgeBoundary G A (S \ A)).card ≤
        (Section44.edgeBoundary G B (S \ B)).card

/-- A minimum quarter-balanced edge cut exists from any explicit
quarter-balanced candidate. -/
theorem exists_minimumQuarterBalancedEdgeCut [Fintype V]
    {S Gamma U : Finset V} (hU : QuarterBalanced S Gamma U) :
    ∃ A : Finset V, IsMinimumQuarterBalancedEdgeCut G S Gamma A := by
  classical
  let HasCutCard : ℕ → Prop := fun n =>
    ∃ A : Finset V, QuarterBalanced S Gamma A ∧
      (Section44.edgeBoundary G A (S \ A)).card = n
  have hExists : ∃ n : ℕ, HasCutCard n :=
    ⟨(Section44.edgeBoundary G U (S \ U)).card, U, hU, rfl⟩
  rcases Nat.find_spec hExists with ⟨A, hA, hAcard⟩
  refine ⟨A, hA, ?_⟩
  intro B hB
  have hBCard : HasCutCard
      (Section44.edgeBoundary G B (S \ B)).card :=
    ⟨B, hB, rfl⟩
  have hmin : Nat.find hExists ≤
      (Section44.edgeBoundary G B (S \ B)).card :=
    Nat.find_min' (H := hExists) hBCard
  simpa [hAcard] using hmin

/-- The opposite orientation of a minimum quarter-balanced edge cut is also
minimum. -/
theorem IsMinimumQuarterBalancedEdgeCut.sdiff [Fintype V]
    {S Gamma A : Finset V}
    (hA : IsMinimumQuarterBalancedEdgeCut G S Gamma A) :
    IsMinimumQuarterBalancedEdgeCut G S Gamma (S \ A) := by
  refine ⟨hA.toQuarterBalanced.sdiff, ?_⟩
  intro B hB
  rw [edgeBoundary_sdiff (G := G) hA.subset]
  exact hA.cut_card_minimal hB

/-- Orient a minimum cut so the retained side contains at least as many
`Gamma` terminals as its complement. -/
theorem IsMinimumQuarterBalancedEdgeCut.exists_oriented [Fintype V]
    {S Gamma A : Finset V}
    (hA : IsMinimumQuarterBalancedEdgeCut G S Gamma A) :
    ∃ A' : Finset V,
      IsMinimumQuarterBalancedEdgeCut G S Gamma A' ∧
        ((S \ A') ∩ Gamma).card ≤ (A' ∩ Gamma).card := by
  by_cases hle : ((S \ A) ∩ Gamma).card ≤ (A ∩ Gamma).card
  · exact ⟨A, hA, hle⟩
  · refine ⟨S \ A, hA.sdiff, ?_⟩
    rw [Finset.sdiff_sdiff_eq_self hA.subset]
    exact Nat.le_of_not_ge hle

end AppendixA3BalancedCut
end SimpleGraph

end Lax17Proofs
