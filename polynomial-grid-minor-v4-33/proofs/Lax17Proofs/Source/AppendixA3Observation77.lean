import Mathlib.Tactic
import Lax17Proofs.Source.AppendixA3Lemma75Start
import Lax17Proofs.Source.AppendixA3Observation77Extraction

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy Observation 7.7

This file completes the corrected proof of Observation 7.7 used in Lemma 7.5.
The source's informal last-half argument is replaced by the first crossing of
three quarters of the *original* augmented boundary.  The strict containment
in the minimum initial set also handles the zero-step pruning case.
-/

namespace SimpleGraph
namespace AppendixA3Lemma75


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

noncomputable section

/-- Corrected Observation 7.7.

For a proper subset of the minimum initial set, every minimum quarter-balanced
cut of an augmented boundary larger than `rho` has at most one eighth as many
crossing edges as augmented-boundary vertices.

The proof runs the `1/9` pruning process.  If its terminal state retains more
than three quarters of the original augmented boundary, that state is a
smaller initial-set candidate.  Otherwise the recorded first three-quarter
crossing is itself a quarter-balanced cut of size at most one eighth, and
minimum-cut optimality gives the conclusion. -/
theorem minimumQuarterBalancedCut_eight_mul_cut_le
    {T S0 S A : Finset V} {rho : ℕ}
    (hS0 : IsMinimumInitialSet G T rho S0)
    (hproper : S ⊂ S0)
    (hrho :
      rho <
        (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card)
    (hA : AppendixA3BalancedCut.IsMinimumQuarterBalancedEdgeCut G S
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T) A) :
    8 * (Section44.edgeBoundary G A (S \ A)).card ≤
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card := by
  classical
  let Omega :=
    AppendixA3ClusterSplit.augmentedBoundaryVertices G S T
  obtain ⟨state, hreachable, hwell⟩ :=
    exists_wellLinked_pruningState G S T
  by_cases hterminal :
      4 * (state.U ∩ Omega).card ≤ 3 * Omega.card
  · have hOmegaPos : 3 * Omega.card < 4 * Omega.card := by
      have : 0 < Omega.card := by
        simpa [Omega] using lt_of_le_of_lt (Nat.zero_le rho) hrho
      omega
    obtain ⟨successor, previous, B, C, _hsuccessor, _hprevious,
        hbefore, hguards⟩ :=
      exists_guarded_original_three_quarter_crossing
        (G := G) (S := S) (T := T) hreachable hOmegaPos (by
          simpa [Omega] using hterminal)
    rcases hguards with
      ⟨hcover, hdisj, horient, hsparse, hsuccessorEq, hafter⟩
    have hafter' :
        4 * (B ∩
          AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card ≤
            3 *
              (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card := by
      simpa [hsuccessorEq, PruningState.retainLeft] using hafter
    have hcrossing :=
      retainLeft_at_three_quarter_original_crossing
        (G := G) previous hcover hdisj horient hsparse hbefore hafter'
    have hbalanced :
        AppendixA3BalancedCut.QuarterBalanced S Omega B := by
      have hfirst := hcrossing.1
      simpa [hsuccessorEq, PruningState.retainLeft, Omega] using hfirst
    have hsmall :
        8 * (Section44.edgeBoundary G B (S \ B)).card ≤ Omega.card := by
      simpa [Omega] using hcrossing.2
    have hminimal :
        (Section44.edgeBoundary G A (S \ A)).card ≤
          (Section44.edgeBoundary G B (S \ B)).card :=
      hA.cut_card_minimal hbalanced
    omega
  · have hmass :
        3 * Omega.card < 4 * (state.U ∩ Omega).card := by
      omega
    have hretained :
        state.U ∩ Omega ⊆
          AppendixA3ClusterSplit.augmentedBoundaryVertices G state.U T := by
      simpa [Omega] using
        (AppendixA3AugmentedBoundary.retained_augmentedBoundaryVertices_subset
            (G := G) (T := T) state.U_subset)
    have hlarge :
        rho ≤ 4 *
          (AppendixA3ClusterSplit.augmentedBoundaryVertices
            G state.U T).card := by
      have hcard :
          (state.U ∩ Omega).card ≤
            (AppendixA3ClusterSplit.augmentedBoundaryVertices
              G state.U T).card :=
        Finset.card_le_card hretained
      have hrhoOmega : rho ≤ Omega.card := Nat.le_of_lt hrho
      omega
    have hstateProper : state.U ⊂ S0 := by
      have hsubset : state.U ⊆ S0 :=
        state.U_subset.trans hproper.subset
      have hcard :
          state.U.card < S0.card :=
        lt_of_le_of_lt
          (Finset.card_le_card state.U_subset)
          (Finset.card_lt_card hproper)
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨hsubset, ?_⟩
      intro heq
      have := congrArg Finset.card heq
      omega
    exact False.elim <|
      (hS0.not_conditions_of_ssubset hstateProper)
        ⟨hlarge, hwell⟩

end
end AppendixA3Lemma75
end SimpleGraph

end Lax17Proofs
