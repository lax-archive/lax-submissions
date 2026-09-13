import Lax17Proofs.Source.Section45

namespace Lax17Proofs

/-!
# Rectangular Chuzhoy--Tan Theorem 4.15

`Section45.theorem415` uses one parameter for the requested chain length and
the consecutive-overlap threshold. The proof permits independent parameters.

The rectangular form gives a chain of length `L` whose consecutive row sets
overlap in at least `W` rows. The double-counting argument depends on `W`,
while the final weighted source-layer argument depends on `L`.

The hypothesis `0 < W` is necessary: with `N = D = M = W = 0` and `L = 1`,
the numerical inequalities hold, but `Fin M` has no one-element list.
-/

namespace SimpleGraph
namespace Exponent7

open Finset

/-- Rectangular form of Chuzhoy--Tan Theorem 4.15.

The selected list has length `L`; consecutive selected row sets overlap in at
least `W` rows.  All inequalities are division-free natural-number
inequalities. -/
theorem theorem415_rectangular
    {N M D W L : ℕ} (S : Fin M → Finset (Fin N))
    (hW : 0 < W)
    (hN : 3 * W ≤ N)
    (hDsq : 4 * N * W ≤ D ^ 2)
    (hlarge : 2 * N * L ≤ D * M)
    (hcard : ∀ i : Fin M, D ≤ (S i).card) :
    ∃ l : List (Fin M),
      l.length = L ∧
        l.IsChain (Section45.LargeOverlapRel S W) := by
  classical
  have hA : 0 < 2 * N := by omega
  have hind :
      ∀ I : Finset (Fin M),
        I ⊆ (Finset.univ : Finset (Fin M)) →
          Section45.RelIndependent (Section45.LargeOverlapRel S W) I →
            D * I.card < 2 * N := by
    intro I _ hI
    exact
      Section45.independent_bound_of_theorem415_hypotheses
        S hW hN hDsq hcard I hI
  rcases Section45.exists_relChainIn_of_weighted_independent_bound
      (rel := Section45.LargeOverlapRel S W)
      (s := (Finset.univ : Finset (Fin M)))
      (A := 2 * N) (D := D) (n := L)
      hA hind (by simpa using hlarge) with
    ⟨l, hlen, hchain, _⟩
  exact ⟨l, hlen, hchain⟩

end Exponent7
end SimpleGraph

end Lax17Proofs
