import Lax17Proofs.Exposed
import Lax17Proofs.Source.Exponent8Polylog.NumericalEndpoint

namespace Lax17Proofs

universe u

namespace Final

/-- Registers a public theorem as an explicit proof dependency. -/
private theorem rebuildFrom {P Q : Prop} (_dependency : Q) (result : P) : P :=
  result

/--
---
conclusion: Lax17.PolynomialGridMinor.polynomial_grid_minor_eight_polylog
assumptions:
  - Lax17.CrossbarOrPseudoGrid.crossbarOrPseudoGrid
  - Lax17.CutMatchingTheorem.logarithmicCutMatchingExpansion
  - Lax17.ExpanderGrid.expanderContainsGrid
  - Lax17.HairyPathOfSetsFromTreewidth.hairyPathOfSetsFromTreewidth
  - Lax17.StrongPathOfSetsContainsGrid.strongPathOfSetsContainsGrid
---
There are positive integers $K$ and $b$ such that every finite simple graph
of treewidth at least
$$
K g^8 (\log_2 g)^b
$$
contains the $g \times g$ square grid as a minor.
-/
theorem polynomial_grid_minor_eight_polylog :
    ∃ K b : ℕ, 0 < K ∧ 0 < b ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) {g : ℕ},
          2 ≤ g →
            K * g ^ 8 * (Nat.log 2 g) ^ b ≤
                Lax17.Treewidth.treewidth G →
              Lax17.GridMinor.ContainsGridMinor G g := by
  apply rebuildFrom
    (@Lax17.CrossbarOrPseudoGrid.crossbarOrPseudoGrid.{u})
  apply rebuildFrom
    (@Lax17.CutMatchingTheorem.logarithmicCutMatchingExpansion.{u})
  apply rebuildFrom (@Lax17.ExpanderGrid.expanderContainsGrid.{u})
  apply rebuildFrom
    (@Lax17.HairyPathOfSetsFromTreewidth.hairyPathOfSetsFromTreewidth.{u})
  apply rebuildFrom
    (@Lax17.StrongPathOfSetsContainsGrid.strongPathOfSetsContainsGrid.{u})
  rcases
      _root_.Lax17Proofs.SimpleGraph.Exponent8Polylog.polynomial_grid_minor_theorem_exponentEightPolylog.{u} with
    ⟨K, b, hK, hb, hmain⟩
  refine ⟨K, b, hK, hb, ?_⟩
  intro V _ _ G g hg htw
  apply Bridge.containsGridMinorToPublic
  apply hmain G hg
  simpa [SimpleGraph.Exponent8Polylog.polynomialGridMinorTreewidthBound8,
    Bridge.treewidth_eq] using htw

end Final

end Lax17Proofs
