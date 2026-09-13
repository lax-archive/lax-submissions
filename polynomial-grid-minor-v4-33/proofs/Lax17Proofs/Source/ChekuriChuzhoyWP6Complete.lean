import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1CorridorConclusion
import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1HillBumpPreservation
import Lax17Proofs.Source.ChekuriChuzhoyWP6

namespace Lax17Proofs

universe u v w

/-!
# Completed Chekuri--Chuzhoy WP6

This module closes the semantic input used by the strong
path-of-sets-to-grid argument.

The proof of Chekuri--Chuzhoy Appendix B, Theorem B.1, is obtained by:

* the page-60 type-one/type-two split;
* the common bump/cross row descent;
* the cycle-erased hill descent, including preservation of active bump- and
  cross-freeness;
* the blocker/valley argument and terminal sparse-grid construction.

The resulting uniform theorem is then passed through the proved induced-
cluster localization and stitched-row construction to obtain the exact local
routing and Corollary 3.2 inputs, and finally the unconditional strong
path-of-sets grid-minor theorem used downstream.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


namespace AppendixB1

/-- Chekuri--Chuzhoy Appendix B, Theorem B.1.

If an `A`--`B` linkage is not good, then either the graph contains the
requested square grid minor or there is an `A`--`B` linkage whose auxiliary
graph has strictly fewer degree-two vertices. -/
theorem theoremB1_proved
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {A B : Finset V} (h : ℕ)
    (L : PerfectPathPacking G A B) :
    TheoremB1Statement G h L := by
  apply theoremB1Statement_of_rowNormal_grid
  intro fixedColumn S hnormal
  exact S.rowNormal_containsGridMinor hnormal

end AppendixB1

/-- The cluster-local routing alternative needed in the sharp form of
Chekuri--Chuzhoy Theorem 3.1. -/
theorem localRoutingClusterInput_proved :
    LocalRoutingClusterInput.{u} :=
  localRoutingClusterInput_of_theoremB1
    AppendixB1.theoremB1_proved

/-- The complete Corollary 3.2 input: local routing is supplied by Theorem
B.1 and the global alternating-row construction by the proved stitching
theorem. -/
theorem corollary32Input_proved :
    Corollary32Input.{u} :=
  corollary32Input_of_theoremB1
    AppendixB1.theoremB1_proved

/-- Unconditional WP6 endpoint in the exact quantitative form consumed by
the degree-ten proof. -/
theorem strongPathOfSets_containsGridMinor_proved
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {ell w g : ℕ}
    (hg : 2 ≤ g)
    (hell : 2 * g * (g - 1) ≤ ell)
    (hw : 16 * g ^ 2 + 10 * g ≤ w)
    (P : StrongPathOfSetsSystem G ell w) :
    ContainsGridMinor G g :=
  strongPathOfSets_containsGridMinor_of_theoremB1
    AppendixB1.theoremB1_proved
    G hg hell hw P

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
