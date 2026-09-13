import Lax17Proofs.Source.ChekuriChuzhoyTheoremA2Inputs
import Lax17Proofs.Source.TreewidthSparsifierContract

namespace Lax17Proofs

universe u v w

/-!
# Degree-three treewidth sparsifier: Theorem 3.4

This module supplies the only form of Theorem 3.4 from
`treewidth-sparsifier.pdf` used in the proof of Theorem 1.1.  The cited result
is Chekuri--Chuzhoy's strong path-of-sets theorem (preprint Theorem 3.4,
journal Theorem 3.5).

The source proof of the degree-three sparsifier uses node-well-linkedness only
for disjoint partitions of a nail set and linkedness only between the two
disjoint nail sets.  Consequently the repository's
`StrongPathOfSetsSystem` is the exact proof-facing object; the stronger
`PaperStrongPathOfSetsSystem`, which additionally quantifies over overlapping
terminal subsets, is not needed.
-/

namespace SimpleGraph
namespace TreewidthSparsifier


/-- Theorem 3.4 in the local strong path-of-sets formulation.

The polynomial exponent is the accepted exponent-50 WP1 endpoint.  This
differs from the source's exponent 48 only by the explicitly documented
exponent-24 strong-tree construction and is sufficient for the degree-ten
grid-minor route.
-/
theorem theorem34_localStrongPathOfSets_from_treewidth :
    ∃ cPath cPathLog : ℕ, 0 < cPath ∧ 0 < cPathLog ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {height width k : ℕ},
          1 < k →
            1 < height →
              1 < width →
                k ≤ treewidth G →
                  cPath * height * width ^ 50 *
                      (Nat.log 2 k) ^ cPathLog < k →
                    Nonempty (StrongPathOfSetsSystem G width height) := by
  rcases
      ChekuriChuzhoy.exists_strongPathOfSets_of_treewidth_from_theoremA2SourceInputs
        ChekuriChuzhoy.theoremA2SourceInputs_proved with
    ⟨cPath, cPathLog, hcPath, hcPathLog, hpath⟩
  refine ⟨cPath, cPathLog, hcPath, hcPathLog, ?_⟩
  intro V _ _ G height width k hk hheight hwidth htw hlarge
  exact hpath G hwidth hheight hk htw hlarge

end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
