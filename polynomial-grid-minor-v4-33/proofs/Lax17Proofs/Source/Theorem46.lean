import Lax17Proofs.Source.UniqueLinkageOrdering

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy--Tan Theorem 4.6

This file packages the generic Section 4.2 slicing theorem.  The counting and
threshold construction is proved in `PseudoGridSlicing`; Lemma 4.5 is proved in
`UniqueLinkageOrdering`.  Combining them gives the paper's Theorem 4.6.
-/

namespace SimpleGraph


namespace PathSlicing

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B S T : Finset V}

/-- Chuzhoy--Tan Theorem 4.6: a unique linkage intersected by a sufficiently
large disjoint auxiliary path family admits an `M`-slicing of width at least
`w`. -/
theorem theorem46
    (R : PerfectPathPacking G A B) (Qpack : PathPacking G S T)
    (M w : ℕ)
    (hM : 0 < M) (_hw : 0 < w)
    (hunique : R.IsUniqueLinkage)
    (hintersects : PathPackingIntersectsLinkage R Qpack)
    (hcard : M * w + (M + 1) * R.card ≤ Qpack.card) :
    ∃ sigma : PathSlicing R M, sigma.WidthAtLeast Qpack w := by
  exact exists_slicing_of_linkageOrdering
    (linkageOrderingOfUnique hunique) Qpack M w hM hintersects hcard

/-- Proposition-wrapper form of Chuzhoy--Tan Theorem 4.6. -/
theorem theorem46_statement : Theorem46Statement := by
  intro V _ _ G A B S T R Qpack M w hM hw hunique hintersects hcard
  exact theorem46 R Qpack M w hM hw hunique hintersects hcard

end PathSlicing

namespace PseudoGrid

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B X : Finset V} {g D M w : ℕ}
variable {P : PerfectPathPacking G A B} {Q : PerfectPathPacking G A X}

/-- The full Section 4.2 pseudo-grid branch.  Observation 4.4 supplies a minor
with a perfect unique linkage intersected by the retained auxiliary family;
Theorem 4.6 then gives the required slicing. -/
theorem section42_slicing_minor_of_pseudoGrid
    (Gamma : PseudoGrid G A B X g D P Q)
    (hminimal : P.IsMinimumTheorem41Pair Q)
    (hM : 0 < M) (hw : 0 < w)
    (hcard :
      M * w + (M + 1) * Gamma.rowPacking.card ≤ Gamma.goodQSet.card) :
    ∃ (W : Type u), ∃ (_ : Fintype W), ∃ (_ : DecidableEq W),
      ∃ (H : _root_.SimpleGraph W),
      ∃ (A' B' S T : Finset W),
        ∃ (R : PerfectPathPacking H A' B') (Qpack : PathPacking H S T),
          ∃ sigma : PathSlicing R M,
            IsMinor H G ∧
              R.IsUniqueLinkage ∧
                R.card = Gamma.rowPacking.card ∧
                  sigma.WidthAtLeast Qpack w := by
  classical
  rcases Gamma.observation_four_four_unique_linkage_reduction hminimal with
    ⟨W, hWfin, hWdec, H, A', B', S', T', R, Qpack,
      hminor, hunique, hRcard, hQcard, hintersects⟩
  letI : Fintype W := hWfin
  letI : DecidableEq W := hWdec
  have hcard' : M * w + (M + 1) * R.card ≤ Qpack.card := by
    calc
      M * w + (M + 1) * R.card
          = M * w + (M + 1) * Gamma.rowPacking.card := by rw [hRcard]
      _ ≤ Gamma.goodQSet.card := hcard
      _ ≤ Qpack.card := hQcard
  rcases PathSlicing.theorem46 R Qpack M w hM hw hunique hintersects hcard' with
    ⟨sigma, hwidth⟩
  exact ⟨W, hWfin, hWdec, H, A', B', S', T', R, Qpack, sigma,
    hminor, hunique, hRcard, hwidth⟩

end PseudoGrid

end SimpleGraph

end Lax17Proofs
