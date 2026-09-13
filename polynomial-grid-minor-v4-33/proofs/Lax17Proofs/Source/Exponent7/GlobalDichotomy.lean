import Lax17Proofs.Source.Exponent7.LocalDichotomy
import Lax17Proofs.Source.CutMatchingGame
import Lax17Proofs.Source.HairyPathOfSetsComplete

namespace Lax17Proofs

/-!
# Global exponent-seven dichotomy

In the non-crossbar branch, one odd hair cluster contains the target grid. In
the other branch, every odd hair cluster supplies a crossbar and the
cut-matching construction yields the grid.
-/

namespace SimpleGraph
namespace Exponent7

universe u

/-- Apply the conditional exponent-seven local dichotomy inside one hair
cluster. -/
theorem crossbar_or_grid_in_hairLocalGraph
    {reserve : ℕ}
    (hDichotomy : CleanMatchingDichotomyStatement.{u} reserve)
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {ell w q g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w) (i : Fin ell)
    (hq : 2 ≤ q)
    (hpow : CrossbarContract.IsPowerOfTwo q)
    (hg : 2 ≤ g)
    (hreserve : 0 < reserve)
    (hscaledWidth : 20000 * (reserve * g ^ 2) ≤ q ^ 2)
    (hlarge : exponentSevenLocalThreshold q (2 * g) ≤ w) :
    Nonempty (Crossbar (Hsys.hairLocalGraph i)
        (Hsys.base.left i) (Hsys.base.right i)
        (Hsys.y i) (q ^ 2)) ∨
      ContainsGridMinor (Hsys.hairLocalGraph i) g := by
  rcases Hsys.exists_left_right_linkage_inHairLocalGraph_with_staysIn i with
    ⟨Pab, hPabCard, _hPabStays⟩
  rcases Hsys.exists_left_y_perfect_linkage_inHairLocalGraph i with
    ⟨Pax, hPaxCard⟩
  have hleftCard : (Hsys.base.left i).card = w :=
    Hsys.base.left_card i
  have hrightCard : (Hsys.base.right i).card = w :=
    Hsys.base.right_card i
  have hyCard : (Hsys.y i).card = w := Hsys.y_card i
  have hleftY : Disjoint (Hsys.base.left i) (Hsys.y i) := by
    rw [Finset.disjoint_left]
    intro v hvLeft hvY
    exact Finset.disjoint_left.mp
      (Hsys.hairCluster_disjoint_base i i)
      (Hsys.y_subset_hairCluster i hvY)
      (Hsys.base.left_subset_cluster i hvLeft)
  have hrightY : Disjoint (Hsys.base.right i) (Hsys.y i) := by
    rw [Finset.disjoint_left]
    intro v hvRight hvY
    exact Finset.disjoint_left.mp
      (Hsys.hairCluster_disjoint_base i i)
      (Hsys.y_subset_hairCluster i hvY)
      (Hsys.base.right_subset_cluster i hvRight)
  exact localCrossbar_or_grid
    (Hsys.hairLocalGraph i) hDichotomy
    hq hpow hg hreserve hscaledWidth
    hleftCard hrightCard hyCard
    (Hsys.base.left_right_disjoint i)
    hleftY hrightY hlarge
    (fun x hx =>
      Hsys.hairLocalGraph_degreeEquals_one_of_mem_y i hx)
    Pab hPabCard Pax.toPathPacking (by simpa using hPaxCard)

/-- Transport the grid alternative from one hair-local graph to the ambient
hairy-system graph. -/
theorem crossbar_or_grid_in_hairyCluster
    {reserve : ℕ}
    (hDichotomy : CleanMatchingDichotomyStatement.{u} reserve)
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {ell w q g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w) (i : Fin ell)
    (hq : 2 ≤ q)
    (hpow : CrossbarContract.IsPowerOfTwo q)
    (hg : 2 ≤ g)
    (hreserve : 0 < reserve)
    (hscaledWidth : 20000 * (reserve * g ^ 2) ≤ q ^ 2)
    (hlarge : exponentSevenLocalThreshold q (2 * g) ≤ w) :
    Nonempty (Crossbar (Hsys.hairLocalGraph i)
        (Hsys.base.left i) (Hsys.base.right i)
        (Hsys.y i) (q ^ 2)) ∨
      ContainsGridMinor G g := by
  rcases crossbar_or_grid_in_hairLocalGraph
      hDichotomy Hsys i hq hpow hg hreserve
        hscaledWidth hlarge with hcrossbar | hgrid
  · exact Or.inl hcrossbar
  · exact Or.inr (hgrid.mono (Hsys.hairLocalGraph_le i))

/-- Either all odd one-based clusters have their local `q^2` crossbar, or one
of them already contains the target grid. -/
theorem local_crossbars_at_odd_clusters_or_grid
    {reserve : ℕ}
    (hDichotomy : CleanMatchingDichotomyStatement.{u} reserve)
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {ell w q g : ℕ}
    (Hsys : HairyPathOfSetsSystem G ell w)
    (hq : 2 ≤ q)
    (hpow : CrossbarContract.IsPowerOfTwo q)
    (hg : 2 ≤ g)
    (hreserve : 0 < reserve)
    (hscaledWidth : 20000 * (reserve * g ^ 2) ≤ q ^ 2)
    (hlarge : exponentSevenLocalThreshold q (2 * g) ≤ w) :
    (∀ i : Fin ell,
        HairyCrossbarGrid.OneBasedOdd i →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (q ^ 2))) ∨
      ContainsGridMinor G g := by
  by_cases hgrid :
      ∃ i : Fin ell,
        HairyCrossbarGrid.OneBasedOdd i ∧
          ContainsGridMinor G g
  · rcases hgrid with ⟨_i, _hi, hminor⟩
    exact Or.inr hminor
  · refine Or.inl ?_
    intro i hi
    rcases crossbar_or_grid_in_hairyCluster
        hDichotomy Hsys i hq hpow hg hreserve
          hscaledWidth hlarge with hcrossbar | hminor
    · exact hcrossbar
    · exact False.elim (hgrid ⟨i, hi, hminor⟩)

/-- The complete conditional exponent-seven theorem on a hairy
Path-of-Sets System.  The first branch is the local short-wide grid; the
second is the existing crossbar/cut-matching-game construction. -/
theorem gridMinor_of_hairyPathOfSets
    {reserve : ℕ}
    (hDichotomy : CleanMatchingDichotomyStatement.{u} reserve) :
    ∃ cGrid : ℕ, 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V)
        {ell w q g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          2 ≤ q →
            CrossbarContract.IsPowerOfTwo q →
              2 ≤ g →
                0 < reserve →
                  MaxDegreeAtMost G 3 →
                    cGrid * Nat.log 2 q ≤ ell →
                      q ^ 2 ≤ w →
                        exponentSevenLocalThreshold q (2 * g) ≤ w →
                          20000 * (reserve * g ^ 2) ≤ q ^ 2 →
                            cGrid * g * (Nat.log 2 q) ^ 2 ≤ q →
                              ContainsGridMinor G g := by
  rcases
      HairyCrossbarGrid.exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_cutMatchingGame
      with
    ⟨cGrid, hcGrid, hcrossbarGrid⟩
  refine ⟨cGrid, hcGrid, ?_⟩
  intro V _ _ G ell w q g Hsys hq hpow hg hreserve hdegree
    hlength hqWidth hlocalWidth hscaledWidth htarget
  rcases local_crossbars_at_odd_clusters_or_grid
      hDichotomy Hsys hq hpow hg hreserve
        hscaledWidth hlocalWidth with hcrossbars | hgrid
  · rcases hcrossbarGrid G Hsys hq hpow hdegree
        hlength hqWidth hcrossbars with
      ⟨g', hproduced, hminor⟩
    exact hminor.of_order_le
      (PolynomialGridMinor.le_gridOrder_of_direct_branch_bound
        hcGrid hq htarget hproduced)
  · exact hgrid

/-- Parameterized treewidth theorem.  All semantic inputs except the named
clean matching dichotomy are supplied by proved Lean declarations; the
remaining hypotheses are explicit natural-number inequalities. -/
theorem containsGridMinor_of_treewidth_parameters
    {reserve : ℕ}
    (hDichotomy : CleanMatchingDichotomyStatement.{u} reserve) :
    ∃ cHair cHairLog cGrid : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cGrid ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V)
          {ell w k q g : ℕ},
            1 < ell →
              1 < w →
                1 < k →
                  k ≤ treewidth G →
                    cHair * w * ell ^ 50 *
                        (Nat.log 2 k) ^ cHairLog < k →
                      2 ≤ q →
                        CrossbarContract.IsPowerOfTwo q →
                          2 ≤ g →
                            0 < reserve →
                              cGrid * Nat.log 2 q ≤ ell →
                                q ^ 2 ≤ w →
                                  exponentSevenLocalThreshold q (2 * g) ≤ w →
                                    20000 * (reserve * g ^ 2) ≤ q ^ 2 →
                                      cGrid * g * (Nat.log 2 q) ^ 2 ≤ q →
                                        ContainsGridMinor G g := by
  rcases PolynomialGridMinor.exists_hairyPathOfSetsInput_proved with
    ⟨cHair, cHairLog, hcHair, hcHairLog, hhairy⟩
  rcases gridMinor_of_hairyPathOfSets hDichotomy with
    ⟨cGrid, hcGrid, hmain⟩
  refine ⟨cHair, cHairLog, cGrid,
    hcHair, hcHairLog, hcGrid, ?_⟩
  intro V _ _ G ell w k q g hell hw hk htw hhairyLarge
    hq hpow hg hreserve hlength hqWidth hlocalWidth
    hscaledWidth htarget
  rcases hhairy G hell hw hk htw hhairyLarge with
    ⟨H, hHG, hdegree, ⟨Hsys⟩⟩
  exact
    (hmain H Hsys hq hpow hg hreserve hdegree
      hlength hqWidth hlocalWidth hscaledWidth htarget).mono hHG

end Exponent7
end SimpleGraph

end Lax17Proofs
