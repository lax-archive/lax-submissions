import Lax17Proofs.Source.Exponent8.LocalDichotomy
import Lax17Proofs.Source.CutMatchingGame
import Lax17Proofs.Source.HairyPathOfSetsComplete
import Lax17Proofs.Source.ChekuriChuzhoyWP6Complete

namespace Lax17Proofs

/-!
# Global consumers of the exponent-eight-and-a-half local dichotomy

This module keeps the experimental Section 5 improvement separate from the
public polynomial-grid-minor endpoint.  It transports the proved local
threshold

`2^29 * g^8 * sqrt(g) * (log₂ g + 1)`

through the existing hairy Path-of-Sets System and then discharges both
outcomes using the proved cut-matching-game and Chekuri--Chuzhoy consumers.
-/

namespace SimpleGraph
namespace Exponent8

universe u

/-- Apply an exponent-eight-and-a-half crossbar dichotomy to one hair-local
graph. -/
theorem crossbar_or_strong_pathOfSets_minor_in_hairLocalGraph85_of_input
    (hinput :
      ∃ c : ℕ, 0 < c ∧
        CrossbarDichotomyInput85.{u} c e8Constant 1) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w) (i : Fin ell),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              exponentEightLocalThreshold e8Constant 1 g ≤ w →
                Nonempty (Crossbar (Hsys.hairLocalGraph i)
                  (Hsys.base.left i) (Hsys.base.right i)
                  (Hsys.y i) (g ^ 2)) ∨
                  ∃ ell' w' : ℕ,
                    g ^ 2 ≤ c * ell' ∧
                      g ^ 2 ≤ c * w' ∧
                        CrossbarContract.HasStrongPathOfSetsMinor
                          (Hsys.hairLocalGraph i) ell' w' := by
  rcases hinput with ⟨c, hc, hcrossbar⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell w g Hsys i hg hpow hlarge
  rcases Hsys.exists_left_right_linkage_inHairLocalGraph_with_staysIn i with
    ⟨Pab, hPab_card, _hPab_stays⟩
  rcases Hsys.exists_left_y_perfect_linkage_inHairLocalGraph i with
    ⟨Pax, hPax_card⟩
  have hleft_card : (Hsys.base.left i).card = w := Hsys.base.left_card i
  have hright_card : (Hsys.base.right i).card = w :=
    Hsys.base.right_card i
  have hy_card : (Hsys.y i).card = w := Hsys.y_card i
  have hleft_y_disjoint : Disjoint (Hsys.base.left i) (Hsys.y i) := by
    rw [Finset.disjoint_left]
    intro v hvleft hvy
    exact Finset.disjoint_left.mp (Hsys.hairCluster_disjoint_base i i)
      (Hsys.y_subset_hairCluster i hvy)
      (Hsys.base.left_subset_cluster i hvleft)
  have hright_y_disjoint : Disjoint (Hsys.base.right i) (Hsys.y i) := by
    rw [Finset.disjoint_left]
    intro v hvright hvy
    exact Finset.disjoint_left.mp (Hsys.hairCluster_disjoint_base i i)
      (Hsys.y_subset_hairCluster i hvy)
      (Hsys.base.right_subset_cluster i hvright)
  exact hcrossbar (Hsys.hairLocalGraph i) hg hpow hleft_card hright_card
    hy_card (Hsys.base.left_right_disjoint i) hleft_y_disjoint
    hright_y_disjoint hlarge
    (fun x hx => Hsys.hairLocalGraph_degreeEquals_one_of_mem_y i hx)
    Pab hPab_card Pax.toPathPacking (by simpa using hPax_card)

/-- The proved local Section 5 theorem in one hair-local graph. -/
theorem crossbar_or_strong_pathOfSets_minor_in_hairLocalGraph85 :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w) (i : Fin ell),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              exponentEightLocalThreshold e8Constant 1 g ≤ w →
                Nonempty (Crossbar (Hsys.hairLocalGraph i)
                  (Hsys.base.left i) (Hsys.base.right i)
                  (Hsys.y i) (g ^ 2)) ∨
                  ∃ ell' w' : ℕ,
                    g ^ 2 ≤ c * ell' ∧
                      g ^ 2 ≤ c * w' ∧
                        CrossbarContract.HasStrongPathOfSetsMinor
                          (Hsys.hairLocalGraph i) ell' w' :=
  crossbar_or_strong_pathOfSets_minor_in_hairLocalGraph85_of_input
    exists_crossbarDichotomyInput85_proved

/-- Transport the strong-minor outcome from a hair-local graph to the ambient
hairy-system graph. -/
theorem crossbar_or_strong_pathOfSets_minor_in_hairyCluster85 :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w) (i : Fin ell),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              exponentEightLocalThreshold e8Constant 1 g ≤ w →
                Nonempty (Crossbar (Hsys.hairLocalGraph i)
                  (Hsys.base.left i) (Hsys.base.right i)
                  (Hsys.y i) (g ^ 2)) ∨
                  ∃ ell' w' : ℕ,
                    g ^ 2 ≤ c * ell' ∧
                      g ^ 2 ≤ c * w' ∧
                        CrossbarContract.HasStrongPathOfSetsMinor
                          G ell' w' := by
  rcases crossbar_or_strong_pathOfSets_minor_in_hairLocalGraph85 with
    ⟨c, hc, hlocal⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell w g Hsys i hg hpow hlarge
  rcases hlocal Hsys i hg hpow hlarge with hcrossbar | hstrong
  · exact Or.inl hcrossbar
  · rcases hstrong with ⟨ell', w', hell, hw, hminor⟩
    exact Or.inr ⟨ell', w', hell, hw,
      hminor.mono (Hsys.hairLocalGraph_le i)⟩

/-- Either every odd one-based cluster carries the required local crossbar, or
one cluster already supplies an ambient strong Path-of-Sets minor. -/
theorem local_crossbars_at_odd_clusters_or_strong_pathOfSets_minor85 :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              exponentEightLocalThreshold e8Constant 1 g ≤ w →
                (∀ i : Fin ell,
                  HairyCrossbarGrid.OneBasedOdd i →
                  Nonempty (Crossbar (Hsys.hairLocalGraph i)
                    (Hsys.base.left i) (Hsys.base.right i)
                    (Hsys.y i) (g ^ 2))) ∨
                  ∃ ell' w' : ℕ,
                    g ^ 2 ≤ c * ell' ∧
                      g ^ 2 ≤ c * w' ∧
                        CrossbarContract.HasStrongPathOfSetsMinor
                          G ell' w' := by
  rcases crossbar_or_strong_pathOfSets_minor_in_hairyCluster85 with
    ⟨c, hc, hcluster⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell w g Hsys hg hpow hlarge
  by_cases hstrong :
      ∃ i : Fin ell,
        HairyCrossbarGrid.OneBasedOdd i ∧
        ∃ ell' w' : ℕ,
          g ^ 2 ≤ c * ell' ∧
            g ^ 2 ≤ c * w' ∧
              CrossbarContract.HasStrongPathOfSetsMinor G ell' w'
  · rcases hstrong with ⟨_i, _hi, ell', w', hell, hw, hminor⟩
    exact Or.inr ⟨ell', w', hell, hw, hminor⟩
  · refine Or.inl ?_
    intro i hi
    rcases hcluster Hsys i hg hpow hlarge with hcrossbar | hminor
    · exact hcrossbar
    · exact False.elim (hstrong ⟨i, hi, hminor⟩)

/-- The exponent-eight-and-a-half hairy-system dichotomy, with the direct
branch discharged by the proved cut-matching-game assembly. -/
theorem gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets85 :
    ∃ cCross cGrid : ℕ, 0 < cCross ∧ 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              MaxDegreeAtMost G 3 →
                cGrid * Nat.log 2 g ≤ ell →
                  g ^ 2 ≤ w →
                    exponentEightLocalThreshold e8Constant 1 g ≤ w →
                      (∃ g' : ℕ,
                        g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                          ContainsGridMinor G g') ∨
                        ∃ ell' w' : ℕ,
                          g ^ 2 ≤ cCross * ell' ∧
                            g ^ 2 ≤ cCross * w' ∧
                              CrossbarContract.HasStrongPathOfSetsMinor
                                G ell' w' := by
  rcases local_crossbars_at_odd_clusters_or_strong_pathOfSets_minor85 with
    ⟨cCross, hcCross, hodd⟩
  rcases
      HairyCrossbarGrid.exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_cutMatchingGame
      with
    ⟨cGrid, hcGrid, hgrid⟩
  refine ⟨cCross, cGrid, hcCross, hcGrid, ?_⟩
  intro V _ _ G ell w g Hsys hg hpow hmaxDegree hell hw hlarge
  rcases hodd Hsys hg hpow hlarge with hcrossbars | hstrong
  · exact Or.inl
      (hgrid G Hsys hg hpow hmaxDegree hell hw hcrossbars)
  · exact Or.inr hstrong

/-- Cancel the local dichotomy coefficient from a scaled square bound. -/
theorem square_le_of_scaled_square_le85 {c g r n : ℕ}
    (hc : 0 < c) (hscaled : c * r ^ 2 ≤ g ^ 2)
    (hn : g ^ 2 ≤ c * n) :
    r ^ 2 ≤ n :=
  Nat.le_of_mul_le_mul_left (le_trans hscaled hn) hc

/-- Both outcomes of the exponent-eight-and-a-half hairy-system dichotomy are
converted to grid minors.  The strong branch uses the proved
Chekuri--Chuzhoy Corollary 3.2 package. -/
theorem gridMinor_or_gridMinor_of_hairy_pathOfSets85 :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {ell w g r : ℕ}
          (Hsys : HairyPathOfSetsSystem G ell w),
            2 ≤ g →
              2 ≤ r →
                CrossbarContract.IsPowerOfTwo g →
                  MaxDegreeAtMost G 3 →
                    cGrid * Nat.log 2 g ≤ ell →
                      g ^ 2 ≤ w →
                        exponentEightLocalThreshold e8Constant 1 g ≤ w →
                          cCross * r ^ 2 ≤ g ^ 2 →
                            (∃ g' : ℕ,
                              g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                ContainsGridMinor G g') ∨
                              ∃ r' : ℕ,
                                r ≤ cStrong * r' ∧
                                  ContainsGridMinor G r' := by
  rcases gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets85 with
    ⟨cCross, cGrid, hcCross, hcGrid, hmain⟩
  rcases
      PolynomialGridMinor.strongMinorGridInput_of_corollary32Input
        ChekuriChuzhoy.corollary32Input_proved with
    ⟨cStrong, hcStrong, hstrongGrid⟩
  refine ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G ell w g r Hsys hg hr hpow hmaxDegree hell hw hlarge
    hscaled
  rcases hmain G Hsys hg hpow hmaxDegree hell hw hlarge with
    hgrid | hstrong
  · exact Or.inl hgrid
  · rcases hstrong with ⟨ell', w', hell', hw', hminor⟩
    exact Or.inr
      (hstrongGrid hr
        (square_le_of_scaled_square_le85 hcCross hscaled hell')
        (square_le_of_scaled_square_le85 hcCross hscaled hw')
        hminor)

/-- Parameterized graph theorem for the exponent-eight-and-a-half route.
Only explicit natural-number inequalities remain; all semantic paper inputs
are supplied by proved Lean theorems. -/
theorem containsGridMinor_of_treewidth_parameters85 :
    ∃ cHair cHairLog cCross cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cCross ∧
        0 < cGrid ∧ 0 < cStrong ∧
          ∀ {V : Type u} [Fintype V] [DecidableEq V]
            (G : _root_.SimpleGraph V) {ell w k g r target : ℕ},
              1 < ell →
                1 < w →
                  1 < k →
                    k ≤ treewidth G →
                      cHair * w * ell ^ 50 *
                          (Nat.log 2 k) ^ cHairLog < k →
                        2 ≤ g →
                          2 ≤ r →
                            CrossbarContract.IsPowerOfTwo g →
                              cGrid * Nat.log 2 g ≤ ell →
                                g ^ 2 ≤ w →
                                  exponentEightLocalThreshold
                                      e8Constant 1 g ≤ w →
                                    cCross * r ^ 2 ≤ g ^ 2 →
                                      cGrid * target *
                                          (Nat.log 2 g) ^ 2 ≤ g →
                                        cStrong * target ≤ r →
                                          ContainsGridMinor G target := by
  rcases PolynomialGridMinor.exists_hairyPathOfSetsInput_proved with
    ⟨cHair, cHairLog, hcHair, hcHairLog, hhairy⟩
  rcases gridMinor_or_gridMinor_of_hairy_pathOfSets85 with
    ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, hmain⟩
  refine ⟨cHair, cHairLog, cCross, cGrid, cStrong,
    hcHair, hcHairLog, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G ell w k g r target hell hw hk htw hhairyLarge hg hr hpow
    hellGrid hwGrid hlarge hscaled htargetDirect htargetStrong
  rcases hhairy G hell hw hk htw hhairyLarge with
    ⟨H, hHG, hmaxDegree, ⟨Hsys⟩⟩
  rcases hmain H Hsys hg hr hpow hmaxDegree hellGrid hwGrid hlarge hscaled with
    hdirect | hstrong
  · rcases hdirect with ⟨g', hproduced, hgrid⟩
    exact (hgrid.mono hHG).of_order_le
      (PolynomialGridMinor.le_gridOrder_of_direct_branch_bound
        hcGrid hg htargetDirect hproduced)
  · rcases hstrong with ⟨r', hproduced, hgrid⟩
    have htarget_le : target ≤ r' :=
      PolynomialGridMinor.le_of_const_mul_le_const_mul hcStrong
        (le_trans htargetStrong hproduced)
    exact (hgrid.mono hHG).of_order_le htarget_le

end Exponent8
end SimpleGraph

end Lax17Proofs
