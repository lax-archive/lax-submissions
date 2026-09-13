import Lax17Proofs.Source.Exponent8Polylog.LocalDichotomy
import Lax17Proofs.Source.CutMatchingGame
import Lax17Proofs.Source.HairyPathOfSetsComplete
import Lax17Proofs.Source.ChekuriChuzhoyWP6Complete

namespace Lax17Proofs

/-!
# Global exponent-eight dichotomy

The local theorem supplies either a width-`g^2` crossbar or a square strong
Path-of-Sets minor. These alternatives are transferred from one hair-local
graph to the host graph. The crossbar branch uses the cut-matching
construction; the strong branch uses Chekuri--Chuzhoy Corollary 3.2.
-/

namespace SimpleGraph
namespace Exponent8Polylog

universe u

/-- Apply the exponent-eight local dichotomy inside one hair-local graph. -/
theorem crossbar_or_strong_minor_in_hairLocalGraph8 :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : _root_.SimpleGraph V} {ell w g : ℕ}
      (Hsys : HairyPathOfSetsSystem G ell w) (i : Fin ell),
        2 ≤ g →
        CrossbarContract.IsPowerOfTwo g →
        exponentEightPolylogLocalThreshold g ≤ w →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)) ∨
          ∃ ell' w' : ℕ,
            g ^ 2 ≤ 20000 * ell' ∧
            g ^ 2 ≤ 20000 * w' ∧
            CrossbarContract.HasStrongPathOfSetsMinor
              (Hsys.hairLocalGraph i) ell' w' := by
  intro V _ _ G ell w g Hsys i hg hpow hlarge
  rcases Hsys.exists_left_right_linkage_inHairLocalGraph_with_staysIn i with
    ⟨Pab, hPabCard, _⟩
  rcases Hsys.exists_left_y_perfect_linkage_inHairLocalGraph i with
    ⟨Pax, hPaxCard⟩
  have hleftY : Disjoint (Hsys.base.left i) (Hsys.y i) := by
    rw [Finset.disjoint_left]
    intro v hvLeft hvY
    exact Finset.disjoint_left.mp (Hsys.hairCluster_disjoint_base i i)
      (Hsys.y_subset_hairCluster i hvY)
      (Hsys.base.left_subset_cluster i hvLeft)
  have hrightY : Disjoint (Hsys.base.right i) (Hsys.y i) := by
    rw [Finset.disjoint_left]
    intro v hvRight hvY
    exact Finset.disjoint_left.mp (Hsys.hairCluster_disjoint_base i i)
      (Hsys.y_subset_hairCluster i hvY)
      (Hsys.base.right_subset_cluster i hvRight)
  exact crossbarDichotomyInput8_proved
    (Hsys.hairLocalGraph i) hg hpow
    (Hsys.base.left_card i) (Hsys.base.right_card i) (Hsys.y_card i)
    (Hsys.base.left_right_disjoint i) hleftY hrightY hlarge
    (fun x hx => Hsys.hairLocalGraph_degreeEquals_one_of_mem_y i hx)
    Pab hPabCard Pax.toPathPacking (by simpa using hPaxCard)

/-- Transport the strong-minor outcome from one hair-local graph to the
ambient hairy-system graph. -/
theorem crossbar_or_strong_minor_in_hairyCluster8 :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : _root_.SimpleGraph V} {ell w g : ℕ}
      (Hsys : HairyPathOfSetsSystem G ell w) (i : Fin ell),
        2 ≤ g →
        CrossbarContract.IsPowerOfTwo g →
        exponentEightPolylogLocalThreshold g ≤ w →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)) ∨
          ∃ ell' w' : ℕ,
            g ^ 2 ≤ 20000 * ell' ∧
            g ^ 2 ≤ 20000 * w' ∧
            CrossbarContract.HasStrongPathOfSetsMinor G ell' w' := by
  intro V _ _ G ell w g Hsys i hg hpow hlarge
  rcases crossbar_or_strong_minor_in_hairLocalGraph8
      Hsys i hg hpow hlarge with hcrossbar | hstrong
  · exact Or.inl hcrossbar
  · rcases hstrong with ⟨ell', w', hell, hw, hminor⟩
    exact Or.inr ⟨ell', w', hell, hw,
      hminor.mono (Hsys.hairLocalGraph_le i)⟩

/-- Either every odd one-based cluster has its local crossbar, or one cluster
already supplies an ambient square strong Path-of-Sets minor. -/
theorem local_crossbars_or_strong_minor8 :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : _root_.SimpleGraph V} {ell w g : ℕ}
      (Hsys : HairyPathOfSetsSystem G ell w),
        2 ≤ g →
        CrossbarContract.IsPowerOfTwo g →
        exponentEightPolylogLocalThreshold g ≤ w →
        (∀ i : Fin ell,
          HairyCrossbarGrid.OneBasedOdd i →
          Nonempty (Crossbar (Hsys.hairLocalGraph i)
            (Hsys.base.left i) (Hsys.base.right i)
            (Hsys.y i) (g ^ 2))) ∨
          ∃ ell' w' : ℕ,
            g ^ 2 ≤ 20000 * ell' ∧
            g ^ 2 ≤ 20000 * w' ∧
            CrossbarContract.HasStrongPathOfSetsMinor G ell' w' := by
  intro V _ _ G ell w g Hsys hg hpow hlarge
  by_cases hstrong :
      ∃ i : Fin ell, HairyCrossbarGrid.OneBasedOdd i ∧
        ∃ ell' w' : ℕ,
          g ^ 2 ≤ 20000 * ell' ∧
          g ^ 2 ≤ 20000 * w' ∧
          CrossbarContract.HasStrongPathOfSetsMinor G ell' w'
  · rcases hstrong with ⟨_, _, ell', w', hell, hw, hminor⟩
    exact Or.inr ⟨ell', w', hell, hw, hminor⟩
  · refine Or.inl ?_
    intro i hi
    rcases crossbar_or_strong_minor_in_hairyCluster8
        Hsys i hg hpow hlarge with hcrossbar | hminor
    · exact hcrossbar
    · exact False.elim (hstrong ⟨i, hi, hminor⟩)

/-- Exponent-eight hairy-system dichotomy, with the all-crossbar branch
handled by the cut-matching construction. -/
theorem gridMinor_or_strong_minor_of_hairy8 :
    ∃ cGrid : ℕ, 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
          CrossbarContract.IsPowerOfTwo g →
          MaxDegreeAtMost G 3 →
          cGrid * Nat.log 2 g ≤ ell →
          g ^ 2 ≤ w →
          exponentEightPolylogLocalThreshold g ≤ w →
          (∃ g' : ℕ,
            g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
            ContainsGridMinor G g') ∨
            ∃ ell' w' : ℕ,
              g ^ 2 ≤ 20000 * ell' ∧
              g ^ 2 ≤ 20000 * w' ∧
              CrossbarContract.HasStrongPathOfSetsMinor G ell' w' := by
  rcases
      HairyCrossbarGrid.exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_cutMatchingGame
      with ⟨cGrid, hcGrid, hgrid⟩
  refine ⟨cGrid, hcGrid, ?_⟩
  intro V _ _ G ell w g Hsys hg hpow hdegree hell hw hlarge
  rcases local_crossbars_or_strong_minor8 Hsys hg hpow hlarge with
    hcrossbars | hstrong
  · exact Or.inl (hgrid G Hsys hg hpow hdegree hell hw hcrossbars)
  · exact Or.inr hstrong

/-- Cancel the coefficient common to a scaled square and the square strong
Path-of-Sets dimensions. -/
theorem square_le_of_scaled_square_le8
    {g r n : ℕ} (hscaled : 20000 * r ^ 2 ≤ g ^ 2)
    (hn : g ^ 2 ≤ 20000 * n) : r ^ 2 ≤ n :=
  Nat.le_of_mul_le_mul_left (hscaled.trans hn) (by norm_num)

/-- Convert both hairy-system outcomes to grid minors. -/
theorem gridMinor_or_gridMinor_of_hairy8 :
    ∃ cGrid cStrong : ℕ,
      0 < cGrid ∧ 0 < cStrong ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g r : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
          2 ≤ r →
          CrossbarContract.IsPowerOfTwo g →
          MaxDegreeAtMost G 3 →
          cGrid * Nat.log 2 g ≤ ell →
          g ^ 2 ≤ w →
          exponentEightPolylogLocalThreshold g ≤ w →
          20000 * r ^ 2 ≤ g ^ 2 →
          (∃ g' : ℕ,
            g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
            ContainsGridMinor G g') ∨
            ∃ r' : ℕ,
              r ≤ cStrong * r' ∧ ContainsGridMinor G r' := by
  rcases gridMinor_or_strong_minor_of_hairy8 with
    ⟨cGrid, hcGrid, hmain⟩
  rcases
      PolynomialGridMinor.strongMinorGridInput_of_corollary32Input
        ChekuriChuzhoy.corollary32Input_proved with
    ⟨cStrong, hcStrong, hstrongGrid⟩
  refine ⟨cGrid, cStrong, hcGrid, hcStrong, ?_⟩
  intro V _ _ G ell w g r Hsys hg hr hpow hdegree hell hw hlarge hscaled
  rcases hmain G Hsys hg hpow hdegree hell hw hlarge with hgrid | hstrong
  · exact Or.inl hgrid
  · rcases hstrong with ⟨ell', w', hell', hw', hminor⟩
    exact Or.inr (hstrongGrid hr
      (square_le_of_scaled_square_le8 hscaled hell')
      (square_le_of_scaled_square_le8 hscaled hw') hminor)

/-- Parameterized graph theorem with explicit natural-number hypotheses. -/
theorem containsGridMinor_of_treewidth_parameters8 :
    ∃ cHair cHairLog cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cGrid ∧ 0 < cStrong ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k g r target : ℕ},
          1 < ell →
          1 < w →
          1 < k →
          k ≤ treewidth G →
          cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k →
          2 ≤ g →
          2 ≤ r →
          CrossbarContract.IsPowerOfTwo g →
          cGrid * Nat.log 2 g ≤ ell →
          g ^ 2 ≤ w →
          exponentEightPolylogLocalThreshold g ≤ w →
          20000 * r ^ 2 ≤ g ^ 2 →
          cGrid * target * (Nat.log 2 g) ^ 2 ≤ g →
          cStrong * target ≤ r →
          ContainsGridMinor G target := by
  rcases PolynomialGridMinor.exists_hairyPathOfSetsInput_proved with
    ⟨cHair, cHairLog, hcHair, hcHairLog, hhairy⟩
  rcases gridMinor_or_gridMinor_of_hairy8 with
    ⟨cGrid, cStrong, hcGrid, hcStrong, hmain⟩
  refine ⟨cHair, cHairLog, cGrid, cStrong,
    hcHair, hcHairLog, hcGrid, hcStrong, ?_⟩
  intro V _ _ G ell w k g r target hell hw hk htw hhairyLarge
    hg hr hpow hellGrid hwGrid hlarge hscaled htargetDirect htargetStrong
  rcases hhairy G hell hw hk htw hhairyLarge with
    ⟨H, hHG, hdegree, ⟨Hsys⟩⟩
  rcases hmain H Hsys hg hr hpow hdegree hellGrid hwGrid hlarge hscaled with
    hdirect | hstrong
  · rcases hdirect with ⟨g', hproduced, hgrid⟩
    exact (hgrid.mono hHG).of_order_le
      (PolynomialGridMinor.le_gridOrder_of_direct_branch_bound
        hcGrid hg htargetDirect hproduced)
  · rcases hstrong with ⟨r', hproduced, hgrid⟩
    have htargetLe : target ≤ r' :=
      PolynomialGridMinor.le_of_const_mul_le_const_mul hcStrong
        (htargetStrong.trans hproduced)
    exact (hgrid.mono hHG).of_order_le htargetLe

end Exponent8Polylog
end SimpleGraph

end Lax17Proofs
