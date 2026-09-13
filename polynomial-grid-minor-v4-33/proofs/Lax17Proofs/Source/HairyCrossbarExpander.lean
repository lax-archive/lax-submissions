import Lax17Proofs.Source.HairyCrossbar
import Lax17Proofs.Source.HairyCrossbarGridExpander

namespace Lax17Proofs

universe u v w

/-!
# Hairy crossbar wrappers using the explicit expander theorem handoff

This module lifts the `HairyCrossbarGridExpander` handoff through the local
crossbar dichotomy.  It is the Chuzhoy--Tan proof-facing interface after
Theorem 8.1 has been internalized: the remaining large-case inputs are a
fixed-round cut-matching transcript provider and the explicit target-size
arithmetic for Theorem 8.1.
-/

namespace SimpleGraph
namespace HairyPathOfSetsSystem




















/-- Explicit-input supergraph version of the target-provider route.  The
crossbar dichotomy, the strong-minor-to-grid theorem, and the unbundled
cut-matching/target-size package are all supplied as hypotheses. -/
theorem gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_inputs_and_unbundledCutMatching_and_targetProviders
    (hcrossInput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput.{u} c)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          {G : _root_.SimpleGraph V} {ell w g : ℕ},
            2 ≤ g →
              g ^ 2 ≤ ell →
                g ^ 2 ≤ w →
                  CrossbarContract.HasStrongPathOfSetsMinor G ell w →
                    ∃ g' : ℕ, g ≤ cStrong * g' ∧ ContainsGridMinor G g')
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        Lax17Proofs.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          Lax17Proofs.SimpleGraph.HairyCrossbarGrid.FixedRoundExpanderTargetProvider
            cRound cScale) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G H : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem H ell w),
            H ≤ G →
              2 ≤ g →
                2 ≤ r →
                  CrossbarContract.IsPowerOfTwo g →
                    MaxDegreeAtMost H 3 →
                      cGrid * Nat.log 2 g ≤ ell →
                        g ^ 2 ≤ w →
                          2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                            cCross * r ^ 2 ≤ g ^ 2 →
                              (∃ g' : ℕ,
                                g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                  ContainsGridMinor G g') ∨
                                ∃ r' : ℕ,
                                  r ≤ cStrong * r' ∧
                                    ContainsGridMinor G r' := by
  rcases local_crossbars_at_odd_clusters_or_strong_pathOfSets_minor_of_crossbarDichotomy
      hcrossInput with
    ⟨cCross, hcCross, hodd⟩
  rcases
    Lax17Proofs.SimpleGraph.HairyCrossbarGrid.exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_unbundled_and_target
      hproviders with
    ⟨cGrid, hcGrid, hgrid⟩
  rcases hstrongGrid with ⟨cStrong, hcStrong, hstrongGrid⟩
  refine ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G H ell w g r Hsys hHG hg hr hpow hmaxDegree hell hw hlarge
    hscaled
  rcases hodd Hsys hg hpow hlarge with hcrossbars | hstrong
  · rcases hgrid H Hsys hg hpow hmaxDegree hell hw hcrossbars with
      ⟨g', hbound, hgrid⟩
    exact Or.inl ⟨g', hbound, hgrid.mono hHG⟩
  · rcases hstrong with ⟨ell', w', hell', hw', hminor⟩
    rcases hstrongGrid hr
        (square_le_of_scaled_square_le hcCross hscaled hell')
        (square_le_of_scaled_square_le hcCross hscaled hw')
        hminor with
      ⟨r', hbound, hgrid⟩
    exact Or.inr ⟨r', hbound, hgrid.mono hHG⟩

/-- Explicit-input supergraph version of the target-provider route using the
Section 4 weak `g^10 log g` crossbar input. -/
theorem gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_inputs10_and_unbundledCutMatching_and_targetProviders
    (hcrossInput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput10.{u} c)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          {G : _root_.SimpleGraph V} {ell w g : ℕ},
            2 ≤ g →
              g ^ 2 ≤ ell →
                g ^ 2 ≤ w →
                  CrossbarContract.HasStrongPathOfSetsMinor G ell w →
                    ∃ g' : ℕ, g ≤ cStrong * g' ∧ ContainsGridMinor G g')
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        Lax17Proofs.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          Lax17Proofs.SimpleGraph.HairyCrossbarGrid.FixedRoundExpanderTargetProvider
            cRound cScale) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G H : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem H ell w),
            H ≤ G →
              2 ≤ g →
                2 ≤ r →
                  CrossbarContract.IsPowerOfTwo g →
                    MaxDegreeAtMost H 3 →
                      cGrid * Nat.log 2 g ≤ ell →
                        g ^ 2 ≤ w →
                          2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ w →
                            cCross * r ^ 2 ≤ g ^ 2 →
                              (∃ g' : ℕ,
                                g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                  ContainsGridMinor G g') ∨
                                ∃ r' : ℕ,
                                  r ≤ cStrong * r' ∧
                                    ContainsGridMinor G r' := by
  rcases local_crossbars_at_odd_clusters_or_strong_pathOfSets_minor_of_crossbarDichotomy10
      hcrossInput with
    ⟨cCross, hcCross, hodd⟩
  rcases
    Lax17Proofs.SimpleGraph.HairyCrossbarGrid.exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_unbundled_and_target
      hproviders with
    ⟨cGrid, hcGrid, hgrid⟩
  rcases hstrongGrid with ⟨cStrong, hcStrong, hstrongGrid⟩
  refine ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G H ell w g r Hsys hHG hg hr hpow hmaxDegree hell hw hlarge
    hscaled
  rcases hodd Hsys hg hpow hlarge with hcrossbars | hstrong
  · rcases hgrid H Hsys hg hpow hmaxDegree hell hw hcrossbars with
      ⟨g', hbound, hgrid⟩
    exact Or.inl ⟨g', hbound, hgrid.mono hHG⟩
  · rcases hstrong with ⟨ell', w', hell', hw', hminor⟩
    rcases hstrongGrid hr
        (square_le_of_scaled_square_le hcCross hscaled hell')
        (square_le_of_scaled_square_le hcCross hscaled hw')
        hminor with
      ⟨r', hbound, hgrid⟩
    exact Or.inr ⟨r', hbound, hgrid.mono hHG⟩

/-- Explicit-input supergraph version after internalizing the Theorem 8.1
target-size arithmetic. -/
theorem gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_inputs_and_unbundledCutMatching
    (hcrossInput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput.{u} c)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          {G : _root_.SimpleGraph V} {ell w g : ℕ},
            2 ≤ g →
              g ^ 2 ≤ ell →
                g ^ 2 ≤ w →
                  CrossbarContract.HasStrongPathOfSetsMinor G ell w →
                    ∃ g' : ℕ, g ≤ cStrong * g' ∧ ContainsGridMinor G g')
    (hprovider :
      ∃ cRound : ℕ, 0 < cRound ∧
        Lax17Proofs.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G H : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem H ell w),
            H ≤ G →
              2 ≤ g →
                2 ≤ r →
                  CrossbarContract.IsPowerOfTwo g →
                    MaxDegreeAtMost H 3 →
                      cGrid * Nat.log 2 g ≤ ell →
                        g ^ 2 ≤ w →
                          2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                            cCross * r ^ 2 ≤ g ^ 2 →
                              (∃ g' : ℕ,
                                g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                  ContainsGridMinor G g') ∨
                                ∃ r' : ℕ,
                                  r ≤ cStrong * r' ∧
                                    ContainsGridMinor G r' :=
  gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_inputs_and_unbundledCutMatching_and_targetProviders
    hcrossInput hstrongGrid
    (by
      rcases hprovider with ⟨cRound, hcRound, hunbundled⟩
      exact
        ⟨cRound,
          Lax17Proofs.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetScale
            cRound,
          hcRound,
          Lax17Proofs.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetScale_pos
            cRound,
          hunbundled,
          Lax17Proofs.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetProvider_explicit
            cRound⟩)


end HairyPathOfSetsSystem
end SimpleGraph

end Lax17Proofs
