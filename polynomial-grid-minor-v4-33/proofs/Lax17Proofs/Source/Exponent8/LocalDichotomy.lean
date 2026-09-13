import Lax17Proofs.Source.Exponent8.Section5Assembly
import Lax17Proofs.Source.Section4Assembly
import Lax17Proofs.Source.Theorem41

namespace Lax17Proofs

/-!
# The exponent-eight-and-a-half local crossbar dichotomy

This module closes the source-local numerical endpoint of the experimental
three-round version of Chuzhoy--Tan Section 5.  The local terminal threshold is

`2^29 * g^8 * sqrt(g) * (log_2(g) + 1)`.

The public degree-ten theorem is not imported from this module.
-/

namespace SimpleGraph
namespace Exponent8

universe u

open Finset
open Section4Reduction

/-- The exact local crossbar-dichotomy interface used by the
exponent-eight-and-a-half experiment. -/
def CrossbarDichotomyInput85 (c C logExp : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (H : _root_.SimpleGraph V) {g kappa : ℕ}
    {A B X : Finset V},
      2 ≤ g →
        CrossbarContract.IsPowerOfTwo g →
          A.card = kappa →
            B.card = kappa →
              X.card = kappa →
                Disjoint A B →
                  Disjoint A X →
                    Disjoint B X →
                      exponentEightLocalThreshold C logExp g ≤ kappa →
                        (∀ x ∈ X, DegreeEquals H x 1) →
                          (Pab : PathPacking H A B) →
                            Pab.card = kappa →
                              (Pax : PathPacking H A X) →
                                Pax.card = kappa →
                                  Nonempty (Crossbar H A B X (g ^ 2)) ∨
                                    ∃ ell w : ℕ,
                                      g ^ 2 ≤ c * ell ∧
                                        g ^ 2 ≤ c * w ∧
                                          CrossbarContract.HasStrongPathOfSetsMinor
                                            H ell w

namespace PseudoGrid

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B X : Finset V} {g kappa : ℕ}
variable {P : PerfectPathPacking G A B}
variable {Q : PerfectPathPacking G A X}

/-- The paths discarded before Observation 4.4 fit inside the main
three-round slicing cost. -/
theorem discardCost_le_threeRoundInitialCost
    (Gamma : PseudoGrid G A B X g (64 * g ^ 4) P Q) :
    (64 * g ^ 4) * (2 * g ^ 2) ≤
      e8M0 g * e8W0 g +
        (e8M0 g + 1) * Gamma.rowPacking.card := by
  have hm : 16 * g ^ 2 ≤ e8M0 g := by
    calc
      16 * g ^ 2 ≤ 64 * g ^ 2 :=
        Nat.mul_le_mul_right (g ^ 2) (by omega)
      _ = 64 * g ^ 2 * 1 * 1 := by ring
      _ ≤
          64 * g ^ 2 * e8Fanout g * e8LogFactor g := by
        gcongr <;> simp [e8Fanout, e8LogFactor]
      _ = e8M0 g := rfl
  have hw : 8 * g ^ 4 ≤ e8W0 g := by
    unfold e8W0
    omega
  calc
    (64 * g ^ 4) * (2 * g ^ 2) =
        (16 * g ^ 2) * (8 * g ^ 4) := by ring
    _ ≤ e8M0 g * e8W0 g := Nat.mul_le_mul hm hw
    _ ≤ e8M0 g * e8W0 g +
          (e8M0 g + 1) * Gamma.rowPacking.card :=
      Nat.le_add_right _ _

/-- The advertised local threshold pays for the exact Theorem 4.6 budget
after the factor-eight retention loss in the pseudo-grid construction. -/
theorem threeRound_slicing_budget
    (Gamma : PseudoGrid G A B X g (64 * g ^ 4) P Q)
    (hg : 2 ≤ g)
    (hlarge :
      exponentEightLocalThreshold e8Constant 1 g ≤ kappa)
    (hPcard : P.card = kappa) :
    e8M0 g * e8W0 g +
          (e8M0 g + 1) * Gamma.rowPacking.card ≤
      Gamma.goodQSet.card := by
  let N := Gamma.rowPacking.card
  have hNupper : N ≤ 64 * g ^ 6 := by
    calc
      N = Gamma.reservedUnion.card := by
        simp [N]
      _ ≤ (64 * g ^ 4) * g ^ 2 :=
        Gamma.reservedUnion_card_le
      _ = 64 * g ^ 6 := by ring
  let p :=
    ThreeRoundParameters.explicitExponentEightParameters
      g N (32 * g ^ 4) hg hNupper rfl
  let cost :=
    e8M0 g * e8W0 g +
      (e8M0 g + 1) * Gamma.rowPacking.card
  let discarded := (64 * g ^ 4) * (2 * g ^ 2)
  have hdiscard : discarded ≤ cost := by
    simpa [discarded, cost] using
      discardCost_le_threeRoundInitialCost Gamma
  have hlocal :
      8 * cost ≤
        exponentEightLocalThreshold e8Constant 1 g := by
    simpa [p, N, cost,
      ThreeRoundParameters.explicitExponentEightParameters] using
      p.localCost
  have htotal :
      4 * (discarded + cost) ≤ kappa := by
    calc
      4 * (discarded + cost) ≤ 4 * (cost + cost) :=
        Nat.mul_le_mul_left 4 (Nat.add_le_add_right hdiscard cost)
      _ = 8 * cost := by ring
      _ ≤ exponentEightLocalThreshold e8Constant 1 g := hlocal
      _ ≤ kappa := hlarge
  apply Gamma.goodQSet_card_lower_bound_of_packing_bound
  rw [hPcard]
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
  simpa [discarded, cost, Nat.mul_comm] using htotal

/-- The no-crossbar pseudo-grid branch yields the strong path-of-sets minor
used by the local dichotomy. -/
theorem hasStrongPathOfSetsMinor_of_noCrossbar
    (Gamma : PseudoGrid G A B X g (64 * g ^ 4) P Q)
    (hminimal : P.IsMinimumTheorem41Pair Q)
    (hg : 2 ≤ g)
    (hpow : CrossbarContract.IsPowerOfTwo g)
    (hlarge :
      exponentEightLocalThreshold e8Constant 1 g ≤ kappa)
    (hPcard : P.card = kappa)
    (hXdisjoint :
      ∀ p : P.Index, Disjoint X (P.path p).vertexSet)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (g ^ 2))) :
    ∃ ell w : ℕ,
      g ^ 2 ≤ 20000 * ell ∧
        g ^ 2 ≤ 20000 * w ∧
          CrossbarContract.HasStrongPathOfSetsMinor G ell w := by
  have hbudget :
      e8M0 g * e8W0 g +
            (e8M0 g + 1) * Gamma.rowPacking.card ≤
        Gamma.goodQSet.card :=
    threeRound_slicing_budget Gamma hg hlarge hPcard
  have hgoodPos : 0 < Gamma.goodQSet.card := by
    have hmain : 0 < e8M0 g * e8W0 g := by
      apply Nat.mul_pos
      · unfold e8M0 e8Fanout e8LogFactor
        positivity
      · unfold e8W0
        have : 0 < 4 * g ^ 4 := by positivity
        omega
    exact hmain.trans_le
      ((Nat.le_add_right
        (e8M0 g * e8W0 g)
        ((e8M0 g + 1) * Gamma.rowPacking.card)).trans hbudget)
  have hgood : Gamma.goodQSet.Nonempty := Finset.card_pos.mp hgoodPos
  have hrowBounds :
      64 * g ^ 4 ≤ Gamma.rowPacking.card ∧
        Gamma.rowPacking.card ≤ 64 * g ^ 6 := by
    have h :=
      Gamma.rowPacking_card_bounds_of_goodQSet_nonempty hgood
    constructor
    · exact h.1
    · simpa only [show (64 * g ^ 4) * g ^ 2 = 64 * g ^ 6 by ring]
        using h.2
  rcases
      exists_reduced_weakPathOfSetsSystem_threeRound
        Gamma hminimal hg hpow hrowBounds.1 hrowBounds.2 le_rfl
        hbudget hXdisjoint hnoCrossbar with
    ⟨Root, hReduced, ⟨Pweak⟩⟩
  let w := Section4Assembly.strongifiedWidth (g ^ 2)
  have hwpos : 0 < w :=
    Section4Assembly.strongifiedWidth_pos (by positivity)
  let Dstrong :=
    Section4Assembly.strongificationData_of_weakPathOfSetsSystem_maxDegreeFour
      Pweak (Root.state.reducedGraph_maxDegreeAtMost_four hReduced)
  let Pstrong : StrongPathOfSetsSystem
      (Root.state.reducedGraph hReduced) (g ^ 2) w :=
    Section46.strong_pathOfSetsSystem_of_strongificationData Pweak Dstrong
  refine ⟨g ^ 2, w, ?_, ?_, ?_⟩
  · have : 1 ≤ 20000 := by norm_num
    simpa using Nat.le_mul_of_pos_left (g ^ 2) (by norm_num : 0 < 20000)
  · exact
      Section4Assembly.le_twentyThousand_mul_strongifiedWidth
        (by positivity)
  · exact
      ⟨Root.state.RowVertex, inferInstance, inferInstance,
        Root.state.reducedGraph hReduced,
        Root.state.reducedGraph_isMinor hReduced, ⟨Pstrong⟩⟩

end PseudoGrid

/-- The fully proved exponent-eight-and-a-half local crossbar dichotomy. -/
theorem crossbarDichotomyInput85_proved :
    CrossbarDichotomyInput85.{u} 20000 e8Constant 1 := by
  intro V _ _ H g kappa A B X hg hpow hA hB hX hAB hAX hBX hlarge
    hdegree Pab hPab Pax hPax
  have hthresholdPos :
      0 < exponentEightLocalThreshold e8Constant 1 g := by
    simp [exponentEightLocalThreshold, e8Constant]
    exact ⟨by positivity, ThreeRoundParameters.e8_sqrt_pos hg⟩
  have hdepthCost :
      (64 * g ^ 4) * (2 * g ^ 2) ≤ kappa := by
    have hg68 : g ^ 6 ≤ g ^ 8 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hs : 1 ≤ Nat.sqrt g := by
      exact ThreeRoundParameters.e8_sqrt_pos hg
    have hl : 1 ≤ Nat.log 2 g + 1 := by omega
    calc
      (64 * g ^ 4) * (2 * g ^ 2) = 128 * g ^ 6 := by ring
      _ ≤ 128 * g ^ 8 := Nat.mul_le_mul_left 128 hg68
      _ ≤ e8Constant * g ^ 8 := by
        apply Nat.mul_le_mul_right
        unfold e8Constant
        norm_num
      _ = e8Constant * g ^ 8 * 1 * 1 := by ring
      _ ≤
          exponentEightLocalThreshold e8Constant 1 g := by
        simp only [exponentEightLocalThreshold, pow_one]
        gcongr
      _ ≤ kappa := hlarge
  have hDle :
      64 * g ^ 4 ≤ kappa / (2 * g ^ 2) := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * g ^ 2)).2
    exact hdepthCost
  rcases
      theorem_four_one_of_pathPackings
        H hg hpow hA hB hX hAB hAX hBX hdegree
        Pab hPab Pax hPax (by
          have : 0 < 64 * g ^ 4 := by positivity
          omega) hDle with
    ⟨P, Q, hPcard, hQcard, hminimal, hconclusion⟩
  rcases hconclusion with hcross | hpseudo
  · exact Or.inl hcross
  · by_cases hcross : Nonempty (Crossbar H A B X (g ^ 2))
    · exact Or.inl hcross
    · rcases hpseudo with ⟨Gamma⟩
      have hXdisjoint :
          ∀ p : P.Index, Disjoint X (P.path p).vertexSet := by
        let Setup : Theorem41Setup
            H A B X g kappa (64 * g ^ 4) P Q :=
          { two_le_g := hg
            g_power_two := hpow
            A_card := hA
            B_card := hB
            X_card := hX
            disjoint_A_B := hAB
            disjoint_A_X := hAX
            disjoint_B_X := hBX
            degree_X := hdegree
            P_card := hPcard
            Q_card := hQcard
            minimal_pair := hminimal
            D_pos := by
              have : 0 < 64 * g ^ 4 := by positivity
              omega
            D_le := hDle }
        intro p
        exact (Setup.P_path_disjoint_X p).symm
      exact Or.inr <|
        SimpleGraph.Exponent8.PseudoGrid.hasStrongPathOfSetsMinor_of_noCrossbar
          Gamma
          hminimal hg hpow hlarge hPcard hXdisjoint hcross

/-- Existential constant form consumed by later experimental composition. -/
theorem exists_crossbarDichotomyInput85_proved :
    ∃ c : ℕ, 0 < c ∧
      CrossbarDichotomyInput85.{u} c e8Constant 1 :=
  ⟨20000, by norm_num, crossbarDichotomyInput85_proved⟩

end Exponent8
end SimpleGraph

end Lax17Proofs
