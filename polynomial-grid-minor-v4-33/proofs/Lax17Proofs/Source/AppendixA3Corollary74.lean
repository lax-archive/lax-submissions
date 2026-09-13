import Lax17Proofs.Source.AppendixA3TerminalCapacity

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy Section 7, Corollary 7.4

This file proves the counting and natural-number arithmetic implication at the
end of Corollary 7.4.  Lemma 7.2 supplies the path packing; terminal degree
capacity then bounds the packing and hence the scaled size of the boundary.
-/

namespace SimpleGraph
namespace AppendixA3Corollary74


variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}

/-! ## Floor arithmetic -/

/-- Removing the floor in the arithmetic used by Corollary 7.4.

The hypotheses `0 < kappa`, `0 < d`, and `0 < alphaDen` are needed to absorb
the remainder discarded by natural-number division.  They are exactly the
positivity conditions available in the source setting. -/
theorem numerator_le_twelve_mul_of_div_three_le_two_mul
    {n kappa d alphaDen : ℕ}
    (hkappa : 0 < kappa) (hd : 0 < d) (halphaDen : 0 < alphaDen)
    (hfloor : n / (3 * alphaDen) ≤ 2 * kappa * d) :
    n ≤ 12 * kappa * d * alphaDen := by
  have hdenom : 0 < 3 * alphaDen := Nat.mul_pos (by norm_num) halphaDen
  have hkd : 0 < kappa * d := Nat.mul_pos hkappa hd
  have hcoefficient : 2 * kappa * d + 1 ≤ 4 * (kappa * d) := by
    calc
      2 * kappa * d + 1 = 2 * (kappa * d) + 1 := by ring
      _ ≤ 4 * (kappa * d) := by omega
  have hn_lt : n < (2 * kappa * d + 1) * (3 * alphaDen) :=
    (Nat.div_lt_iff_lt_mul hdenom).mp (Nat.lt_succ_of_le hfloor)
  have hscaled :
      (2 * kappa * d + 1) * (3 * alphaDen) ≤
        12 * kappa * d * alphaDen := by
    calc
      (2 * kappa * d + 1) * (3 * alphaDen) ≤
          (4 * (kappa * d)) * (3 * alphaDen) :=
        Nat.mul_le_mul_right (3 * alphaDen) hcoefficient
      _ = 12 * kappa * d * alphaDen := by ring
  exact (hn_lt.trans_le hscaled).le

/-! ## Corollary 7.4 -/

/-- Chuzhoy, Section 7, Corollary 7.4, in scaled natural-number form.

Lemma 7.2 provides at least
`floor (alphaNum * Gamma.card / (3 * alphaDen))` edge-disjoint paths from the
`2 * kappa` terminals to `Gamma`.  Since every terminal has degree at most
`d`, terminal capacity gives the claimed scaled boundary bound.  Positivity of
`alphaDen` is essential when removing the floor; `alphaNum > 0` records the
source assumption `alpha0 > 0` even though this final counting step does not
otherwise use it. -/
theorem corollary_7_4_scaled_boundary_bound_of_edgePathPacking [Fintype V]
    {C T Gamma : Finset V} {kappa d alphaNum alphaDen : ℕ}
    (hkappa : 0 < kappa) (hd : 0 < d)
    (_halphaNum : 0 < alphaNum) (halphaDen : 0 < alphaDen)
    (hTcard : T.card = 2 * kappa)
    (hT : T ⊆ C) (hGamma : Gamma ⊆ C)
    (hdisjoint : Disjoint T Gamma)
    (hdegree : MaxDegreeAtMost G d)
    (P : EdgePathPacking G T Gamma)
    (hstay : P.StaysIn C)
    (hpacking : alphaNum * Gamma.card / (3 * alphaDen) ≤ P.card) :
    alphaNum * Gamma.card ≤ 12 * kappa * d * alphaDen := by
  have hcapacity : P.card ≤ d * T.card :=
    AppendixA3TerminalCapacity.EdgePathPacking.card_le_maxDegree_mul_source_card_of_staysIn
      P hdegree hT hGamma hdisjoint hstay
  have hfloor :
      alphaNum * Gamma.card / (3 * alphaDen) ≤ 2 * kappa * d := by
    calc
      alphaNum * Gamma.card / (3 * alphaDen) ≤ P.card := hpacking
      _ ≤ d * T.card := hcapacity
      _ = 2 * kappa * d := by rw [hTcard]; ring
  exact numerator_le_twelve_mul_of_div_three_le_two_mul
    hkappa hd halphaDen hfloor

end AppendixA3Corollary74
end SimpleGraph

end Lax17Proofs
