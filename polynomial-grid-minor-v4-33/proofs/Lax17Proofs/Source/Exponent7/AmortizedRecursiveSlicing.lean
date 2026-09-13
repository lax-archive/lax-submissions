import Lax17Proofs.Source.Exponent8.ThreeRoundRecursion

namespace Lax17Proofs

/-!
# Additive-loss amortized recursive slicing

The logarithmic-depth recursion uses the additive conclusion of Lemma 4.8,
avoiding a factor-two loss at each refinement. The definitions below specify
the binary refinement thresholds and prove the Theorem 4.6 budget together
with division-free one-step and cumulative potential bounds.
-/

namespace SimpleGraph

open Finset

universe u v

namespace Exponent8
namespace RecursiveSliceLayer

variable
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {m width Dhat g : ℕ}

/-- Additive Lemma 4.8 bounds the number of paths discarded by cleanup.

`additiveCap` is a parameter. In the exponent-seven specialization it is
`8 * g^4`; the bounds
`Rbar.card <= 64 * g^6` and `Dhat = 32 * g^4` prove `hscale`.
-/
theorem cleanup_discarded_paths_le
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) Dhat)
    (i : Fin m) {additiveCap : ℕ}
    (hscale :
      Rbar.card * (4 * g ^ 2) ≤ Dhat * additiveCap)
    (hDhat : 0 < Dhat) :
    ((L.sigma.pathsInSlice Qbar i) \ (L.cleanup i).paths).card ≤
      additiveCap := by
  have hdiscardedRows :
      ((Finset.univ : Finset Rbar.Index) \ (L.cleanup i).rows).card ≤
        Rbar.card := by
    calc
      ((Finset.univ : Finset Rbar.Index) \ (L.cleanup i).rows).card ≤
          (Finset.univ : Finset Rbar.Index).card :=
        Finset.card_le_card (Finset.sdiff_subset)
      _ = Rbar.card := by simp [PerfectPathPacking.card]
  have hscaled :
      Dhat *
          ((L.sigma.pathsInSlice Qbar i) \ (L.cleanup i).paths).card ≤
        Dhat * additiveCap := by
    calc
      Dhat *
          ((L.sigma.pathsInSlice Qbar i) \ (L.cleanup i).paths).card =
          ((L.sigma.pathsInSlice Qbar i) \ (L.cleanup i).paths).card *
            Dhat := by ac_rfl
      _ ≤
          ((Finset.univ : Finset Rbar.Index) \ (L.cleanup i).rows).card *
            (4 * g ^ 2) :=
        (L.cleanup i).additive_loss
      _ ≤ Rbar.card * (4 * g ^ 2) :=
        Nat.mul_le_mul_right (4 * g ^ 2) hdiscardedRows
      _ ≤ Dhat * additiveCap := hscale
  exact Nat.le_of_mul_le_mul_left hscaled hDhat

/-- The retained good family loses only `additiveCap + 4*g^4` paths from
the full parent slice: `additiveCap` in Lemma 4.8 and `4*g^4` in the
strengthened Claim 5.3. -/
theorem pathsInSlice_card_le_goodQ_add_loss
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) Dhat)
    (i : Fin m) {additiveCap : ℕ}
    (hscale :
      Rbar.card * (4 * g ^ 2) ≤ Dhat * additiveCap)
    (hDhat : 0 < Dhat)
    (hg : 0 < g)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (g ^ 2))) :
    (L.sigma.pathsInSlice Qbar i).card ≤
      (L.observation54GoodQ i).card + additiveCap + 4 * g ^ 4 := by
  have hpartition :=
    Finset.card_sdiff_add_card_eq_card (L.cleanup i).paths_subset
  have hdiscard :=
    L.cleanup_discarded_paths_le i hscale hDhat
  have hclaim :
      (L.cleanup i).paths.card ≤
        (L.observation54GoodQ i).card + 4 * g ^ 4 := by
    simpa [observation54GoodQ, observation54BadRows] using
      L.claim53Strong_cleanup i hg hnoCrossbar
  omega

/-- Uniform additive cleanup bound for the logarithmic-depth recursion.

Additive Lemma 4.8 discards at most `8 * g^4` paths, and the last-hit form of
Claim 5.3 discards at most another `4 * g^4`. The bound `16 * g^4` leaves
`4 * g^4` for integer rounding. -/
theorem pathsInSlice_card_le_goodQ_add_sixteen_mul_g_pow_four
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) Dhat)
    (i : Fin m)
    (hscale :
      Rbar.card * (4 * g ^ 2) ≤ Dhat * (8 * g ^ 4))
    (hDhat : 0 < Dhat)
    (hg : 0 < g)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (g ^ 2))) :
    (L.sigma.pathsInSlice Qbar i).card ≤
      (L.observation54GoodQ i).card + 16 * g ^ 4 := by
  have h :=
    L.pathsInSlice_card_le_goodQ_add_loss
      i hscale hDhat hg hnoCrossbar
  have hloss : 8 * g ^ 4 + 4 * g ^ 4 ≤ 16 * g ^ 4 := by
    omega
  omega

/-- Exact local Theorem 4.6 budget for a small slice, without the old
factor-two half-retention charge.

This is the proof-producing bridge needed by logarithmic-depth recursion.
The cost of all child cells and trivial discarded-row cuts only has to fit
inside the parent width after the additive loss.
-/
theorem goodQ_additive_budget_of_mem_small
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) Dhat)
    (i : Fin m)
    {rowCap fanout widthNext additiveCap : ℕ}
    (hi : i ∈ L.smallIndices rowCap)
    (hscale :
      Rbar.card * (4 * g ^ 2) ≤ Dhat * additiveCap)
    (hDhat : 0 < Dhat)
    (hbudget :
      fanout * widthNext + (fanout + 1) * rowCap +
          (additiveCap + 4 * g ^ 4) ≤ width)
    (hg : 0 < g)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (g ^ 2))) :
    fanout * widthNext +
        (fanout + 1) * (L.cleanup i).rows.card ≤
      (L.observation54GoodQ i).card := by
  have hrow :
      (L.cleanup i).rows.card ≤ rowCap :=
    Nat.le_of_lt ((L.mem_smallIndices rowCap i).1 hi)
  have hcost :
      fanout * widthNext +
          (fanout + 1) * (L.cleanup i).rows.card +
          (additiveCap + 4 * g ^ 4) ≤ width := by
    exact
      (Nat.add_le_add_right
        (Nat.add_le_add_left
          (Nat.mul_le_mul_left (fanout + 1) hrow)
          (fanout * widthNext))
        (additiveCap + 4 * g ^ 4)).trans hbudget
  have hwidth := L.width_at_least i
  have hretained :=
    L.pathsInSlice_card_le_goodQ_add_loss
      i hscale hDhat hg hnoCrossbar
  omega

end RecursiveSliceLayer
end Exponent8

namespace Exponent7

open Exponent8

/-! ## Binary amortized arithmetic -/

/-- Additive loss used in the exponent-seven specialization:
`8*g^4` from additive Lemma 4.8 and `4*g^4` from Claim 5.3. -/
def amortizedLoss (g : ℕ) : ℕ :=
  12 * g ^ 4

/-- A slice of width at most this threshold is terminal. -/
def amortizedStopThreshold (h Dstar : ℕ) : ℕ :=
  4096 * h * Dstar

/-- Row threshold used to decide whether a slice is productive. -/
def amortizedRowCap (h q : ℕ) : ℕ :=
  q / (1024 * h)

/-- Width of each of two children of a nonproductive slice. -/
def amortizedChildWidth (delta h q : ℕ) : ℕ :=
  (q - delta - 3 * amortizedRowCap h q) / 2

theorem amortizedRowCap_scaled_le
    (h q : ℕ) :
    1024 * h * amortizedRowCap h q ≤ q := by
  simpa [amortizedRowCap, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using
    Nat.div_mul_le_self q (1024 * h)

/-- Above the stopping threshold, all one-step charges fit into one eighth
of the parent potential.  The statement is multiplication-only. -/
theorem amortized_charges_scaled_le
    {h Dstar delta q : ℕ}
    (hh : 0 < h) (hD : 0 < Dstar)
    (hdelta : delta ≤ Dstar)
    (hcontinue : amortizedStopThreshold h Dstar < q) :
    8 * h *
        (delta + 3 * amortizedRowCap h q + 1) ≤ q := by
  have hstop :
      4096 * h * Dstar ≤ q := by
    simpa [amortizedStopThreshold] using Nat.le_of_lt hcontinue
  have hdeltaScaled :
      32 * h * delta ≤ q := by
    calc
      32 * h * delta ≤ 4096 * h * Dstar := by
        nlinarith
      _ ≤ q := hstop
  have hcapScaled :
      32 * h * (3 * amortizedRowCap h q) ≤ q := by
    calc
      32 * h * (3 * amortizedRowCap h q) =
          96 * h * amortizedRowCap h q := by ring
      _ ≤ 1024 * h * amortizedRowCap h q := by
        nlinarith
      _ ≤ q := amortizedRowCap_scaled_le h q
  have honeScaled :
      32 * h * 1 ≤ q := by
    calc
      32 * h * 1 ≤ 4096 * h * Dstar := by
        nlinarith
      _ ≤ q := hstop
  have hδ :
      4 * (8 * h * delta) ≤ q := by
    calc
      4 * (8 * h * delta) = 32 * h * delta := by ring
      _ ≤ q := hdeltaScaled
  have hc :
      4 * (8 * h * (3 * amortizedRowCap h q)) ≤ q := by
    calc
      4 * (8 * h * (3 * amortizedRowCap h q)) =
          32 * h * (3 * amortizedRowCap h q) := by ring
      _ ≤ q := hcapScaled
  have ho :
      4 * (8 * h * 1) ≤ q := by
    calc
      4 * (8 * h * 1) = 32 * h * 1 := by ring
      _ ≤ q := honeScaled
  calc
    8 * h *
        (delta + 3 * amortizedRowCap h q + 1) =
        8 * h * delta +
          8 * h * (3 * amortizedRowCap h q) +
          8 * h * 1 := by ring
    _ ≤ q := by omega

/-- The two child widths, the three trivial-cut charges, and the additive
loss fit in the parent width. -/
theorem amortizedChildWidth_budget
    {h Dstar delta q : ℕ}
    (hh : 0 < h) (hD : 0 < Dstar)
    (hdelta : delta ≤ Dstar)
    (hcontinue : amortizedStopThreshold h Dstar < q) :
    2 * amortizedChildWidth delta h q +
        3 * amortizedRowCap h q + delta ≤ q := by
  have hcharges :=
    amortized_charges_scaled_le hh hD hdelta hcontinue
  have hsum :
      delta + 3 * amortizedRowCap h q ≤ q := by
    have hh8 : 1 ≤ 8 * h := by omega
    have :
        delta + 3 * amortizedRowCap h q + 1 ≤ q := by
      calc
        delta + 3 * amortizedRowCap h q + 1 ≤
            8 * h *
              (delta + 3 * amortizedRowCap h q + 1) := by
          nlinarith
        _ ≤ q := hcharges
    omega
  have hdiv :=
    Nat.div_mul_le_self
      (q - delta - 3 * amortizedRowCap h q) 2
  dsimp [amortizedChildWidth]
  omega

/-- Rounding down by two loses at most one additional unit. -/
theorem le_two_mul_amortizedChildWidth_add_charges
    {h Dstar delta q : ℕ}
    (hh : 0 < h) (hD : 0 < Dstar)
    (hdelta : delta ≤ Dstar)
    (hcontinue : amortizedStopThreshold h Dstar < q) :
    q ≤
      2 * amortizedChildWidth delta h q +
        (delta + 3 * amortizedRowCap h q + 1) := by
  have hcharges :=
    amortized_charges_scaled_le hh hD hdelta hcontinue
  have hsum :
      delta + 3 * amortizedRowCap h q ≤ q := by
    have hh8 : 1 ≤ 8 * h := by omega
    have :
        delta + 3 * amortizedRowCap h q + 1 ≤ q := by
      calc
        delta + 3 * amortizedRowCap h q + 1 ≤
            8 * h *
              (delta + 3 * amortizedRowCap h q + 1) := by
          nlinarith
        _ ≤ q := hcharges
    omega
  let x := q - delta - 3 * amortizedRowCap h q
  have hmod := Nat.mod_lt x (by norm_num : 0 < 2)
  have hdecomp := Nat.mod_add_div x 2
  dsimp [amortizedChildWidth, x] at hmod hdecomp ⊢
  omega

/-- One binary refinement retains at least a `(1 - 1/(8h))` fraction of
the parent potential, in a division-free form. -/
theorem amortizedChildWidth_retention
    {h Dstar delta q : ℕ}
    (hh : 0 < h) (hD : 0 < Dstar)
    (hdelta : delta ≤ Dstar)
    (hcontinue : amortizedStopThreshold h Dstar < q) :
    8 * h * q ≤
      8 * h * (2 * amortizedChildWidth delta h q) + q := by
  have hsplit :=
    le_two_mul_amortizedChildWidth_add_charges
      hh hD hdelta hcontinue
  have hcharges :=
    amortized_charges_scaled_le hh hD hdelta hcontinue
  calc
    8 * h * q ≤
        8 * h *
          (2 * amortizedChildWidth delta h q +
            (delta + 3 * amortizedRowCap h q + 1)) :=
      Nat.mul_le_mul_left (8 * h) hsplit
    _ =
        8 * h * (2 * amortizedChildWidth delta h q) +
          8 * h *
            (delta + 3 * amortizedRowCap h q + 1) := by
      ring
    _ ≤ 8 * h * (2 * amortizedChildWidth delta h q) + q :=
      Nat.add_le_add_left hcharges _

/-- A continuing slice has positive child width, as required by local
Theorem 4.6. -/
theorem amortizedChildWidth_pos
    {h Dstar delta q : ℕ}
    (hh : 0 < h) (hD : 0 < Dstar)
    (hdelta : delta ≤ Dstar)
    (hcontinue : amortizedStopThreshold h Dstar < q) :
    0 < amortizedChildWidth delta h q := by
  have hcharges :=
    amortized_charges_scaled_le hh hD hdelta hcontinue
  have hchargePos :
      0 < delta + 3 * amortizedRowCap h q + 1 := by omega
  have hh8 : 1 < 8 * h := by omega
  have hstrict :
      delta + 3 * amortizedRowCap h q + 1 < q := by
    calc
      delta + 3 * amortizedRowCap h q + 1 <
          8 * h *
            (delta + 3 * amortizedRowCap h q + 1) := by
        nlinarith
      _ ≤ q := hcharges
  apply Nat.div_pos (by omega) (by norm_num)

/-- A continuing refinement stays above the terminal pruning width. -/
theorem Dstar_le_amortizedChildWidth
    {h Dstar delta q : ℕ}
    (hh : 0 < h) (hD : 0 < Dstar)
    (hdelta : delta ≤ Dstar)
    (hcontinue : amortizedStopThreshold h Dstar < q) :
    Dstar ≤ amortizedChildWidth delta h q := by
  have hcharges :=
    amortized_charges_scaled_le hh hD hdelta hcontinue
  have hDscaled :
      4 * (2 * Dstar) ≤ q := by
    exact Nat.le_of_lt <| lt_of_le_of_lt
      (show 4 * (2 * Dstar) ≤ 4096 * h * Dstar by nlinarith)
      (by simpa [amortizedStopThreshold] using hcontinue)
  have hrestScaled :
      4 * (delta + 3 * amortizedRowCap h q) ≤ q := by
    calc
      4 * (delta + 3 * amortizedRowCap h q) ≤
          8 * h *
            (delta + 3 * amortizedRowCap h q + 1) := by
        nlinarith
      _ ≤ q := hcharges
  have hfit :
      2 * Dstar + delta + 3 * amortizedRowCap h q ≤ q := by
    omega
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
  dsimp [amortizedChildWidth]
  omega

/-- Each child has at most half the parent width. -/
theorem two_mul_amortizedChildWidth_le
    (delta h q : ℕ) :
    2 * amortizedChildWidth delta h q ≤ q := by
  calc
    2 * amortizedChildWidth delta h q ≤
        q - delta - 3 * amortizedRowCap h q := by
      simpa [amortizedChildWidth, Nat.mul_comm] using
        Nat.div_mul_le_self
          (q - delta - 3 * amortizedRowCap h q) 2
    _ ≤ q := by omega

/-- Count-level form of one amortized binary refinement.

`largeCount` slices retire with their whole potential, while `smallCount`
slices each produce two children.  The returned second conjunct is exactly
the scaled-loss premise used by `AmortizedPotentialTrace.step`.
-/
theorem amortized_count_step
    {h m largeCount smallCount q qNext : ℕ}
    (hpartition : largeCount + smallCount = m)
    (hbudget : 2 * qNext ≤ q)
    (hretention :
      8 * h * q ≤ 8 * h * (2 * qNext) + q) :
    let accounted :=
      largeCount * q + (2 * smallCount) * qNext
    let loss := m * q - accounted
    accounted + loss = m * q ∧
      8 * h * loss ≤ m * q := by
  dsimp
  have haccounted :
      largeCount * q + (2 * smallCount) * qNext ≤ m * q := by
    calc
      largeCount * q + (2 * smallCount) * qNext =
          largeCount * q + smallCount * (2 * qNext) := by ring
      _ ≤ largeCount * q + smallCount * q :=
        Nat.add_le_add_left
          (Nat.mul_le_mul_left smallCount hbudget) _
      _ = m * q := by rw [← hpartition]; ring
  constructor
  · exact Nat.add_sub_of_le haccounted
  · let d := q - 2 * qNext
    have hqsplit : 2 * qNext + d = q := by
      exact Nat.add_sub_of_le hbudget
    have hdscaled :
        8 * h * d ≤ q := by
      have hretention' :
          8 * h * (2 * qNext + d) ≤
            8 * h * (2 * qNext) + q := by
        simpa [hqsplit] using hretention
      nlinarith
    have hlossEq :
        m * q -
            (largeCount * q + (2 * smallCount) * qNext) =
          smallCount * d := by
      rw [← hpartition]
      simp only [Nat.add_mul]
      rw [Nat.add_sub_add_left]
      rw [show (2 * smallCount) * qNext =
          smallCount * (2 * qNext) by ring]
      rw [← Nat.mul_sub_left_distrib]
    rw [hlossEq]
    calc
      8 * h * (smallCount * d) =
          smallCount * (8 * h * d) := by ring
      _ ≤ smallCount * q :=
        Nat.mul_le_mul_left smallCount hdscaled
      _ ≤ m * q := by
        exact Nat.mul_le_mul_right q
          (by omega)

/-- A continuing slice has row cap at least one. -/
theorem one_le_amortizedRowCap
    {h Dstar q : ℕ}
    (hh : 0 < h) (hD : 0 < Dstar)
    (hcontinue : amortizedStopThreshold h Dstar < q) :
    1 ≤ amortizedRowCap h q := by
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 1024 * h)).2
  exact Nat.le_of_lt <| lt_of_le_of_lt
    (show 1 * (1024 * h) ≤ 4096 * h * Dstar by nlinarith)
    (by simpa [amortizedStopThreshold] using hcontinue)

/-- The parent width is at most twice the denominator times its productive
row cap. -/
theorem width_le_two_mul_amortizedRowCap
    {h Dstar q : ℕ}
    (hh : 0 < h) (hD : 0 < Dstar)
    (hcontinue : amortizedStopThreshold h Dstar < q) :
    q ≤ 2048 * h * amortizedRowCap h q := by
  have hden : 0 < 1024 * h := by positivity
  have hquot : 1 ≤ amortizedRowCap h q :=
    one_le_amortizedRowCap hh hD hcontinue
  have hstrict :
      q < (1024 * h) * (q / (1024 * h) + 1) :=
    Nat.lt_mul_div_succ q hden
  calc
    q ≤ (1024 * h) * (amortizedRowCap h q + 1) :=
      (by simpa [amortizedRowCap] using Nat.le_of_lt hstrict)
    _ ≤ (1024 * h) * (2 * amortizedRowCap h q) := by
      exact Nat.mul_le_mul_left (1024 * h) (by omega)
    _ = 2048 * h * amortizedRowCap h q := by ring

/-- Productive slice potential is charged to its retained-row mass. -/
theorem largePotential_le_weighted_rowMass
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {g Dhat m q h Dstar : ℕ}
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m q (4 * g ^ 2) Dhat)
    (hh : 0 < h) (hD : 0 < Dstar)
    (hcontinue : amortizedStopThreshold h Dstar < q) :
    (L.largeIndices (amortizedRowCap h q)).card * q ≤
      2048 * h *
        (∑ i ∈ L.largeIndices (amortizedRowCap h q),
          (L.cleanup i).rows.card) := by
  have hcapRows :
      (L.largeIndices (amortizedRowCap h q)).card *
          amortizedRowCap h q ≤
        ∑ i ∈ L.largeIndices (amortizedRowCap h q),
          (L.cleanup i).rows.card := by
    calc
      (L.largeIndices (amortizedRowCap h q)).card *
          amortizedRowCap h q =
          ∑ _i ∈ L.largeIndices (amortizedRowCap h q),
            amortizedRowCap h q := by
        simp
      _ ≤
          ∑ i ∈ L.largeIndices (amortizedRowCap h q),
            (L.cleanup i).rows.card := by
        exact Finset.sum_le_sum fun i hi =>
          (L.mem_largeIndices (amortizedRowCap h q) i).1 hi
  calc
    (L.largeIndices (amortizedRowCap h q)).card * q ≤
        (L.largeIndices (amortizedRowCap h q)).card *
          (2048 * h * amortizedRowCap h q) :=
      Nat.mul_le_mul_left _
        (width_le_two_mul_amortizedRowCap hh hD hcontinue)
    _ =
        2048 * h *
          ((L.largeIndices (amortizedRowCap h q)).card *
            amortizedRowCap h q) := by ring
    _ ≤
        2048 * h *
          (∑ i ∈ L.largeIndices (amortizedRowCap h q),
            (L.cleanup i).rows.card) :=
      Nat.mul_le_mul_left (2048 * h) hcapRows

/-! ## Proof-producing refinement of every nonproductive slice -/

/-- Refine every slice whose cleanup has fewer than `rowCap` rows.

Unlike `Exponent8.recursiveSlicingRound`, this theorem does not require the
small slices to form a majority and does not discard a prescribed fraction
of their count.  The next slicing has exactly two (or, abstractly, `fanout`)
children for each selected small slice.  This is the state transition used by
the amortized controller.
-/
theorem refineAllSmallSlicesAdditive
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {g Dhat m width rowCap fanout widthNext additiveCap : ℕ}
    (C : RecursiveSlicingContext
      G H A B X P Q Rbar Qbar Dhat)
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) Dhat)
    (hg : 0 < g)
    (hfanout : 0 < fanout)
    (hwidthNext : 0 < widthNext)
    (hsmall :
      0 < (L.smallIndices rowCap).card)
    (hscale :
      Rbar.card * (4 * g ^ 2) ≤ Dhat * additiveCap)
    (hbudget :
      fanout * widthNext + (fanout + 1) * rowCap +
          (additiveCap + 4 * g ^ 4) ≤ width)
    (hmassNext :
      2 * Rbar.card * (4 * g ^ 2) ≤ Dhat * widthNext)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (g ^ 2))) :
    Nonempty
      (RecursiveSliceLayer
        G H A B X P Q Rbar Qbar
        ((L.smallIndices rowCap).card * fanout)
        widthNext (4 * g ^ 2) Dhat) := by
  classical
  let small := L.smallIndices rowCap
  let selected : Fin small.card → Fin m :=
    small.orderEmbOfFin rfl
  have hselected : StrictMono selected :=
    (small.orderEmbOfFin rfl).strictMono
  have hselectedSmall :
      ∀ a : Fin small.card, selected a ∈ small := by
    intro a
    exact small.orderEmbOfFin_mem rfl a
  let refine :
      ∀ a : Fin small.card,
        PathSlicing.ExtendedParentRefinement
          L.sigma Qbar (selected a) fanout widthNext :=
    fun a =>
      Classical.choice
        (L.exists_observation54ExtendedParentRefinement
          (selected a) C.Dhat_pos hfanout hwidthNext
          (L.goodQ_additive_budget_of_mem_small
            (selected a) (hselectedSmall a)
            hscale C.Dhat_pos hbudget hg hnoCrossbar))
  rcases
      PathSlicing.composeSelectedSliceRefinements
        L.sigma selected hselected refine
          (by simpa [small] using hsmall) hfanout with
    ⟨tau, htau, _hcell⟩
  exact ⟨C.toLayer tau htau hmassNext⟩

/-! ## A reusable finite potential trace -/

/-- An amortized trace indexed by its initial active potential.

At one step, `output` is potential retired into productive slices, `next` is
the active child potential, and `loss` is the exact unaccounted amount.  The
only analytic hypothesis is `scale * loss ≤ potential`.
-/
inductive AmortizedPotentialTrace (scale : ℕ) : ℕ → Type
  | terminal (potential : ℕ) :
      AmortizedPotentialTrace scale potential
  | step {potential next : ℕ}
      (output loss : ℕ)
      (balance : output + next + loss = potential)
      (scaled_loss : scale * loss ≤ potential)
      (tail : AmortizedPotentialTrace scale next) :
      AmortizedPotentialTrace scale potential

namespace AmortizedPotentialTrace

variable {scale initial : ℕ}

/-- Number of actual refinement steps in a trace. -/
def steps {scale : ℕ} :
    {initial : ℕ} → AmortizedPotentialTrace scale initial → ℕ
  | _, .terminal _ => 0
  | _, .step _ _ _ _ tail => steps tail + 1

/-- Total productive potential plus the final terminal active potential. -/
def outcome {scale : ℕ} :
    {initial : ℕ} → AmortizedPotentialTrace scale initial → ℕ
  | _, .terminal p => p
  | _, .step output _ _ _ tail => output + outcome tail

/-- Total unaccounted potential over all refinement steps. -/
def totalLoss {scale : ℕ} :
    {initial : ℕ} → AmortizedPotentialTrace scale initial → ℕ
  | _, .terminal _ => 0
  | _, .step _ loss _ _ tail => loss + totalLoss tail

/-- The initial potential partitions exactly into final outcomes and losses. -/
theorem outcome_add_totalLoss
    (t : AmortizedPotentialTrace scale initial) :
    t.outcome + t.totalLoss = initial := by
  induction t with
  | terminal p =>
      simp [outcome, totalLoss]
  | step output loss balance scaled_loss tail ih =>
      simp only [outcome, totalLoss]
      omega

/-- Outcomes can never exceed the initial potential. -/
theorem outcome_le
    (t : AmortizedPotentialTrace scale initial) :
    t.outcome ≤ initial := by
  have := t.outcome_add_totalLoss
  omega

/-- The accumulated scaled loss is at most `steps * initial`.

This is the induction that makes a logarithmic number of refinement levels
safe: every later active potential is already bounded by the preceding one.
-/
theorem scale_mul_totalLoss_le
    (t : AmortizedPotentialTrace scale initial) :
    scale * t.totalLoss ≤ t.steps * initial := by
  induction t with
  | terminal p =>
      simp [steps, totalLoss]
  | @step potential next output loss balance scaled_loss tail ih =>
      have hnext : next ≤ potential := by omega
      calc
        scale * (AmortizedPotentialTrace.totalLoss
            (.step output loss balance scaled_loss tail)) =
            scale * loss + scale * tail.totalLoss := by
          simp [totalLoss, Nat.mul_add]
        _ ≤ potential + tail.steps * next :=
          Nat.add_le_add scaled_loss ih
        _ ≤ potential + tail.steps * potential :=
          Nat.add_le_add_left
            (Nat.mul_le_mul_left tail.steps hnext) potential
        _ =
            (AmortizedPotentialTrace.steps
              (.step output loss balance scaled_loss tail)) *
                potential := by
          simp [steps]
          ring

/-- At most `h` steps, each losing at most a `1/(8h)` fraction of its active
potential, retain at least seven eighths of the initial potential. -/
theorem seven_mul_initial_le_eight_mul_outcome
    {h : ℕ} (hh : 0 < h)
    (t : AmortizedPotentialTrace (8 * h) initial)
    (hsteps : t.steps ≤ h) :
    7 * initial ≤ 8 * t.outcome := by
  have hloss :
      8 * h * t.totalLoss ≤ h * initial := by
    calc
      8 * h * t.totalLoss ≤ t.steps * initial :=
        t.scale_mul_totalLoss_le
      _ ≤ h * initial :=
        Nat.mul_le_mul_right initial hsteps
  have hbalance := t.outcome_add_totalLoss
  have hcancel :
      h * (7 * initial) +
          8 * h * t.totalLoss ≤
        h * (8 * t.outcome) +
          8 * h * t.totalLoss := by
    calc
      h * (7 * initial) +
          8 * h * t.totalLoss ≤
          h * (7 * initial) + h * initial :=
        Nat.add_le_add_left hloss _
      _ = 8 * h * initial := by ring
      _ =
          8 * h * (t.outcome + t.totalLoss) := by
        rw [hbalance]
      _ =
          h * (8 * t.outcome) +
            8 * h * t.totalLoss := by ring
  have hmul :
      h * (7 * initial) ≤ h * (8 * t.outcome) :=
    Nat.le_of_add_le_add_right hcancel
  exact Nat.le_of_mul_le_mul_left hmul hh

end AmortizedPotentialTrace

end Exponent7
end SimpleGraph

end Lax17Proofs
