import Lax235315Proofs.Construction.KeyFailureBounds
import Lax235315Proofs.Construction.GuardedArithmetic

/-! Rational-valued forms of the finite failure bounds, for the adaptive
protocol's probability accounting. -/

namespace Lax235315Proofs.Construction.RationalFailureBounds

open Lax235315Proofs.Construction.KeyFailureBounds
open Lax235315Proofs.Construction.Sampling
open Lax235315Proofs.Construction.FiniteRandomKeys
open Lax235315Proofs.Construction.GuardedArithmetic
open Lax235315Proofs.Construction.DriverSetup

/-- The one-round unconditioned failure fraction, in the rational field used
by `AdaptiveBitBlocks.failureMass`. -/
lemma failingAssignments_fraction_le_paper_rat
    {α : Type*} [Fintype α] [DecidableEq α] {N q c s : ℕ}
    (hN : 0 < N) (haN : Fintype.card α ≤ N) (hNq : N ≤ q)
    (hs : s ≤ Fintype.card α) {bad : Finset (Finset α)}
    (hbad : bad ⊆ samples (Finset.univ : Finset α) s)
    (hbadFraction :
      (bad.card : ℝ) / (samples (Finset.univ : Finset α) s).card ≤
        (c : ℝ) ^ 2 / N) :
    ((failingAssignments (q ^ 8) s bad).card : ℚ) /
        (allAssignments α (q ^ 8)).card ≤
      1 / (N : ℚ) ^ 6 + (c : ℚ) ^ 2 / N := by
  have hreal := failingAssignments_fraction_le_paper
    hN haN hNq hs hbad hbadFraction
  apply (Rat.cast_le (K := ℝ)).1
  push_cast
  exact hreal

/-- The guarded total failure estimate, in rationals. It is stronger than
the adaptive protocol's required one-third budget. -/
lemma paper_total_failure_le_one_six_rat {n c L rounds : ℕ}
    (hn : 12 ≤ n) (hL : L ≤ n) (hrounds : rounds ≤ L)
    (hguard : 12 * c ^ 2 * L ≤ n) :
    (rounds : ℚ) *
        (1 / (n : ℚ) ^ 6 + (c : ℚ) ^ 2 / n) ≤ 1 / 6 := by
  have hreal := paper_total_failure_le_one_six hn hL hrounds hguard
  apply (Rat.cast_le (K := ℝ)).1
  push_cast
  exact hreal

/-- The literal quotient guard supplies the numeric failure budget for at
most `clog₂ n` adaptive rounds. -/
lemma guarded_total_failure_le_one_six_rat {n c : ℕ}
    (hc : 1 ≤ c) (hn : 1 < n)
    (hguard : ¬ n / c ^ 2 < 12 * Nat.clog 2 n) :
    (Nat.clog 2 n : ℚ) *
        (1 / (n : ℚ) ^ 6 + (c : ℚ) ^ 2 / n) ≤ 1 / 6 := by
  have hL : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by omega) hn
  have hthreshold := threshold_le_of_not_square_quotient hc hn hguard
  have hn12 : 12 ≤ n := by nlinarith [hc, hL]
  exact paper_total_failure_le_one_six_rat hn12 (clog_le_vertices n)
    le_rfl hthreshold

end Lax235315Proofs.Construction.RationalFailureBounds
