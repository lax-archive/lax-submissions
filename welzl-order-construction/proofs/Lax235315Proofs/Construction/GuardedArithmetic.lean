import Lax235315Proofs.Construction.DriverSetup
import Lax235315Proofs.Construction.MachineBridge
import Mathlib.Tactic

/-! Arithmetic facts for the guarded reduction driver. These lemmas keep the
quotient guards separate from the source-run proof while exposing precisely
the product bounds that each guard establishes. -/
namespace Lax235315Proofs.Construction.GuardedArithmetic

open Lax11.GraphEncoding
open Lax235315Proofs.Construction.MachineBridge
open Lax235315Proofs.Construction.DriverSetup

/-- The first quotient guard implies the initial active count is below the
reduction threshold, as soon as the logarithmic factor is positive. -/
lemma initial_count_le_threshold_of_quotient {c n : ℕ}
    (hc : 1 ≤ c) (hn : 1 < n) (hquot : n / c < c) :
    n ≤ 12 * c ^ 2 * Nat.clog 2 n := by
  have hcpos : 0 < c := by omega
  have hsq : n < c ^ 2 := by
    simpa [pow_two] using (Nat.div_lt_iff_lt_mul hcpos).mp hquot
  have hL : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by omega) hn
  nlinarith

/-- Passing the first quotient guard certifies that the square of c fits
inside n. -/
lemma square_le_of_not_quotient {c n : ℕ}
    (hc : 1 ≤ c) (hquot : ¬ n / c < c) : c ^ 2 ≤ n := by
  have hdiv : c ≤ n / c := Nat.le_of_not_gt hquot
  have hprod : (n / c) * c ≤ n := Nat.div_mul_le_self n c
  nlinarith [hdiv, hprod]

/-- The second quotient guard pays for the threshold assignment. -/
lemma threshold_le_of_not_square_quotient {c n : ℕ}
    (hc : 1 ≤ c) (hn : 1 < n)
    (hquot : ¬ n / c ^ 2 < 12 * Nat.clog 2 n) :
    12 * c ^ 2 * Nat.clog 2 n ≤ n := by
  have hcsq : 0 < c ^ 2 := pow_pos (by omega : 0 < c) _
  have hdiv : 12 * Nat.clog 2 n ≤ n / c ^ 2 := Nat.le_of_not_gt hquot
  have hprod : (n / c ^ 2) * c ^ 2 ≤ n := Nat.div_mul_le_self n (c ^ 2)
  nlinarith [hdiv, hprod]

/-- Taking the small branch of the second quotient guard leaves the initial
active count below the reduction threshold (in fact, strictly below it). -/
lemma initial_count_lt_threshold_of_square_quotient {c n : ℕ}
    (hc : 1 ≤ c) (hquot : n / c ^ 2 < 12 * Nat.clog 2 n) :
    n < 12 * c ^ 2 * Nat.clog 2 n := by
  have hcsq : 0 < c ^ 2 := pow_pos (by omega : 0 < c) _
  have hmul : n < (12 * Nat.clog 2 n) * c ^ 2 :=
    (Nat.div_lt_iff_lt_mul hcsq).mp hquot
  nlinarith [hmul]

/-- Every value used by the reduction-loop guard and threshold fits the
linear source bound. The CSR length identity supplies the graph-size bounds;
the guarded square bound supplies the c-dependent bounds. -/
lemma source_fits_of_square_le {c n : ℕ} {x : List ℕ} {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G) (hc : 1 ≤ c) (hn : 1 < n)
    (hcsq : c ^ 2 ≤ n) :
    n < sourceBound c x ∧
    c < sourceBound c x ∧
    Nat.clog 2 n < sourceBound c x ∧
    2 ^ Nat.clog 2 n < sourceBound c x ∧
    2 * n + 1 < sourceBound c x ∧
    2 * edgeCount x < sourceBound c x ∧
    12 * Nat.clog 2 n < sourceBound c x ∧
    2 * c ^ 2 < sourceBound c x := by
  have hlen : n + 2 * edgeCount x + 3 = x.length := by
    have he := hx.length_eq
    omega
  have hnlen : n ≤ x.length := by omega
  have hedgelen : 2 * edgeCount x ≤ x.length := by omega
  have hcsmall : c ≤ n := by
    have hcSq : c ≤ c ^ 2 := by nlinarith [hc]
    omega
  have hLle := clog_le_vertices n
  have hpow := radix_size_lt n
  have htwice : 2 * n + 1 ≤ 3 * (x.length + c + 1) := by omega
  have hsq : 2 * c ^ 2 ≤ 2 * n := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp [sourceBound] <;>
    nlinarith [hnlen, hLle, hpow, htwice, hedgelen, hsq]

end Lax235315Proofs.Construction.GuardedArithmetic
