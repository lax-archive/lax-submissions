import Lax235315Proofs.Construction.Iterations
import Mathlib.Tactic

/-! Amortized source time and unread-bit reserves for the guarded loop. -/
namespace Lax235315Proofs.Construction.RoundPotential

/-- Above the loop threshold, the additive recurrence is a two-thirds
contraction. This is the reserve needed to pay for the next random block. -/
lemma guarded_contraction {a a' c L : ℕ} (hL : 1 ≤ L)
    (hlarge : 12 * c ^ 2 * L < a) (hshrink : a' ≤ a / 2 + c ^ 2) :
    3 * a' ≤ 2 * a := by
  have hd := Nat.div_mul_le_self a 2
  have ht := Nat.mul_le_mul_left (12 * c ^ 2) hL
  nlinarith

lemma bit_reserve_step {a a' c L : ℕ} (hL : 1 ≤ L)
    (hlarge : 12 * c ^ 2 * L < a) (hshrink : a' ≤ a / 2 + c ^ 2) :
    8 * L * a + 24 * L * a' ≤ 24 * L * a := by
  have h := Nat.mul_le_mul_left (8 * L) (guarded_contraction hL hlarge hshrink)
  nlinarith

/-- Dropping the exact key block preserves a sufficient reserve for the
next accepted round, without assuming an indefinitely long random stream. -/
lemma remaining_bits {source : List ℕ} {a a' c L : ℕ} (hL : 1 ≤ L)
    (hlarge : 12 * c ^ 2 * L < a) (hshrink : a' ≤ a / 2 + c ^ 2)
    (hreserve : 24 * L * a ≤ source.length) :
    24 * L * a' ≤ (source.drop (8 * L * a)).length := by
  rw [List.length_drop]
  have h := bit_reserve_step hL hlarge hshrink
  omega

/-- Remaining full-scan charges plus an active-key credit. -/
def potential (N L round a : ℕ) : ℕ :=
  5000 * N * (L + 1 - round) + 360 * L * a

lemma potential_step {N L round a a' c : ℕ} (hN : 1 ≤ N)
    (hL : 1 ≤ L) (hr : round + 1 ≤ L)
    (hlarge : 12 * c ^ 2 * L < a) (hshrink : a' ≤ a / 2 + c ^ 2) :
    potential N L (round + 1) a' + (4500 * N + 120 * L * a) + 4 ≤
      potential N L round a := by
  have hkey := Nat.mul_le_mul_left (120 * L) (guarded_contraction hL hlarge hshrink)
  have hdiff : L + 1 - round = (L + 1 - (round + 1)) + 1 := by omega
  unfold potential
  rw [hdiff, Nat.mul_add]
  nlinarith

/-- Rejection consumes one last round but no further loop iteration. -/
lemma potential_exit {N L round a : ℕ} (hN : 1 ≤ N) (hr : round + 1 ≤ L) :
    (4500 * N + 120 * L * a) + 4 ≤ potential N L round a := by
  have hleft : 1 ≤ L + 1 - round := by omega
  have hbase := Nat.mul_le_mul_left (5000 * N) hleft
  unfold potential
  nlinarith

lemma potential_initial {N L n : ℕ} (hn : n ≤ N) :
    potential N L 0 n ≤ 5360 * N * (L + 1) := by
  have h := Nat.mul_le_mul_left (360 * L) hn
  simp only [potential, Nat.sub_zero]
  nlinarith

end Lax235315Proofs.Construction.RoundPotential
