import Lax185574Proofs.StpRam.ScriptRounds
import Lax185574.RankShift

/-!
The calls of the rank shift in the composite of lem:compute-stp.

Entry `i < q · n` of the list `F ++ A` is `tree_{k+a, q−a}(v)` for
`a = i / n` and `v = i % n`, and entry `i` of `A` is
`tree_{k+a+1, q−a−1}(v)`. So the call on entry `i` is a call of the
program of lem:shift at rank `(k + a, q − a − 1)`, whose constants are
bounded by the sums `cSum`, `aSum` over `a < q`.
-/

namespace Lax185574Proofs.StpRam

open Lax808846.Ram Lax808846.RamComputes Lax185574.WordEncoding Lax185574.Computing
open Lax185574.TypeTrees Lax185574.PartialGraphs Lax185574.PartialGraphEncoding

variable {n : ℕ}

/-- The sum of the constants of the rank shift at the ranks of the
calls. -/
def cSum (cS : ℕ → ℕ → ℕ) (k q : ℕ) : ℕ := ∑ j ∈ Finset.range q, cS (k + j) (q - j - 1)

/-- **A call of the rank shift.** -/
theorem callee_facts {pS : Program} {eS : ℕ} {cS aS : ℕ → ℕ → ℕ}
    (hcS : ∀ k q, ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n), 1 ≤ ℓ → ℓ ≤ k →
      Computes pS eS (cS k q) (tree G k (q + 1) u) (tree G (k + 1) q u)
        (fun m => cS k q * (m + 1) ^ aS k q))
    (G : PartialGraph (Fin n)) {k q : ℕ} (hk : 1 ≤ k) {i : ℕ} (hi : i < q * n) (v : ℕ)
    (hadm : ∀ y ∈ (famF G k q ++ answers G k q).getD i [],
      cSum cS k q * (((famF G k q ++ answers G k q).getD i []).length + y + 1) ^ eS ≤ 2 ^ v) :
    (∀ r t, RunsTo v pS ((famF G k q ++ answers G k q).getD i []) r t →
      r = (answers G k q).getD i []) ∧
    (cSum cS k q * (((famF G k q ++ answers G k q).getD i []).length + 1) ^ cSum aS k q ≤ 2 ^ v →
      ∃ t ≤ cSum cS k q * (((famF G k q ++ answers G k q).getD i []).length + 1) ^ cSum aS k q,
        RunsTo v pS ((famF G k q ++ answers G k q).getD i []) ((answers G k q).getD i []) t) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hi
    · exact h
  obtain ⟨h, h1⟩ := query_eq G k q hi
  obtain ⟨h', h2⟩ := answer_eq G k q hi
  set a := i / n with ha
  have haq : a < q := by rw [ha, Nat.div_lt_iff_lt_mul hn]; exact hi
  have hc : cS (k + a) (q - a - 1) ≤ cSum cS k q :=
    Finset.single_le_sum (f := fun j => cS (k + j) (q - j - 1)) (fun j _ => Nat.zero_le _)
      (Finset.mem_range.mpr haq)
  have hae : aS (k + a) (q - a - 1) ≤ cSum aS k q :=
    Finset.single_le_sum (f := fun j => aS (k + j) (q - j - 1)) (fun j _ => Nat.zero_le _)
      (Finset.mem_range.mpr haq)
  have hP := hcS (k + a) (q - a - 1) n G 1 ![⟨i % n, h⟩] le_rfl (le_trans hk (Nat.le_add_right _ _))
  have eq1 : toWord (tree G (k + a) (q - a - 1 + 1) ![⟨i % n, h⟩]) = (famF G k q ++ answers G k q).getD i [] := by
    rw [famF, h1, show q - a - 1 + 1 = q - a by omega]
  have eq2 : toWord (tree G (k + a + 1) (q - a - 1) ![⟨i % n, h⟩]) = (answers G k q).getD i [] := by
    rw [h2, show k + (a + 1) = k + a + 1 by ring, show q - (a + 1) = q - a - 1 by omega]
  rw [← eq1, ← eq2]
  rw [← eq1] at hadm
  have hadm' : WordAdmissible eS (cS (k + a) (q - a - 1)) v
      (toWord (tree G (k + a) (q - a - 1 + 1) ![⟨i % n, h⟩])) := fun y hy =>
    le_trans (Nat.mul_le_mul_right _ hc) (hadm y hy)
  obtain ⟨hs, ht⟩ := hP v hadm'
  refine ⟨hs, fun hT => ?_⟩
  have hX : 1 ≤ (toWord (tree G (k + a) (q - a - 1 + 1) ![⟨i % n, h⟩])).length + 1 := by omega
  have hb : cS (k + a) (q - a - 1) * (wordLength (tree G (k + a) (q - a - 1 + 1) ![⟨i % n, h⟩]) + 1) ^
      aS (k + a) (q - a - 1) ≤ cSum cS k q *
        ((toWord (tree G (k + a) (q - a - 1 + 1) ![⟨i % n, h⟩])).length + 1) ^ cSum aS k q :=
    Nat.mul_le_mul hc (Nat.pow_le_pow_right hX hae)
  obtain ⟨t, htt, hr⟩ := ht (le_trans hb hT) _ rfl
  exact ⟨t, le_trans htt hb, hr⟩

end Lax185574Proofs.StpRam
