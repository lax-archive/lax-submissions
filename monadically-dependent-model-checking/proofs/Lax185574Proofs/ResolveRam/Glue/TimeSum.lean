import Lax185574Proofs.ResolveRam.LenBounds
import Lax185574Proofs.ResolveRam.GlueSpec

/-!
The sum of the round times of the glue program of lem:resolve-lift.

`time_sum`: if every round takes time linear in `n + 1`, besides the
rounds `0`, `1` and the last one, which take time linear in
`(n + 1)²`, then the sum of the round times is at most `rBound`. The
number of rounds is at most `Cc * (n + 1) * Y ^ Ac` by `calls_le`.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.ResolveRam
open Lax185574Proofs.TypeTreeSizes Lax3.DistFO

/-- **The sum of the round times.** -/
theorem time_sum (k₀ q₀ : ℕ) (hk : 1 ≤ k₀) : ∃ Cc Ac : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n))
    (P Q : ℕ) (s : Bool) (f : ℕ → ℕ) (a b : ℕ),
    (∀ j ≤ (rcalls G P Q s k₀ q₀).length, f j ≤
      (if j ≤ 1 ∨ j = (rcalls G P Q s k₀ q₀).length then
        a * (n + 1) * (n + 1) *
          (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ b else 0) +
      a * (n + 1) * (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ b) →
    ∑ j ∈ Finset.range ((rcalls G P Q s k₀ q₀).length + 1), f j ≤
      rBound G k₀ q₀ P Q s (a * (Cc + 3)) (b + Ac) := by
  refine ⟨1 + 6 * (q₀ + 1) * ((k₀ + q₀ + 2) ^ 2 + 1) ^ q₀ + 1, q₀ + 1, ?_⟩
  intro n G P Q s f a b hf
  have hc := calls_le k₀ q₀ hk G P Q s
  set R := (rcalls G P Q s k₀ q₀).length with hR
  set T := treeCount G (resolveBy G s P Q) k₀ q₀ with hT
  set Y := maxTreeSize G k₀ q₀ + T + 1 with hY
  set Cr := 1 + 6 * (q₀ + 1) * ((k₀ + q₀ + 2) ^ 2 + 1) ^ q₀ with hCr
  set A := a * (n + 1) * (n + 1) * Y ^ b with hA
  set B := a * (n + 1) * Y ^ b with hB
  have h1 : ∑ j ∈ Finset.range (R + 1), f j ≤
      ∑ j ∈ Finset.range (R + 1), ((if j ≤ 1 ∨ j = R then A else 0) + B) :=
    Finset.sum_le_sum (fun j hj => hf j (by simp at hj; omega))
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, Finset.sum_ite,
    Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul] at h1
  have hcard : (Finset.filter (fun j => j ≤ 1 ∨ j = R) (Finset.range (R + 1))).card ≤ 3 := by
    calc _ ≤ ({0, 1, R} : Finset ℕ).card := Finset.card_le_card (by intro j; simp; omega)
      _ ≤ 3 := Finset.card_le_three
  set P1 := Y ^ b with hP1
  set P2 := Y ^ (q₀ + 1) with hP2
  have hP2one : 1 ≤ P2 := Nat.one_le_pow _ _ (by omega)
  have hTP : (T + 1) ^ (q₀ + 1) ≤ P2 := Nat.pow_le_pow_left (by omega) _
  have hR1 : R + 1 ≤ (Cr + 1) * (n + 1) * P2 := by
    have : Cr * (n + 1) * (T + 1) ^ (q₀ + 1) ≤ Cr * (n + 1) * P2 := Nat.mul_le_mul_left _ hTP
    have h2 : 1 ≤ (n + 1) * P2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have : (Cr + 1) * (n + 1) * P2 = Cr * (n + 1) * P2 + (n + 1) * P2 := by ring
    omega
  have e1 : (Finset.filter (fun j => j ≤ 1 ∨ j = R) (Finset.range (R + 1))).card * A ≤
      3 * (a * (n + 1) * (n + 1) * P1 * P2) := by
    calc _ ≤ 3 * A := Nat.mul_le_mul_right _ hcard
      _ ≤ 3 * (A * P2) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hP2one)
      _ = _ := by rw [hA]
  have e2 : (R + 1) * B ≤ (Cr + 1) * (a * (n + 1) * (n + 1) * P1 * P2) := by
    calc _ ≤ ((Cr + 1) * (n + 1) * P2) * B := Nat.mul_le_mul_right _ hR1
      _ = (Cr + 1) * (a * (n + 1) * (n + 1) * P1 * P2) := by rw [hB]; ring
      _ ≤ (Cr + 1) * (a * (n + 1) * (n + 1) * P1 * P2) := by
        refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_))
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have e3 : rBound G k₀ q₀ P Q s (a * (Cr + 1 + 3)) (b + (q₀ + 1)) =
      (Cr + 1) * (a * (n + 1) * (n + 1) * P1 * P2) + 3 * (a * (n + 1) * (n + 1) * P1 * P2) := by
    simp only [rBound]; rw [← hT, ← hY, pow_add, ← hP1, ← hP2]; ring
  rw [e3]
  omega

end Lax185574Proofs.ResolveRam.Glue
