import Lax17Proofs.Source.Exponent8.AllHappyClusters
import Lax17Proofs.Source.CrossbarPower
import Mathlib.Data.Nat.Log

namespace Lax17Proofs

/-!
# Dyadic grouping of happy clusters

This is the multiplication-only geometric grouping from Chuzhoy--Tan
Section 5.1.  There are `2 * (log_2 g + 1)` classes.  The first classes are
half-open; the final class is closed at its upper endpoint.  The latter is
necessary when the row bound is the non-strict inequality
`N <= 64 * g^6`.
-/

namespace SimpleGraph
namespace Exponent8

open Finset

/-- Number of geometric classes used in the large-slice branch. -/
def dyadicClassCount (g : ℕ) : ℕ :=
  2 * (Nat.log 2 g + 1)

/-- Lower row threshold of geometric class `j`. -/
def dyadicClassDepth (g : ℕ)
    (j : Fin (dyadicClassCount g)) : ℕ :=
  16 * g ^ 4 * 2 ^ j.1

/-- Candidate dyadic exponents whose lower threshold is at most `n`. -/
private def dyadicEligible (K base n : ℕ) : Finset (Fin K) :=
  Finset.univ.filter fun j => base * 2 ^ j.1 ≤ n

private theorem dyadicEligible_nonempty
    {K base n : ℕ} (hK : 0 < K) (hbase : base ≤ n) :
    (dyadicEligible K base n).Nonempty := by
  let z : Fin K := ⟨0, hK⟩
  refine ⟨z, ?_⟩
  simp [dyadicEligible, z, hbase]

/-- Largest available dyadic exponent whose lower threshold is at most `n`. -/
private noncomputable def dyadicBucket
    (K base n : ℕ) (hK : 0 < K) (hbase : base ≤ n) : Fin K :=
  (dyadicEligible K base n).max'
    (dyadicEligible_nonempty hK hbase)

private theorem dyadicBucket_mem
    {K base n : ℕ} (hK : 0 < K) (hbase : base ≤ n) :
    dyadicBucket K base n hK hbase ∈ dyadicEligible K base n :=
  Finset.max'_mem _ _

private theorem dyadicBucket_lower
    {K base n : ℕ} (hK : 0 < K) (hbase : base ≤ n) :
    base * 2 ^ (dyadicBucket K base n hK hbase).1 ≤ n := by
  exact (Finset.mem_filter.1 (dyadicBucket_mem hK hbase)).2

private theorem dyadicBucket_strict_upper_of_not_last
    {K base n : ℕ} (hK : 0 < K) (hbase : base ≤ n)
    (hnext :
      (dyadicBucket K base n hK hbase).1 + 1 < K) :
    n <
      base * 2 ^ ((dyadicBucket K base n hK hbase).1 + 1) := by
  let j := dyadicBucket K base n hK hbase
  let js : Fin K := ⟨j.1 + 1, hnext⟩
  by_contra hnot
  have hnextLower :
      base * 2 ^ js.1 ≤ n := by
    exact Nat.le_of_not_gt hnot
  have hjsMem : js ∈ dyadicEligible K base n := by
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hnextLower⟩
  have hle : js ≤ j :=
    Finset.le_max' (dyadicEligible K base n) js hjsMem
  have hval : js.1 ≤ j.1 := Fin.mk_le_mk.mp hle
  dsimp [js] at hval
  omega

private theorem dyadicBucket_upper
    {K base n : ℕ} (hK : 0 < K) (hbase : base ≤ n)
    (htop : n ≤ base * 2 ^ K) :
    n ≤
      2 * (base * 2 ^ (dyadicBucket K base n hK hbase).1) := by
  let j := dyadicBucket K base n hK hbase
  by_cases hnext : j.1 + 1 < K
  · have hstrict :=
      dyadicBucket_strict_upper_of_not_last hK hbase hnext
    calc
      n ≤ base * 2 ^ (j.1 + 1) := Nat.le_of_lt hstrict
      _ = 2 * (base * 2 ^ j.1) := by
        rw [pow_succ]
        ring
  · have hjlast : j.1 + 1 = K := by
      have hjlt := j.2
      omega
    calc
      n ≤ base * 2 ^ K := htop
      _ = base * 2 ^ (j.1 + 1) := by
        exact congrArg (fun e => base * 2 ^ e) hjlast.symm
      _ = 2 * (base * 2 ^ j.1) := by
        rw [pow_succ]
        ring

/-- The upper endpoint of the final class.  The equality is exact for the
source convention that `g` is an integral power of two. -/
theorem dyadic_top_endpoint
    {g : ℕ} (hpow : CrossbarContract.IsPowerOfTwo g) :
    16 * g ^ 4 * 2 ^ dyadicClassCount g = 64 * g ^ 6 := by
  rcases hpow with ⟨k, rfl⟩
  simp only [dyadicClassCount, Nat.log_pow (by decide : 1 < 2)]
  rw [show 2 * (k + 1) = (k + 1) * 2 by omega]
  rw [pow_mul, pow_succ]
  ring

/-- One geometric class together with the mass and count inequalities needed
by Theorem 4.15. -/
structure DyadicClusterClass
    {C : ℕ} (size : Fin C → ℕ) (g N : ℕ) where
  j : Fin (dyadicClassCount g)
  members : Finset (Fin C)
  mass :
    4 * N * g ^ 2 ≤ ∑ c ∈ members, size c
  lower :
    ∀ c ∈ members, dyadicClassDepth g j ≤ size c
  upper :
    ∀ c ∈ members, size c ≤ 2 * dyadicClassDepth g j
  strict_upper_of_not_last :
    ∀ c ∈ members,
      j.1 + 1 < dyadicClassCount g →
        size c < 2 * dyadicClassDepth g j
  count_mass :
    2 * N * g ^ 2 ≤ dyadicClassDepth g j * members.card

/-- Corrected dyadic grouping theorem.  The final class is closed on the
right, so the non-strict source bound `N <= 64*g^6` covers its endpoint. -/
noncomputable def exists_dyadicClusterClass
    {C : ℕ} (size : Fin C → ℕ)
    (g N : ℕ)
    (hg : 2 ≤ g)
    (hpow : CrossbarContract.IsPowerOfTwo g)
    (hsizeLower : ∀ c, 16 * g ^ 4 ≤ size c)
    (hsizeUpper : ∀ c, size c ≤ N)
    (hNupper : N ≤ 64 * g ^ 6)
    (hmass :
      8 * N * g ^ 2 * (Nat.log 2 g + 1) ≤
        ∑ c : Fin C, size c) :
    DyadicClusterClass size g N := by
  classical
  let K := dyadicClassCount g
  let base := 16 * g ^ 4
  have hK : 0 < K := by
    dsimp [K, dyadicClassCount]
    omega
  let bucket : Fin C → Fin K :=
    fun c => dyadicBucket K base (size c) hK (hsizeLower c)
  let members : Fin K → Finset (Fin C) :=
    fun j => Finset.univ.filter fun c => bucket c = j
  let classMass : Fin K → ℕ :=
    fun j => ∑ c ∈ members j, size c
  have hpartition :
      (∑ j : Fin K, classMass j) =
        ∑ c : Fin C, size c := by
    simpa [classMass, members] using
      (Finset.sum_fiberwise_eq_sum_filter
        (Finset.univ : Finset (Fin C))
        (Finset.univ : Finset (Fin K))
        bucket size)
  let hmax :=
    Finset.exists_max_image
      (Finset.univ : Finset (Fin K)) classMass
      (Finset.univ_nonempty_iff.2 ⟨⟨0, hK⟩⟩)
  let j : Fin K := hmax.choose
  have hjmax :
      ∀ t ∈ (Finset.univ : Finset (Fin K)),
        classMass t ≤ classMass j :=
    hmax.choose_spec.2
  have hsumMax :
      (∑ t : Fin K, classMass t) ≤ K * classMass j := by
    simpa [Nat.nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul
        (Finset.univ : Finset (Fin K)) classMass (classMass j)
        (fun t ht => hjmax t ht))
  have hmassMax :
      8 * N * g ^ 2 * (Nat.log 2 g + 1) ≤
        K * classMass j := by
    exact hmass.trans (hpartition.symm ▸ hsumMax)
  have hKfactor :
      K * (4 * N * g ^ 2) =
        8 * N * g ^ 2 * (Nat.log 2 g + 1) := by
    simp [K, dyadicClassCount]
    ring
  have hclassMass :
      4 * N * g ^ 2 ≤ classMass j := by
    apply Nat.le_of_mul_le_mul_left
      (show K * (4 * N * g ^ 2) ≤ K * classMass j by
        rw [hKfactor]
        exact hmassMax)
      hK
  have htop :
      ∀ c : Fin C, size c ≤ base * 2 ^ K := by
    intro c
    calc
      size c ≤ N := hsizeUpper c
      _ ≤ 64 * g ^ 6 := hNupper
      _ = base * 2 ^ K := by
        dsimp [base, K]
        exact (dyadic_top_endpoint hpow).symm
  have hlower :
      ∀ c ∈ members j,
        dyadicClassDepth g
          ⟨j.1, by simpa [K] using j.2⟩ ≤ size c := by
    intro c hc
    have hbc : bucket c = j := (Finset.mem_filter.1 hc).2
    have hb :=
      dyadicBucket_lower hK (hsizeLower c)
    change base * 2 ^ (bucket c).1 ≤ size c at hb
    rw [hbc] at hb
    simpa [dyadicClassDepth, base] using hb
  have hupper :
      ∀ c ∈ members j,
        size c ≤
          2 * dyadicClassDepth g
            ⟨j.1, by simpa [K] using j.2⟩ := by
    intro c hc
    have hbc : bucket c = j := (Finset.mem_filter.1 hc).2
    have hb :=
      dyadicBucket_upper hK (hsizeLower c) (htop c)
    change size c ≤ 2 * (base * 2 ^ (bucket c).1) at hb
    rw [hbc] at hb
    simpa [dyadicClassDepth, base] using hb
  have hstrict :
      ∀ c ∈ members j,
        j.1 + 1 < K →
          size c <
            2 * dyadicClassDepth g
              ⟨j.1, by simpa [K] using j.2⟩ := by
    intro c hc hjnext
    have hbc : bucket c = j := (Finset.mem_filter.1 hc).2
    have hjnext' : (bucket c).1 + 1 < K := by
      rw [hbc]
      exact hjnext
    have hb :=
      dyadicBucket_strict_upper_of_not_last
        hK (hsizeLower c) hjnext'
    change size c < base * 2 ^ ((bucket c).1 + 1) at hb
    rw [hbc] at hb
    calc
      size c < base * 2 ^ (j.1 + 1) := hb
      _ = 2 * dyadicClassDepth g
          ⟨j.1, by simpa [K] using j.2⟩ := by
        simp [dyadicClassDepth, base, pow_succ]
        ring
  let jg : Fin (dyadicClassCount g) :=
    ⟨j.1, by simpa [K] using j.2⟩
  have hmassUpper :
      classMass j ≤
        (members j).card * (2 * dyadicClassDepth g jg) := by
    exact
      Finset.sum_le_card_nsmul
        (members j) size (2 * dyadicClassDepth g jg)
        (by
          intro c hc
          exact hupper c hc)
  have htwice :
      2 * (2 * N * g ^ 2) ≤
        2 * (dyadicClassDepth g jg * (members j).card) := by
    calc
      2 * (2 * N * g ^ 2) = 4 * N * g ^ 2 := by ring
      _ ≤ classMass j := hclassMass
      _ ≤ (members j).card * (2 * dyadicClassDepth g jg) :=
        hmassUpper
      _ = 2 * (dyadicClassDepth g jg * (members j).card) := by
        ring
  have hcount :
      2 * N * g ^ 2 ≤
        dyadicClassDepth g jg * (members j).card :=
    Nat.le_of_mul_le_mul_left htwice (by omega)
  exact
    { j := jg
      members := members j
      mass := by
        simpa [classMass] using hclassMass
      lower := hlower
      upper := hupper
      strict_upper_of_not_last := by
        intro c hc hnotLast
        exact hstrict c hc (by simpa [K] using hnotLast)
      count_mass := hcount }

end Exponent8
end SimpleGraph

end Lax17Proofs
