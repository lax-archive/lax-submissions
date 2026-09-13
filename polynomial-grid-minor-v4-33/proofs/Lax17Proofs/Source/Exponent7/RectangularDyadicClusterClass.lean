import Lax17Proofs.Source.Exponent8.DyadicClusterClass

namespace Lax17Proofs

/-!
# Rectangular dyadic grouping

The geometric row-depth classes use a separate mass target: `L` is the
required number of clusters in the rectangular Theorem 4.15 chain, while the
overlap width is independent.
-/

namespace SimpleGraph
namespace Exponent7

open Finset
open Exponent8

private def rectangularDyadicEligible
    (K base n : ℕ) : Finset (Fin K) :=
  Finset.univ.filter fun j => base * 2 ^ j.1 ≤ n

private theorem rectangularDyadicEligible_nonempty
    {K base n : ℕ} (hK : 0 < K) (hbase : base ≤ n) :
    (rectangularDyadicEligible K base n).Nonempty := by
  let z : Fin K := ⟨0, hK⟩
  exact ⟨z, by simp [rectangularDyadicEligible, z, hbase]⟩

private noncomputable def rectangularDyadicBucket
    (K base n : ℕ) (hK : 0 < K) (hbase : base ≤ n) : Fin K :=
  (rectangularDyadicEligible K base n).max'
    (rectangularDyadicEligible_nonempty hK hbase)

private theorem rectangularDyadicBucket_lower
    {K base n : ℕ} (hK : 0 < K) (hbase : base ≤ n) :
    base *
        2 ^ (rectangularDyadicBucket K base n hK hbase).1 ≤ n := by
  exact (Finset.mem_filter.1
    (Finset.max'_mem
      (rectangularDyadicEligible K base n)
      (rectangularDyadicEligible_nonempty hK hbase))).2

private theorem rectangularDyadicBucket_strict_upper_of_not_last
    {K base n : ℕ} (hK : 0 < K) (hbase : base ≤ n)
    (hnext :
      (rectangularDyadicBucket K base n hK hbase).1 + 1 < K) :
    n <
      base *
        2 ^ ((rectangularDyadicBucket K base n hK hbase).1 + 1) := by
  let j := rectangularDyadicBucket K base n hK hbase
  let js : Fin K := ⟨j.1 + 1, hnext⟩
  by_contra hnot
  have hjsMem :
      js ∈ rectangularDyadicEligible K base n := by
    exact Finset.mem_filter.2
      ⟨Finset.mem_univ _, Nat.le_of_not_gt hnot⟩
  have hle : js ≤ j :=
    Finset.le_max'
      (rectangularDyadicEligible K base n) js hjsMem
  have hval : js.1 ≤ j.1 := Fin.mk_le_mk.mp hle
  dsimp [js] at hval
  omega

private theorem rectangularDyadicBucket_upper
    {K base n : ℕ} (hK : 0 < K) (hbase : base ≤ n)
    (htop : n ≤ base * 2 ^ K) :
    n ≤
      2 *
        (base *
          2 ^ (rectangularDyadicBucket K base n hK hbase).1) := by
  let j := rectangularDyadicBucket K base n hK hbase
  by_cases hnext : j.1 + 1 < K
  · have hstrict :=
      rectangularDyadicBucket_strict_upper_of_not_last
        hK hbase hnext
    calc
      n ≤ base * 2 ^ (j.1 + 1) := Nat.le_of_lt hstrict
      _ = 2 * (base * 2 ^ j.1) := by
        rw [pow_succ]
        ring
  · have hjlast : j.1 + 1 = K := by omega
    calc
      n ≤ base * 2 ^ K := htop
      _ = base * 2 ^ (j.1 + 1) := by rw [hjlast]
      _ = 2 * (base * 2 ^ j.1) := by
        rw [pow_succ]
        ring

/-- One dyadic row-depth class carrying enough mass for a chain of length
`L`. -/
structure RectangularDyadicClusterClass
    {C : ℕ} (size : Fin C → ℕ) (g N L : ℕ) where
  j : Fin (dyadicClassCount g)
  members : Finset (Fin C)
  mass :
    4 * N * L ≤ ∑ c ∈ members, size c
  lower :
    ∀ c ∈ members, dyadicClassDepth g j ≤ size c
  upper :
    ∀ c ∈ members, size c ≤ 2 * dyadicClassDepth g j
  strict_upper_of_not_last :
    ∀ c ∈ members,
      j.1 + 1 < dyadicClassCount g →
        size c < 2 * dyadicClassDepth g j
  count_mass :
    2 * N * L ≤ dyadicClassDepth g j * members.card

/-- Corrected rectangular dyadic grouping.  As in the square proof, the final
class is closed at its upper endpoint. -/
noncomputable def exists_rectangularDyadicClusterClass
    {C : ℕ} (size : Fin C → ℕ)
    (g N L : ℕ)
    (hg : 2 ≤ g)
    (hpow : CrossbarContract.IsPowerOfTwo g)
    (hsizeLower : ∀ c, 16 * g ^ 4 ≤ size c)
    (hsizeUpper : ∀ c, size c ≤ N)
    (hNupper : N ≤ 64 * g ^ 6)
    (hmass :
      8 * N * L * (Nat.log 2 g + 1) ≤
        ∑ c : Fin C, size c) :
    RectangularDyadicClusterClass size g N L := by
  classical
  let K := dyadicClassCount g
  let base := 16 * g ^ 4
  have hK : 0 < K := by
    dsimp [K, dyadicClassCount]
    omega
  let bucket : Fin C → Fin K :=
    fun c =>
      rectangularDyadicBucket
        K base (size c) hK (hsizeLower c)
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
        (Finset.univ : Finset (Fin K)) classMass
        (classMass j) (fun t ht => hjmax t ht))
  have hmassMax :
      8 * N * L * (Nat.log 2 g + 1) ≤
        K * classMass j :=
    hmass.trans (hpartition.symm ▸ hsumMax)
  have hKfactor :
      K * (4 * N * L) =
        8 * N * L * (Nat.log 2 g + 1) := by
    simp [K, dyadicClassCount]
    ring
  have hclassMass :
      4 * N * L ≤ classMass j := by
    apply Nat.le_of_mul_le_mul_left
      (show K * (4 * N * L) ≤ K * classMass j by
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
      rectangularDyadicBucket_lower hK (hsizeLower c)
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
      rectangularDyadicBucket_upper
        hK (hsizeLower c) (htop c)
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
      rectangularDyadicBucket_strict_upper_of_not_last
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
        (members j).card * (2 * dyadicClassDepth g jg) :=
    Finset.sum_le_card_nsmul
      (members j) size (2 * dyadicClassDepth g jg)
      (by
        intro c hc
        exact hupper c hc)
  have htwice :
      2 * (2 * N * L) ≤
        2 * (dyadicClassDepth g jg * (members j).card) := by
    calc
      2 * (2 * N * L) = 4 * N * L := by ring
      _ ≤ classMass j := hclassMass
      _ ≤ (members j).card *
          (2 * dyadicClassDepth g jg) := hmassUpper
      _ = 2 *
          (dyadicClassDepth g jg * (members j).card) := by
        ring
  have hcount :
      2 * N * L ≤
        dyadicClassDepth g jg * (members j).card :=
    Nat.le_of_mul_le_mul_left htwice (by omega)
  exact
    { j := jg
      members := members j
      mass := by simpa [classMass] using hclassMass
      lower := hlower
      upper := hupper
      strict_upper_of_not_last := by
        intro c hc hnotLast
        exact hstrict c hc (by simpa [K] using hnotLast)
      count_mass := hcount }

end Exponent7
end SimpleGraph

end Lax17Proofs
