import Lax185574.BipartiteHomogeneity
import Lax185574Proofs.Lib.TupleRamsey
import Mathlib.Order.Interval.Finset.Fin

namespace Lax185574Proofs.BipartiteHomogeneity

open Lax185574.BipartiteHomogeneity
open Lax185574Proofs.Lib.TupleRamsey (otp tupleRamseyAtSize)

/-- On `I^ℓ × J^ℓ` the color of a pair of tuples depends only on the
order types of the two tuples. -/
def Homogeneous {k ℓ t : ℕ} (c : (Fin ℓ → Fin t) → (Fin ℓ → Fin t) → Fin k)
    (I J : Finset (Fin t)) : Prop :=
  ∀ a a' b b' : Fin ℓ → Fin t,
    (∀ i, a i ∈ I) → (∀ i, a' i ∈ I) → (∀ i, b i ∈ J) → (∀ i, b' i ∈ J) →
    orderType a = orderType a' → orderType b = orderType b' →
    c a b = c a' b'

theorem Homogeneous.mono {k ℓ t : ℕ} {c : (Fin ℓ → Fin t) → (Fin ℓ → Fin t) → Fin k}
    {I J I' J' : Finset (Fin t)} (h : Homogeneous c I J) (hI : I' ⊆ I) (hJ : J' ⊆ J) :
    Homogeneous c I' J' :=
  fun a a' b b' ha ha' hb hb' => h a a' b b' (fun i => hI (ha i)) (fun i => hI (ha' i))
    (fun i => hJ (hb i)) (fun i => hJ (hb' i))

/-- Every coloring on `[n]` has homogeneous sets `I`, `J` with at least
`m` elements each. -/
def Good (k ℓ m n : ℕ) : Prop :=
  ∀ c : (Fin ℓ → Fin n) → (Fin ℓ → Fin n) → Fin k,
    ∃ I J : Finset (Fin n), m ≤ I.card ∧ m ≤ J.card ∧ Homogeneous c I J

theorem good_zero (k ℓ n : ℕ) : Good k ℓ 0 n := by
  intro c
  refine ⟨∅, ∅, le_rfl, le_rfl, ?_⟩
  intro a a' b b' ha _ _ _ _ _
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · rw [Subsingleton.elim a a', Subsingleton.elim b b']
  · exact absurd (ha ⟨0, hℓ⟩) (Finset.notMem_empty _)

/-- Equal order types in the curried form of the statement give equal
order types in the form of the Ramsey core. -/
theorem otp_eq_of_orderType_eq {ℓ t : ℕ} {a b : Fin ℓ → Fin t}
    (h : orderType a = orderType b) : otp a = otp b := by
  funext p
  exact congrFun (congrFun h p.1) p.2

/-- The Ramsey step: for every `m` all large enough `n` are good. -/
theorem eventually_good (k ℓ m : ℕ) : ∃ N : ℕ, ∀ n, N ≤ n → Good k ℓ m n := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, fun n hn c => ?_⟩
    exact (c (fun _ => ⟨0, hn⟩) (fun _ => ⟨0, hn⟩)).elim0
  obtain ⟨N, hN⟩ := tupleRamseyAtSize k (ℓ + ℓ) (m + m) hk
  refine ⟨N, fun n hn c => ?_⟩
  let d : (Fin (ℓ + ℓ) → Fin n) → Fin k := fun w =>
    c (fun i => w (Fin.castAdd ℓ i)) (fun i => w (Fin.natAdd ℓ i))
  obtain ⟨H, -, hHcard, f, hf⟩ :=
    hN (Finset.univ : Finset (Fin n)) (by simpa using hn) d
  let e : Fin H.card ↪o Fin n := H.orderEmbOfFin rfl
  let g : Fin (m + m) → Fin n := fun i => e (Fin.castLE hHcard i)
  have hg : StrictMono g := fun i j hij => e.strictMono (by rw [Fin.lt_def] at hij ⊢; simpa using hij)
  have hgH : ∀ i, g i ∈ H := fun i => H.orderEmbOfFin_mem rfl _
  let I : Finset (Fin n) := Finset.univ.image fun i : Fin m => g (Fin.castAdd m i)
  let J : Finset (Fin n) := Finset.univ.image fun i : Fin m => g (Fin.natAdd m i)
  have hIcard : I.card = m := by
    exact (Finset.card_image_of_injective _
      (hg.injective.comp (Fin.castAdd_injective m m))).trans (by simp)
  have hJcard : J.card = m := by
    exact (Finset.card_image_of_injective _
      (hg.injective.comp (Fin.natAdd_injective m m))).trans (by simp)
  have hIH : ∀ x ∈ I, x ∈ H := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hgH _
  have hJH : ∀ x ∈ J, x ∈ H := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hgH _
  have hIJ : ∀ x ∈ I, ∀ y ∈ J, x < y := by
    intro x hx y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    apply hg
    rw [Fin.lt_def]
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    omega
  refine ⟨I, J, hIcard.ge, hJcard.ge, ?_⟩
  intro a a' b b' ha ha' hb hb' hab hbb
  have key : ∀ (x y : Fin ℓ → Fin n), (∀ i, x i ∈ I) → (∀ i, y i ∈ J) →
      c x y = f (otp (Fin.append x y)) := by
    intro x y hx hy
    have hmem : ∀ i, Fin.append x y i ∈ H := by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hIH _ (hx j)
      · rw [Fin.append_right]; exact hJH _ (hy j)
    have hd : d (Fin.append x y) = c x y := by
      simp only [d, Fin.append_left, Fin.append_right]
    rw [← hd]
    exact hf _ hmem
  rw [key a b ha hb, key a' b' ha' hb']
  congr 1
  funext p
  obtain ⟨p, q⟩ := p
  have hA := otp_eq_of_orderType_eq hab
  have hB := otp_eq_of_orderType_eq hbb
  show compare (Fin.append a b p) (Fin.append a b q) =
    compare (Fin.append a' b' p) (Fin.append a' b' q)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) p <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) q <;>
    simp only [Fin.append_left, Fin.append_right]
  · exact congrFun hA (i, j)
  · rw [compare_lt_iff_lt.mpr (hIJ _ (ha i) _ (hb j)),
      compare_lt_iff_lt.mpr (hIJ _ (ha' i) _ (hb' j))]
  · rw [compare_gt_iff_gt.mpr (hIJ _ (ha j) _ (hb i)),
      compare_gt_iff_gt.mpr (hIJ _ (ha' j) _ (hb' i))]
  · exact congrFun hB (i, j)

/-- The size function: the largest `m ≤ t` such that every `n ≥ t` is
good for `m`. -/
noncomputable def sizeFun (k ℓ : ℕ) (t : ℕ) : ℕ :=
  open Classical in Nat.findGreatest (fun m => ∀ n, t ≤ n → Good k ℓ m n) t

theorem sizeFun_spec (k ℓ t : ℕ) : ∀ n, t ≤ n → Good k ℓ (sizeFun k ℓ t) n := by
  classical
  have h0 : ∀ n, t ≤ n → Good k ℓ 0 n := fun n _ => good_zero k ℓ n
  exact Nat.findGreatest_spec (P := fun m => ∀ n, t ≤ n → Good k ℓ m n)
    (Nat.zero_le t) h0

/--
---
conclusion: Lax185574.BipartiteHomogeneity.exists_orderType_homogeneous
---
Concatenate the two tuples to one tuple of length `2ℓ` and apply the
Erdős–Rado theorem for order types of tuples to the induced coloring.
This gives a set `H` of size `2m` on which the color depends only on the
order type of the concatenation. Split `H` into its `m` smallest
elements `I` and its `m` largest elements `J`. Every entry from `I` lies
below every entry from `J`, so for `a ∈ I^ℓ` and `b ∈ J^ℓ` the order
type of the concatenation is determined by the order types of `a` and
`b`. The function `U(t)` is the largest `m ≤ t` such that every `n ≥ t`
admits such sets of size `m` for every coloring. It is non-decreasing by
definition and unbounded by the Ramsey step.

The Ramsey core is adapted from lax-345067 (finite Ramsey theorems for
pairs and tuples).
-/
theorem exists_orderType_homogeneous (k ℓ : ℕ) :
    ∃ U : ℕ → ℕ, Monotone U ∧ (∀ m : ℕ, ∃ t : ℕ, m ≤ U t) ∧
      ∀ (t : ℕ) (c : (Fin ℓ → Fin t) → (Fin ℓ → Fin t) → Fin k),
        ∃ I J : Finset (Fin t), I.card = U t ∧ J.card = U t ∧
          ∀ a a' b b' : Fin ℓ → Fin t,
            (∀ i, a i ∈ I) → (∀ i, a' i ∈ I) → (∀ i, b i ∈ J) → (∀ i, b' i ∈ J) →
            orderType a = orderType a' → orderType b = orderType b' →
            c a b = c a' b' := by
  classical
  refine ⟨sizeFun k ℓ, ?_, ?_, ?_⟩
  · refine monotone_nat_of_le_succ fun t => ?_
    apply Nat.le_findGreatest
    · exact (Nat.findGreatest_le t).trans (Nat.le_succ t)
    · exact fun n hn => sizeFun_spec k ℓ t n ((Nat.le_succ t).trans hn)
  · intro m
    obtain ⟨N, hN⟩ := eventually_good k ℓ m
    refine ⟨max N m, Nat.le_findGreatest (le_max_right N m) fun n hn => ?_⟩
    exact hN n ((le_max_left N m).trans hn)
  · intro t c
    obtain ⟨I, J, hI, hJ, hc⟩ := sizeFun_spec k ℓ t t le_rfl c
    obtain ⟨I', hI'I, hI'⟩ := Finset.exists_subset_card_eq hI
    obtain ⟨J', hJ'J, hJ'⟩ := Finset.exists_subset_card_eq hJ
    exact ⟨I', J', hI', hJ', hc.mono hI'I hJ'J⟩

end Lax185574Proofs.BipartiteHomogeneity
