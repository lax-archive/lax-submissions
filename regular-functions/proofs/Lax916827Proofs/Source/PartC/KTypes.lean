/-
`k`-types of strings (Definition `def:k-types` of *Transducers*, M. Bojańczyk) and
their combinatorial properties (Lemma `lem:k-types-properties`): refinement, congruence and
aperiodicity.

The definitions live in this file so that the proofs can be developed before the
statements of Section *Logic* in `RequestProject/PartC/MSO.lean`.

The three properties are proved by induction on `k`, with no reference to
logic.  For aperiodicity the bound `tpBound k` is used: two powers `uⁿ` and `uᵐ`
have the same `k`-type as soon as both exponents are at least `tpBound k`.
-/
import Lax765601Proofs.Source.Common.Basic
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-! ## `k`-types -/

/-- The type of `k`-types over the alphabet `A`. -/
def TpType (A : Type) : ℕ → Type
  | 0 => Unit
  | k + 1 => Set (TpType A k × A × TpType A k)

/-- **Definition `def:k-types` (k-types).**  `tp k w` is the `k`-type of the string
`w`:  `tp 0 w = ∅` and
`tp (k+1) w = {(tp k w₁, a, tp k w₂) | w = w₁ a w₂}`. -/
def tp {A : Type} : (k : ℕ) → List A → TpType A k
  | 0, _ => ()
  | k + 1, w =>
      {t : TpType A k × A × TpType A k |
        ∃ (w₁ : List A) (a : A) (w₂ : List A), w = w₁ ++ a :: w₂ ∧ t = (tp k w₁, a, tp k w₂)}

variable {A : Type}

/-- The `(k+1)`-type of a string, viewed as a set of triples. -/
def tpSet (k : ℕ) (w : List A) : Set (TpType A k × A × TpType A k) := tp (k + 1) w

lemma tp_succ_eq_iff_tpSet (k : ℕ) (w v : List A) :
    tp (k + 1) w = tp (k + 1) v ↔ tpSet k w = tpSet k v := Iff.rfl

lemma mem_tpSet (k : ℕ) (w : List A) (t : TpType A k × A × TpType A k) :
    t ∈ tpSet k w ↔ ∃ (w₁ : List A) (a : A) (w₂ : List A),
      w = w₁ ++ a :: w₂ ∧ t = (tp k w₁, a, tp k w₂) := Iff.rfl

lemma mem_tpSet_of (k : ℕ) (w₁ : List A) (a : A) (w₂ : List A) :
    (tp k w₁, a, tp k w₂) ∈ tpSet k (w₁ ++ a :: w₂) := ⟨w₁, a, w₂, rfl, rfl⟩

lemma tp_zero (w v : List A) : tp 0 w = tp 0 v := rfl

/-! ## Refinement -/

/-- The `(k+1)`-type of a string determines its `k`-type. -/
lemma tp_refine : ∀ (k : ℕ) (w v : List A), tp (k + 1) w = tp (k + 1) v → tp k w = tp k v := by
  intro k
  induction k with
  | zero => intro w v _; rfl
  | succ k ih =>
      have hsub : ∀ (x y : List A), tp (k + 2) x = tp (k + 2) y → tpSet k x ⊆ tpSet k y := by
        intro x y hxy t ht
        obtain ⟨x₁, a, x₂, hx, rfl⟩ := ht
        have h1 : (tp (k + 1) x₁, a, tp (k + 1) x₂) ∈ tpSet (k + 1) x := by
          rw [hx]; exact mem_tpSet_of (k + 1) x₁ a x₂
        rw [(tp_succ_eq_iff_tpSet (k + 1) x y).mp hxy] at h1
        obtain ⟨y₁, b, y₂, hy, heq⟩ := h1
        simp only [Prod.mk.injEq] at heq
        obtain ⟨e1, e2, e3⟩ := heq
        subst e2
        refine ⟨y₁, a, y₂, hy, ?_⟩
        rw [ih x₁ y₁ e1, ih x₂ y₂ e3]
      intro w v h
      rw [tp_succ_eq_iff_tpSet]
      exact Set.Subset.antisymm (hsub w v h) (hsub v w h.symm)

/-! ## Congruence -/

/-- `k`-types are compatible with concatenation. -/
lemma tp_congr : ∀ (k : ℕ) (w w' v v' : List A),
    tp k w = tp k w' → tp k v = tp k v' → tp k (w ++ v) = tp k (w' ++ v') := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _; rfl
  | succ k ih =>
      have key : ∀ (w w' v v' : List A), tp (k + 1) w = tp (k + 1) w' →
          tp (k + 1) v = tp (k + 1) v' → tpSet k (w ++ v) ⊆ tpSet k (w' ++ v') := by
        intro w w' v v' hw hv t ht
        obtain ⟨x, a, y, hxy, rfl⟩ := ht
        have hwk : tp k w = tp k w' := tp_refine k w w' hw
        have hvk : tp k v = tp k v' := tp_refine k v v' hv
        rcases List.append_eq_append_iff.mp hxy with ⟨z, hz1, hz2⟩ | ⟨z, hz1, hz2⟩
        · -- the marked position lies in `v`
          have h1 : (tp k z, a, tp k y) ∈ tpSet k v := by
            rw [hz2]; exact mem_tpSet_of k z a y
          rw [(tp_succ_eq_iff_tpSet k v v').mp hv] at h1
          obtain ⟨z', b, y', hv', heq⟩ := h1
          simp only [Prod.mk.injEq] at heq
          obtain ⟨e1, e2, e3⟩ := heq
          subst e2
          refine ⟨w' ++ z', a, y', by rw [hv']; simp, ?_⟩
          have : tp k x = tp k (w' ++ z') := by
            rw [hz1]; exact ih w w' z z' hwk e1
          rw [this, e3]
        · -- the marked position lies in `w`, or `w` is a prefix of `x`
          cases z with
          | nil =>
              have hwx : w = x := by simpa using hz1
              have hv2 : v = a :: y := by simpa using hz2.symm
              have h1 : (tp k ([] : List A), a, tp k y) ∈ tpSet k v := by
                rw [hv2]; exact mem_tpSet_of k [] a y
              rw [(tp_succ_eq_iff_tpSet k v v').mp hv] at h1
              obtain ⟨z', b, y', hv', heq⟩ := h1
              simp only [Prod.mk.injEq] at heq
              obtain ⟨e1, e2, e3⟩ := heq
              subst e2
              refine ⟨w' ++ z', a, y', by rw [hv']; simp, ?_⟩
              have : tp k x = tp k (w' ++ z') := by
                have h2 := ih w w' [] z' hwk e1
                simpa [← hwx] using h2
              rw [this, e3]
          | cons c z' =>
              have hac : c = a ∧ y = z' ++ v := by
                have hz2' := hz2
                simp only [List.cons_append, List.cons.injEq] at hz2'
                exact ⟨hz2'.1.symm, hz2'.2⟩
              obtain ⟨hca, hy⟩ := hac
              rw [hca] at hz1
              have h1 : (tp k x, a, tp k z') ∈ tpSet k w := by
                rw [hz1]; exact mem_tpSet_of k x a z'
              rw [(tp_succ_eq_iff_tpSet k w w').mp hw] at h1
              obtain ⟨x', b, z'', hw', heq⟩ := h1
              simp only [Prod.mk.injEq] at heq
              obtain ⟨e1, e2, e3⟩ := heq
              subst e2
              refine ⟨x', a, z'' ++ v', by rw [hw']; simp, ?_⟩
              have : tp k y = tp k (z'' ++ v') := by
                rw [hy]; exact ih z' z'' v v' e3 hvk
              rw [this, e1]
      intro w w' v v' hw hv
      rw [tp_succ_eq_iff_tpSet]
      exact Set.Subset.antisymm (key w w' v v' hw hv) (key w' w v' v hw.symm hv.symm)

/-! ## Aperiodicity -/

/-- Decomposing a power of a string at a marked position. -/
lemma npow_eq_append_cons {u : List A} : ∀ (n : ℕ) {x : List A} {a : A} {y : List A},
    npow u n = x ++ a :: y →
    ∃ (i j : ℕ) (p s : List A), u = p ++ a :: s ∧ i + j + 1 = n ∧
      x = npow u i ++ p ∧ y = s ++ npow u j := by
  intro n
  induction n with
  | zero => intro x a y h; simp [npow] at h
  | succ n ih =>
      intro x a y h
      rw [npow_succ] at h
      rcases List.append_eq_append_iff.mp h with ⟨z, hz1, hz2⟩ | ⟨z, hz1, hz2⟩
      · obtain ⟨i, j, p, s, hu, hsum, hx, hy⟩ := ih hz2
        refine ⟨i + 1, j, p, s, hu, by omega, ?_, hy⟩
        rw [hz1, hx, npow_succ, List.append_assoc]
      · cases z with
        | nil =>
            have hux : u = x := by simpa using hz1
            have hy : a :: y = npow u n := by simpa using hz2
            cases n with
            | zero => simp [npow] at hy
            | succ m =>
                have hune : u ≠ [] := by
                  intro h0
                  rw [h0] at hy
                  simp at hy
                have hnp : a :: y = u ++ npow u m := by rw [hy, npow_succ]
                obtain ⟨x', hx'⟩ : ∃ x' : List A, u = a :: x' := by
                  cases u with
                  | nil => exact absurd rfl hune
                  | cons c x' =>
                      refine ⟨x', ?_⟩
                      simp only [List.cons_append, List.cons.injEq] at hnp
                      rw [hnp.1]
                have hyy : y = x' ++ npow u m := by
                  have h2 : a :: y = a :: (x' ++ npow u m) := by
                    rw [hnp]
                    nth_rewrite 1 [hx']
                    simp
                  simpa using h2
                refine ⟨1, m, [], x', by simpa using hx', by omega, ?_, hyy⟩
                rw [← hux]
                simp [npow]
        | cons c z' =>
            have hcz : c = a ∧ y = z' ++ npow u n := by
              simp only [List.cons_append, List.cons.injEq] at hz2
              exact ⟨hz2.1.symm, hz2.2⟩
            obtain ⟨rfl, hy⟩ := hcz
            exact ⟨0, n, x, z', hz1, by omega, by simp [npow], hy⟩

/-- Recomposing a power of a string at a marked position. -/
lemma npow_decomp_eq {u p s : List A} {a : A} (h : u = p ++ a :: s) (i j : ℕ) :
    npow u (i + j + 1) = (npow u i ++ p) ++ a :: (s ++ npow u j) := by
  have hsum : i + j + 1 = i + (j + 1) := by omega
  rw [hsum, npow_add, npow_succ]
  nth_rewrite 2 [h]
  simp

/-- The bound after which the `k`-type of a power no longer changes. -/
def tpBound : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * tpBound k + 2

/-- All sufficiently large powers of a string have the same `k`-type. -/
lemma tp_npow_eq : ∀ (k : ℕ) (u : List A) (m n : ℕ),
    tpBound k ≤ m → tpBound k ≤ n → tp k (npow u m) = tp k (npow u n) := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _; rfl
  | succ k ih =>
      have key : ∀ (u : List A) (m n : ℕ), tpBound (k + 1) ≤ m → tpBound (k + 1) ≤ n →
          tpSet k (npow u m) ⊆ tpSet k (npow u n) := by
        intro u m n hm hn t ht
        obtain ⟨x, a, y, hx, rfl⟩ := ht
        obtain ⟨i, j, p, s, hu, hsum, hxi, hyj⟩ := npow_eq_append_cons m hx
        have hbound : tpBound (k + 1) = 2 * tpBound k + 2 := rfl
        rw [hbound] at hm hn
        -- choose new exponents with the same `k`-types
        obtain ⟨i', j', hsum', hi, hj⟩ : ∃ i' j' : ℕ, i' + j' + 1 = n ∧
            tp k (npow u i) = tp k (npow u i') ∧ tp k (npow u j) = tp k (npow u j') := by
          by_cases hi : tpBound k ≤ i
          · by_cases hj : tpBound k ≤ j
            · refine ⟨tpBound k, n - 1 - tpBound k, by omega, ih u i (tpBound k) hi le_rfl, ?_⟩
              exact ih u j (n - 1 - tpBound k) hj (by omega)
            · refine ⟨n - 1 - j, j, by omega, ?_, rfl⟩
              exact ih u i (n - 1 - j) hi (by omega)
          · refine ⟨i, n - 1 - i, by omega, rfl, ?_⟩
            exact ih u j (n - 1 - i) (by omega) (by omega)
        refine ⟨npow u i' ++ p, a, s ++ npow u j', ?_, ?_⟩
        · rw [← hsum']
          exact npow_decomp_eq hu i' j'
        · have h1 : tp k x = tp k (npow u i' ++ p) := by
            rw [hxi]; exact tp_congr k (npow u i) (npow u i') p p hi rfl
          have h2 : tp k y = tp k (s ++ npow u j') := by
            rw [hyj]; exact tp_congr k s s (npow u j) (npow u j') rfl hj
          rw [h1, h2]
      intro u m n hm hn
      rw [tp_succ_eq_iff_tpSet]
      exact Set.Subset.antisymm (key u m n hm hn) (key u n m hn hm)

/-- **Lemma `lem:k-types-properties`.**  Refinement, congruence and aperiodicity of `k`-types. -/
theorem tp_properties_aux (k : ℕ) :
    (∀ w v : List A, tp (k + 1) w = tp (k + 1) v → tp k w = tp k v) ∧
    (∀ w w' v v' : List A, tp k w = tp k w' → tp k v = tp k v' →
      tp k (w ++ v) = tp k (w' ++ v')) ∧
    (∀ w : List A, ∃ N : ℕ, ∀ n ≥ N, tp k (npow w n) = tp k (npow w N)) :=
  ⟨tp_refine k, tp_congr k,
    fun w => ⟨tpBound k, fun n hn => tp_npow_eq k w n (tpBound k) hn le_rfl⟩⟩

end Lax916827Proofs.Transducers
