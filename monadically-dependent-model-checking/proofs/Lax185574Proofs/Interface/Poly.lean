import Lax185574Proofs.Interface.Computes
import Lax185574.TypeTrees

/-!
Polynomial running times in the two notions of computing.

The algorithmic statements of this submission have the form "there is an
algorithm `A` such that for all parameters there are `c` and `a` such
that for all inputs `x`, `A` computes `y` from `x` in time `O(T)`",
where `T` is a polynomial in sizes of encodings, written with
`Lax185574.Algorithms.Algorithm.Computes`. Their proofs were written for
the older notion `Lax185574.Computing.Computes`, with a time function of
the input length. This module specialises the two bridges
`computes_of_old` and `old_of_computes` to time bounds that are natural
numbers, and to the common shape `c · (m + 1)^a`.

From the old notion to the new one the exponent and the constant stay,
or the constant grows by a factor that absorbs the difference of the
time bounds. From the new notion to the old one the exponent of the
word length doubles, and the time `c · T + c` is absorbed into `c · T'`
for an old time bound `T' ≥ 2 · T`. For the shape `(m + 1)^a` the degree
grows by one, since `(m + 1)^(a+1) ≥ 2 · (m + 1)^a` for `m ≥ 1`.
-/

namespace Lax185574Proofs.Interface

open Lax808846.Ram Lax185574.Encoding Lax185574.Computing Lax185574.Algorithms

universe u v

variable {α : Type u} {β : Type v} [Encode α] [Encode β]

/-- The new notion is monotone in the constant and in the time bound. -/
theorem computes_mono {A : Algorithm} {c c' : ℕ} {a : α} {b : β} {T T' : ℝ}
    (hc : c ≤ c') (hT : T ≤ T') (h0 : 0 ≤ T) (h : A.Computes c a b T) :
    A.Computes c' a b T' := by
  intro w hw
  obtain ⟨hs, ht⟩ := h w (le_trans (Nat.mul_le_mul_right _ hc) hw)
  have hcc : (c : ℝ) ≤ c' := by exact_mod_cast hc
  have hle : (c : ℝ) * T + c ≤ c' * T' + c' := by
    have : (c : ℝ) * T ≤ c' * T' :=
      mul_le_mul hcc hT h0 (by positivity)
    linarith
  refine ⟨hs, fun hTw => ?_⟩
  obtain ⟨t, htle, hrun⟩ := ht (hle.trans hTw)
  exact ⟨t, htle.trans hle, hrun⟩

/-- The old notion gives the new one for a time bound `T₀ : ℕ`, with a
constant `c' ≥ c` such that `c' · T₀ + c'` bounds the old time. -/
theorem computes_of_old_nat {p : Program} {e c c' : ℕ} {a : α} {b : β} {T' : ℕ → ℕ}
    (T₀ : ℕ) {T : ℝ} (hTT : (T₀ : ℝ) = T) (hc : c ≤ c')
    (hT : T' (wordLength a) ≤ c' * T₀ + c') (h : Computes p e c a b T') :
    (⟨p, e⟩ : Algorithm).Computes c' a b T := by
  refine computes_of_old hc ?_ h
  rw [← hTT]
  exact_mod_cast hT

/-- The new notion gives the old one for a time bound `T₀ : ℕ`, with the
exponent doubled, for a nonempty input and an old time bound that
dominates `c · T₀ + c`. -/
theorem old_of_computes_nat {A : Algorithm} {c : ℕ} {a : α} {b : β} {T : ℝ} (T₀ : ℕ)
    {T' : ℕ → ℕ} (hTT : T = T₀) (hne : encode a ≠ []) (hT : c * T₀ + c ≤ T' (wordLength a))
    (h : A.Computes c a b T) : Computes A.program (2 * A.wordExponent) c a b T' := by
  refine old_of_computes hne ?_ h
  rw [hTT]
  exact_mod_cast hT

/-- `c · X + c ≤ c · Y` once `1 ≤ X` and `2 · X ≤ Y`. -/
theorem mul_add_le_mul {c X Y : ℕ} (hX : 1 ≤ X) (hY : 2 * X ≤ Y) : c * X + c ≤ c * Y := by
  have : c * X + c ≤ c * (2 * X) := by nlinarith
  exact this.trans (Nat.mul_le_mul_left c hY)

/-- `2 · (N + 1)^a ≤ (N + 1)^(a + 1)` for `N ≥ 1`. -/
theorem two_mul_pow_le {N : ℕ} (a : ℕ) (hN : 1 ≤ N) : 2 * (N + 1) ^ a ≤ (N + 1) ^ (a + 1) := by
  rw [pow_succ, mul_comm]
  exact Nat.mul_le_mul_left _ (by omega)

/-- `c · (N + 1)^a + c ≤ c · (N + 1)^(a + 1)` for `N ≥ 1`. -/
theorem mul_pow_add_le {c N : ℕ} (a : ℕ) (hN : 1 ≤ N) :
    c * (N + 1) ^ a + c ≤ c * (N + 1) ^ (a + 1) :=
  mul_add_le_mul (Nat.one_le_pow _ _ (by omega)) (two_mul_pow_le a hN)

/-- `(M + d + 1)^a ≤ (d + 1)^a · (M + 1)^a`: an additive term of the
size moves into the constant. -/
theorem add_succ_pow_le (M d a : ℕ) : (M + d + 1) ^ a ≤ (d + 1) ^ a * (M + 1) ^ a := by
  rw [← mul_pow]
  exact Nat.pow_le_pow_left (by nlinarith) a

/-- The old polynomial time `c · (m + 1)^a` in the input length `m`
gives the new time `(N + 1)^a` for `N` the input length, written as a
real number, with the same constant. -/
theorem computes_of_poly {p : Program} {e c a : ℕ} {x : α} {y : β} {N : ℝ}
    (hN : ((encode x).length : ℝ) = N) (h : Computes p e c x y (fun m => c * (m + 1) ^ a)) :
    (⟨p, e⟩ : Algorithm).Computes c x y ((N + 1) ^ a) :=
  computes_of_old_nat (((encode x).length + 1) ^ a) (by rw [← hN]; push_cast; rfl) le_rfl
    (Nat.le_add_right _ _) h

/-- The new time `(N + 1)^a`, where `N` is the input length, gives the
old polynomial time with the degree increased by one. -/
theorem poly_of_computes {A : Algorithm} {c a : ℕ} {x : α} {y : β} {N : ℝ}
    (hN : ((encode x).length : ℝ) = N) (hne : encode x ≠ [])
    (h : A.Computes c x y ((N + 1) ^ a)) :
    Computes A.program (2 * A.wordExponent) c x y (fun m => c * (m + 1) ^ (a + 1)) :=
  old_of_computes_nat (((encode x).length + 1) ^ a) (by rw [← hN]; push_cast; rfl) hne
    (mul_pow_add_le a (List.length_pos_iff.mpr hne)) h

/-! ## Finite sets and lengths of encodings -/

/-- The finite set of the entries of a list. -/
theorem finsetOf_list {γ : Type*} [DecidableEq γ] (l : List γ) :
    Lax185574.TypeTrees.finsetOf {x | x ∈ l} = l.toFinset := by
  unfold Lax185574.TypeTrees.finsetOf
  rw [dif_pos (List.finite_toSet l)]
  ext x
  simp

theorem length_encode_prod (a : α) (b : β) :
    (encode (a, b)).length = (encode a).length + (encode b).length :=
  List.length_append

theorem encode_prod_ne_nil {a : α} (b : β) (h : encode a ≠ []) : encode (a, b) ≠ [] := by
  show encode a ++ encode b ≠ []
  simp [h]

theorem encode_list_ne_nil {γ : Type*} [Encode γ] (l : List γ) : encode l ≠ [] :=
  List.cons_ne_nil _ _

theorem encode_partialGraph_ne_nil {n : ℕ} (G : Lax185574.PartialGraphs.PartialGraph (Fin n)) :
    encode G ≠ [] :=
  encode_prod_ne_nil (a := G.color) _ (encode_list_ne_nil (List.ofFn G.color))

theorem encode_typeTree_ne_nil (τ : Lax185574.TypeTrees.TypeTree) : encode τ ≠ [] := by
  show encode (τ.k, τ.q, τ.ℓ) ++ encode τ.root ≠ []
  simp [show encode (τ.k, τ.q, τ.ℓ) = [τ.k, τ.q, τ.ℓ] from rfl]

theorem one_le_length_encode_typeTree (τ : Lax185574.TypeTrees.TypeTree) :
    1 ≤ (encode τ).length :=
  List.length_pos_iff.mpr (encode_typeTree_ne_nil τ)

theorem length_encode_list_fin {ℓ : ℕ} (J : List (Fin ℓ)) :
    (encode J).length = J.length + 1 := by
  have h : (fun i : Fin ℓ => (encode i).length) = fun _ => 1 := funext fun _ => rfl
  show (J.length :: (J.map encode).flatten).length = _
  simp [List.length_flatten, Function.comp_def, h]

end Lax185574Proofs.Interface
