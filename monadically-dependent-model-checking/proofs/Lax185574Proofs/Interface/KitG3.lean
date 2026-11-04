import Lax185574Proofs.Interface.Computes
import Lax185574Proofs.Interface.Encode
import Lax185574Proofs.Interface.MDBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Small facts for moving the algorithmic statements of Part II between
`Lax185574.Algorithms.Algorithm.Computes` and the older
`Lax185574.Computing.Computes`.

Both notions depend on the input and the output only through their
encodings (`computes_congr`, `oldComputes_congr`). The older one is
monotone in the constant and in the time bound (`oldComputes_mono`). A
graph and a simple graph on `Fin n` are encoded alike, also inside pairs
and triples. A time bound `⌊c · (n+1)^x⌋` of the older statements is at
most `c' · n^x + c'` for `c' = ⌈c · 2^x⌉`, and `c · n^x + c` is at most
`⌊3c · (n+1)^x⌋`.
-/

namespace Lax185574Proofs.Interface.KitG3

open Lax808846.Ram Lax808846.RamComputes
open Lax185574.Encoding Lax185574.Algorithms Lax185574.Graphs

universe u u' v v'

/-! ## Graphs -/

/-- A simple graph on `Fin n` as a graph on `n` vertices. -/
def toGraph {n : ℕ} (H : SimpleGraph (Fin n)) : Graph :=
  ⟨n, H.Adj, fun _ _ h => H.adj_symm h, fun _ => H.irrefl⟩

@[simp]
theorem toGraph_n {n : ℕ} (H : SimpleGraph (Fin n)) : (toGraph H).n = n := rfl

@[simp]
theorem toSimpleGraph_toGraph {n : ℕ} (H : SimpleGraph (Fin n)) :
    (toGraph H).toSimpleGraph = H := rfl

/-! ## Encodings -/

theorem encode_pair {α : Type u} {β : Type v} [Encode α] [Encode β] (a : α) (b : β) :
    encode (a, b) = encode a ++ encode b := rfl

/-- A graph paired with a value is encoded as its simple graph paired
with the value. -/
theorem encode_graph_pair {β : Type v} [Encode β] (G : Graph) (b : β) :
    encode (G, b) = encode (G.toSimpleGraph, b) := by
  rw [encode_pair, encode_pair, encode_graph]

/-- The same for a graph at the end of a triple. -/
theorem encode_triple_graph {α : Type u} {β : Type v} [Encode α] [Encode β]
    (a : α) (b : β) (G : Graph) :
    encode (a, b, G) = encode (a, b, G.toSimpleGraph) := by
  rw [encode_pair, encode_pair, encode_pair, encode_pair, encode_graph]

theorem encode_pair_list_ne_nil {α : Type u} {β : Type v} [Encode α] [Encode β]
    (a : α) (l : List β) : encode (a, l) ≠ [] := by
  rw [encode_pair, encode_list]
  simp

theorem encode_nat_pair_ne_nil {β : Type v} [Encode β] (r : ℕ) (b : β) :
    encode (r, b) ≠ [] := by
  rw [encode_pair]
  simp [encode]

/-! ## The two notions -/

section Congr

variable {α : Type u} {α' : Type u'} {β : Type v} {β' : Type v'}
  [Encode α] [Encode α'] [Encode β] [Encode β']

/-- `Algorithm.Computes` depends on the input and the output only through
their encodings. -/
theorem computes_congr {A : Algorithm} {c : ℕ} {a : α} {a' : α'} {b : β} {b' : β'} {T : ℝ}
    (ha : encode a = encode a') (hb : encode b = encode b') (h : A.Computes c a b T) :
    A.Computes c a' b' T := by
  unfold Algorithm.Computes at *
  rw [← ha, ← hb]
  exact h

/-- The older notion depends on the input and the output only through
their encodings. -/
theorem oldComputes_congr {p : Program} {e c : ℕ} {a : α} {a' : α'} {b : β} {b' : β'}
    {T : ℕ → ℕ} (ha : encode a = encode a') (hb : encode b = encode b')
    (h : Lax185574.Computing.Computes p e c a b T) :
    Lax185574.Computing.Computes p e c a' b' T := by
  unfold Lax185574.Computing.Computes wordLength at *
  rw [← ha, ← hb]
  exact h

end Congr

/-- The older notion is monotone in the constant and in the time
bound. -/
theorem oldComputes_mono {α : Type u} {β : Type v} [Encode α] [Encode β] {p : Program}
    {e c c' : ℕ} {a : α} {b : β} {T T' : ℕ → ℕ} (hc : c ≤ c') (hT : ∀ m, T m ≤ T' m)
    (h : Lax185574.Computing.Computes p e c a b T) :
    Lax185574.Computing.Computes p e c' a b T' := by
  intro w hadm
  obtain ⟨hs, ht⟩ := h w fun v hv => le_trans (Nat.mul_le_mul_right _ hc) (hadm v hv)
  refine ⟨hs, fun hTw x hx => ?_⟩
  obtain ⟨t, htle, hrun⟩ := ht ((hT _).trans hTw) x hx
  exact ⟨t, htle.trans (hT _), hrun⟩

/-! ## Real time bounds -/

theorem one_le_succ_mul_succ_pow (a n k : ℕ) : (1 : ℝ) ≤ ((a : ℝ) + 1) * ((n : ℝ) + 1) ^ k := by
  have h1 : (1 : ℝ) ≤ (a : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) a]
  have h2 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ k := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
  nlinarith

theorem succ_rpow_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ((n : ℝ) + 1) ^ x ≤ 2 ^ x * (n : ℝ) ^ x + 2 ^ x := by
  have h2 : (1 : ℝ) ≤ 2 ^ x := Real.one_le_rpow (by norm_num) hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, zero_add, Real.one_rpow]
    have : (0 : ℝ) ≤ 2 ^ x * (0 : ℝ) ^ x := mul_nonneg (by positivity) (Real.rpow_nonneg le_rfl x)
    linarith
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : ((n : ℝ) + 1) ^ x ≤ (2 * (n : ℝ)) ^ x :=
      Real.rpow_le_rpow (by positivity) (by linarith) hx
    rw [Real.mul_rpow (by norm_num) (by positivity)] at this
    linarith

theorem le_ceil_mul_two_rpow (c : ℕ) {x : ℝ} (hx : 0 ≤ x) : c ≤ ⌈(c : ℝ) * 2 ^ x⌉₊ := by
  have h2 : (1 : ℝ) ≤ 2 ^ x := Real.one_le_rpow (by norm_num) hx
  have : (c : ℝ) ≤ (c : ℝ) * 2 ^ x := le_mul_of_one_le_right (Nat.cast_nonneg c) h2
  exact_mod_cast this.trans (Nat.le_ceil _)

/-- An older time bound `⌊c · (n+1)^x⌋` is at most `c' · n^x + c'` for
`c' = ⌈c · 2^x⌉`. -/
theorem floor_rpow_le (c n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ((⌊(c : ℝ) * ((n : ℝ) + 1) ^ x⌋₊ : ℕ) : ℝ) ≤
      (⌈(c : ℝ) * 2 ^ x⌉₊ : ℝ) * (n : ℝ) ^ x + ⌈(c : ℝ) * 2 ^ x⌉₊ := by
  have h0 : (0 : ℝ) ≤ (c : ℝ) * ((n : ℝ) + 1) ^ x := by positivity
  refine (Nat.floor_le h0).trans ?_
  have hc : (c : ℝ) * 2 ^ x ≤ ⌈(c : ℝ) * 2 ^ x⌉₊ := Nat.le_ceil _
  have hnx : (0 : ℝ) ≤ (n : ℝ) ^ x := Real.rpow_nonneg (Nat.cast_nonneg n) x
  calc (c : ℝ) * ((n : ℝ) + 1) ^ x ≤ (c : ℝ) * (2 ^ x * (n : ℝ) ^ x + 2 ^ x) :=
        mul_le_mul_of_nonneg_left (succ_rpow_le n hx) (Nat.cast_nonneg c)
    _ = (c : ℝ) * 2 ^ x * (n : ℝ) ^ x + (c : ℝ) * 2 ^ x := by ring
    _ ≤ _ := by nlinarith

/-- `c · n^x + c` is at most the older time bound `⌊3c · (n+1)^x⌋`. -/
theorem le_floor_rpow (c n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (c : ℝ) * (n : ℝ) ^ x + c ≤ ((⌊((3 * c : ℕ) : ℝ) * ((n : ℝ) + 1) ^ x⌋₊ : ℕ) : ℝ) := by
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ x :=
    Real.one_le_rpow (by have := Nat.cast_nonneg (α := ℝ) n; linarith) hx
  have h2 : (n : ℝ) ^ x ≤ ((n : ℝ) + 1) ^ x :=
    Real.rpow_le_rpow (Nat.cast_nonneg n) (by linarith) hx
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hfl := Nat.lt_floor_add_one (((3 * c : ℕ) : ℝ) * ((n : ℝ) + 1) ^ x)
  push_cast at hfl ⊢
  nlinarith

end Lax185574Proofs.Interface.KitG3
