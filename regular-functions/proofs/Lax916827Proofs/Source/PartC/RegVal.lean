/-
The numerical value of an output string, and the entry points of the pieces of a
crossing decomposition, for the effective equivalence bound of Theorem
`thm:decidable-equivalence-regular` (`RequestProject/PartC/RegEffBound.lean`).

An output string over a finite alphabet is turned into a rational number by the
base-`K` encoding `Transducers.Iota.iota` of `RequestProject/PartB/Iota.lean`,
with `K` one more than the number of letters.  The encoding is injective and
*additive on the left*:

  `oval (o₁ ++ o₂) = oval o₁ + owt o₁ * oval o₂`,   `owt o = K ^ |o|`,

so the value of a concatenation of finitely many pieces is a sum of products of
the values and the weights of the pieces (`Transducers.RegHankel.oval_flatten`).
That is the identity that turns the crossing decomposition of a run into a
Hankel decomposition of its value.
-/
import Lax916827Proofs.Source.PartC.RegProfile
import Lax132576Proofs.Source.PartB.Iota
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace RegHankel

/-! ## The value of an output string -/

noncomputable section

open Classical

variable {B : Type} [Fintype B]

/-- An injective numbering of the letters of a finite alphabet. -/
noncomputable def encL (b : B) : ℕ := (Fintype.equivFin B b : ℕ)

lemma encL_injective : Function.Injective (encL (B := B)) := by
  intro b b' h
  have : (Fintype.equivFin B b : Fin (Fintype.card B)) = Fintype.equivFin B b' := Fin.ext h
  exact (Fintype.equivFin B).injective this

lemma encL_lt (b : B) : encL b + 1 < Fintype.card B + 1 := by
  have := (Fintype.equivFin B b).isLt
  simp [encL]

/-- The number representing an output string. -/
noncomputable def oval (o : List B) : ℚ :=
  (Iota.iota (Fintype.card B + 1) (o.map encL) : ℚ)

/-- The weight of an output string: the base to the power of its length. -/
noncomputable def owt (o : List B) : ℚ := ((Fintype.card B + 1 : ℕ) : ℚ) ^ o.length

@[simp] lemma oval_nil : oval ([] : List B) = 0 := by simp [oval]

@[simp] lemma owt_nil : owt ([] : List B) = 1 := by simp [owt]

lemma oval_append (o₁ o₂ : List B) : oval (o₁ ++ o₂) = oval o₁ + owt o₁ * oval o₂ := by
  simp only [oval, owt, List.map_append, Iota.iota_append, List.length_map]
  push_cast
  ring

lemma owt_append (o₁ o₂ : List B) : owt (o₁ ++ o₂) = owt o₁ * owt o₂ := by
  simp [owt, pow_add]

/-- The encoding of output strings is injective. -/
lemma oval_injective : Function.Injective (oval (B := B)) := by
  intro o o' h
  have h' : Iota.iota (Fintype.card B + 1) (o.map encL) =
      Iota.iota (Fintype.card B + 1) (o'.map encL) := by
    simp only [oval] at h
    exact_mod_cast h
  have hb : ∀ (l : List B) (x : ℕ), x ∈ l.map encL → x + 1 < Fintype.card B + 1 := by
    intro l x hx
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
    exact encL_lt b
  have := Iota.iota_inj (hb o) (hb o') h'
  exact List.map_injective_iff.2 encL_injective this

/-! ## The value of a concatenation of pieces -/

lemma owt_flatten (F : ℕ → List B) :
    ∀ n : ℕ, owt (((List.range n).map F).flatten) = ∏ i ∈ Finset.range n, owt (F i) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ]
      simp only [List.map_append, List.flatten_append, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_nil, List.append_nil]
      rw [owt_append, ih, Finset.prod_range_succ]

lemma oval_flatten (F : ℕ → List B) :
    ∀ n : ℕ, oval (((List.range n).map F).flatten)
      = ∑ j ∈ Finset.range n, (∏ i ∈ Finset.range j, owt (F i)) * oval (F j) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ]
      simp only [List.map_append, List.flatten_append, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_nil, List.append_nil]
      rw [oval_append, ih, owt_flatten, Finset.sum_range_succ]

end

/-! ## The entry points of the pieces, on the two sides of the cut -/

open RegPos

variable {Q : Type}

/-- The entry point of the `i`-th piece, when it is on the left of the cut. -/
def entryL (init : Q) (n₀ : ℕ) (cs : List Q) (i : ℕ) : ℕ × Q :=
  if i = 0 then (0, init) else (n₀, cs.getD (i - 1) init)

/-- The entry point of the `i`-th piece, when it is on the right of the cut;
read on the suffix, it does not depend on the cut. -/
def entryR (init : Q) (cs : List Q) (i : ℕ) : ℕ × Q := (1, cs.getD (i - 1) init)

lemma entryC_eq_entryL (init : Q) (n₀ : ℕ) (cs : List Q) {i : ℕ} (h : flipn true i = true) :
    entryC init n₀ true (0, init) cs i = entryL init n₀ cs i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [entryC, entryL]
  · simp [entryC, entryL, hi.ne', h, nxt]

lemma entryC_eq_entryR (init : Q) (n₀ : ℕ) (cs : List Q) {i : ℕ} (h : flipn true i = false) :
    entryC init n₀ true (0, init) cs i = entryR init cs i := by
  have hi : i ≠ 0 := by rintro rfl; simp at h
  simp [entryC, entryR, hi, h, nxt]

end RegHankel

end Lax916827Proofs.Transducers
