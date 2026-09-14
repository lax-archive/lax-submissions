/-
The injective encoding of strings by numbers used in the proof of
Theorem `thm:equivalence-rational-functions` of *Transducers* (M. Bojańczyk).

Following the book, output strings are represented by numbers: a string
`a₁ ⋯ a_n` over an alphabet of numbers smaller than `K - 1` is represented by the
number whose base-`K` digits are `a₁ + 1, …, a_n + 1` (the shift by one avoids
leading zeros, so that the representation is injective).  The digits are read
from the left, so that the representation is *additive on the left*:

  `iota K (u ++ v) = iota K u + K ^ |u| * iota K v`,

which is what makes the map computable by a weighted automaton: the matrix

  `⟦v⟧ = !![K ^ |v|, iota K v; 0, 1]`

is multiplicative, and the automaton of `RequestProject/PartB/PairWeighted.lean`
is exactly the automaton of these two-by-two matrices.
-/
import Mathlib.Computability.Primrec.List
import Mathlib.Tactic

namespace Lax132576Proofs.Transducers
namespace Iota

/-- The number representing a string in base `K`, with the digit of a letter `a`
equal to `a + 1`. -/
def iota (K : ℕ) (v : List ℕ) : ℕ := v.foldr (fun a s => (a + 1) + K * s) 0

@[simp] lemma iota_nil (K : ℕ) : iota K [] = 0 := rfl

@[simp] lemma iota_cons (K a : ℕ) (v : List ℕ) :
    iota K (a :: v) = (a + 1) + K * iota K v := rfl

lemma iota_append (K : ℕ) (u v : List ℕ) :
    iota K (u ++ v) = iota K u + K ^ u.length * iota K v := by
  induction u with
  | nil => simp
  | cons a u ih =>
      simp only [List.cons_append, iota_cons, ih, List.length_cons, pow_succ]
      ring

/-- The representation is injective on strings whose letters are smaller than
`K - 1`. -/
lemma iota_inj {K : ℕ} : ∀ {u v : List ℕ}, (∀ x ∈ u, x + 1 < K) → (∀ x ∈ v, x + 1 < K) →
    iota K u = iota K v → u = v := by
  intro u
  induction u with
  | nil =>
      rintro (_ | ⟨b, v⟩) hu hv h
      · rfl
      · rw [iota_nil, iota_cons] at h; omega
  | cons a u ih =>
      rintro (_ | ⟨b, v⟩) hu hv h
      · rw [iota_nil, iota_cons] at h; omega
      · rw [iota_cons, iota_cons] at h
        have ha : a + 1 < K := hu a (by simp)
        have hb : b + 1 < K := hv b (by simp)
        have hab : a = b ∧ iota K u = iota K v := by
          rcases lt_trichotomy (iota K u) (iota K v) with hlt | heq | hgt
          · exfalso
            have h1 : K * (iota K u + 1) ≤ K * iota K v :=
              Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hlt)
            rw [Nat.mul_add, Nat.mul_one] at h1
            omega
          · rw [heq] at h; omega
          · exfalso
            have h1 : K * (iota K v + 1) ≤ K * iota K u :=
              Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hgt)
            rw [Nat.mul_add, Nat.mul_one] at h1
            omega
        rw [hab.1]
        rw [ih (fun x hx => hu x (by simp [hx])) (fun x hx => hv x (by simp [hx])) hab.2]

/-- The number representing a string is smaller than `K ^ |v|`, provided the
letters are smaller than `K - 1`. -/
lemma iota_lt_pow {K : ℕ} : ∀ {v : List ℕ}, (∀ x ∈ v, x + 1 < K) → iota K v < K ^ v.length := by
  intro v
  induction v with
  | nil => intro _; simp
  | cons a v ih =>
      intro hv
      have ha : a + 1 < K := hv a (by simp)
      have h := ih (fun x hx => hv x (by simp [hx]))
      have h1 : K * (iota K v + 1) ≤ K * K ^ v.length :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt h)
      rw [Nat.mul_add, Nat.mul_one] at h1
      have : K * iota K v + K ≤ K * K ^ v.length := by omega
      simp only [iota_cons, List.length_cons, pow_succ]
      calc a + 1 + K * iota K v < K + K * iota K v := by omega
        _ ≤ K * K ^ v.length := by omega
        _ = K ^ v.length * K := by ring

lemma primrec_iota : Primrec₂ iota := by
  have H : Primrec (fun p : ℕ × List ℕ =>
      p.2.foldr (fun (b : ℕ) (s : ℕ) => (b + 1) + p.1 * s) 0) :=
    Primrec.list_foldr (f := fun p : ℕ × List ℕ => p.2) (g := fun _ => (0 : ℕ))
      (h := fun (p : ℕ × List ℕ) (x : ℕ × ℕ) => (x.1 + 1) + p.1 * x.2)
      Primrec.snd (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)))
  exact H

end Iota
end Lax132576Proofs.Transducers
