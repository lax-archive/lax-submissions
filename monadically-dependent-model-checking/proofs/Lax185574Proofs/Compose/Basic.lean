import Lax185574Proofs.Legacy
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Small facts used when programs are composed: the word of a script
determines the script, and a running time `a · ⌊b · P⌋ + d` is absorbed
by a single bound `⌊c · P⌋` once `P ≥ 1`.
-/

namespace Lax185574Proofs.Compose

open Lax185574.WordEncoding Lax185574.SequenceEncoding

/-- The word of a list of natural numbers is its length, then its
entries. -/
theorem toWord_list_nat (l : List ℕ) : toWord l = l.length :: l := by
  change l.length :: (l.map fun n => [n]).flatten = _
  congr 1
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem stepCode_length (s : Step) : (toWord s).length = 3 := by
  cases s <;> rfl

theorem stepCode_injective {s t : Step} (h : toWord s = toWord t) : s = t := by
  cases s <;> cases t <;> simp_all [word_simps, stepCode]

theorem flatten_steps_injective :
    ∀ {l l' : List Step}, l.length = l'.length →
      (l.map toWord).flatten = (l'.map toWord).flatten → l = l'
  | [], [], _, _ => rfl
  | s :: l, t :: l', hlen, h => by
      simp only [List.map_cons, List.flatten_cons] at h
      obtain ⟨h1, h2⟩ := List.append_inj h (by rw [stepCode_length, stepCode_length])
      rw [stepCode_injective h1, flatten_steps_injective (by simpa using hlen) h2]

/-- The word of a script determines the script. -/
theorem script_toWord_injective {n : ℕ} {σ τ : Script n} (h : toWord σ = toWord τ) : σ = τ := by
  obtain ⟨cσ, sσ⟩ := σ
  obtain ⟨cτ, sτ⟩ := τ
  change toWord (List.ofFn cσ) ++ toWord sσ = toWord (List.ofFn cτ) ++ toWord sτ at h
  rw [toWord_list_nat, toWord_list_nat] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  have hc : cσ = cτ := List.ofFn_injective (List.cons_eq_cons.mp h1).2
  change sσ.length :: (sσ.map toWord).flatten = sτ.length :: (sτ.map toWord).flatten at h2
  obtain ⟨hl, hf⟩ := List.cons_eq_cons.mp h2
  rw [hc, flatten_steps_injective hl hf]

/-- A word encodes at most one sequence of partial graphs. -/
theorem encodesSequence_unique {n : ℕ} {y : List ℕ}
    {s s' : List (Lax185574.PartialGraphs.PartialGraph (Fin n))}
    (h : EncodesSequence y s) (h' : EncodesSequence y s') : s = s' := by
  obtain ⟨σ, rfl, rfl⟩ := h
  obtain ⟨τ, hτ, rfl⟩ := h'
  rw [script_toWord_injective hτ]

/-- A running time `a · ⌊b · P⌋ + d` is at most `⌊(a · b + d) · P⌋`
when `P ≥ 1`. -/
theorem mul_floor_add_le {a b d : ℕ} {P : ℝ} (hP : 1 ≤ P) :
    a * ⌊(b : ℝ) * P⌋₊ + d ≤ ⌊((a * b + d : ℕ) : ℝ) * P⌋₊ := by
  apply Nat.le_floor
  have hb : (0 : ℝ) ≤ b * P := by positivity
  have h1 : (⌊(b : ℝ) * P⌋₊ : ℝ) ≤ b * P := Nat.floor_le hb
  push_cast
  have h2 : (a : ℝ) * ⌊(b : ℝ) * P⌋₊ ≤ a * (b * P) :=
    mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg a)
  have h3 : (d : ℝ) ≤ d * P := le_mul_of_one_le_right (Nat.cast_nonneg d) hP
  nlinarith

/-- `⌊b · P⌋` is monotone in the natural factor `b`. -/
theorem floor_mul_mono {b c : ℕ} {P : ℝ} (hP : 0 ≤ P) (h : b ≤ c) :
    ⌊(b : ℝ) * P⌋₊ ≤ ⌊(c : ℝ) * P⌋₊ :=
  Nat.floor_le_floor (mul_le_mul_of_nonneg_right (by exact_mod_cast h) hP)

end Lax185574Proofs.Compose
