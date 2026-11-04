import Lax185574Proofs.RamPipeBack
import Lax185574Proofs.RamLower

/-!
Running a program on a converted input.

A converter `R` turns the input `x` into a word `y`, and a program `P`
runs on a rewrite of `y` and `x`. The pipe of `R` into `P` runs both at
the word length `w - 2`. If `R` halts on `x` with output `y`, and `P`
halts on the rewrite with output `z` and has no other output there, then
the pipe halts on `x` with output `z` within a constant times the sum of
the two running times, and every halting run of the pipe outputs `z`.
So the pipe inherits both clauses of a `Computes` statement of `P`,
provided the converter halts at the word lengths in question.
-/

namespace Lax185574Proofs.Interface

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.Simulate

/-- **A converter followed by a program.** -/
theorem pipe_after (R P : Program) (ρ' : Rewrite 2) : ∃ (p : Program) (K : ℕ),
    ∀ (w : ℕ) (x y z : List ℕ) (t₁ t₂ : ℕ), K ≤ 2 ^ (w - 2) → x.length < 2 ^ (w - 2) →
      y.length < 2 ^ (w - 2) → ρ'.Fits w ![y, x] →
      RunsTo (w - 2) R x y t₁ → RunsTo (w - 2) P (ρ'.apply ![y, x]) z t₂ →
      (∀ z' t, RunsTo (w - 2) P (ρ'.apply ![y, x]) z' t → z' = z) →
      (∃ t ≤ K * (t₁ + t₂ + 3 + ρ'.cost ![y, x]), RunsTo w p x z t) ∧
      (∀ z' t, RunsTo w p x z' t → z' = z) := by
  obtain ⟨p, K, hp⟩ := pipe_sound R P idRw ρ'
  refine ⟨p, K, fun w x y z t₁ t₂ hK hx hy hfit h₁ h₂ hP => ?_⟩
  have hxw : x.length < 2 ^ w :=
    lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le w 2))
  obtain ⟨hf, hb⟩ := hp w x hK (idRw_fits hxw)
  simp only [idRw_apply, idRw_cost] at hf hb
  refine ⟨hf y z t₁ t₂ hy.le hfit h₁ h₂, fun z' t h => ?_⟩
  obtain ⟨y', t₁', -, -, h₁', h₂'⟩ := hb z' t h
  obtain ⟨rfl, -⟩ := runsTo_unique h₁' h₁
  obtain ⟨t₂', -, h₂''⟩ := h₂' hfit
  exact hP z' t₂' h₂''

end Lax185574Proofs.Interface
