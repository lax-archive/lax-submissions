import Lax185574Proofs.RamSimulateBack

/-!
Running a program `D` word-length levels lower.

`simulate_sound` with the identity rewrite runs a program at word
length `w - 1` on the input of the simulator, in both directions.
Iterating it `D` times runs the program at `w - D`. A composite uses
this to make the outputs of a stage small compared with the word length
of the next stage, since every output entry of a run at word length `v`
is below `2 ^ v`.
-/

namespace Lax185574Proofs.Simulate

open Lax808846.Ram Lax185574Proofs.RamSim

/-- The identity rewrite. -/
def idRw : Rewrite 1 := [.slice 0 (.lit 0) none]

theorem idRw_apply (x : List ℕ) : idRw.apply (fun _ => x) = x := by
  simp [idRw, Rewrite.apply, Segment.apply, HExpr.eval]

theorem idRw_cost (x : List ℕ) : idRw.cost (fun _ => x) = 3 := by
  simp [idRw, Rewrite.cost, Segment.cost, HExpr.cost]

theorem idRw_fits {w : ℕ} {x : List ℕ} (hx : x.length < 2 ^ w) : idRw.Fits w (fun _ => x) := by
  refine ⟨fun _ => hx, by rw [idRw_apply]; exact hx, ?_⟩
  intro seg hseg
  simp only [idRw, List.mem_cons, List.mem_nil_iff, or_false] at hseg
  subst hseg
  exact ⟨trivial, by simp [HExpr.eval]⟩

/-- **Lowering.** For every program `p₀` and every `D` there is a
program that runs `p₀` at word length `w - D`, in both directions. -/
theorem lower : ∀ (D : ℕ) (p₀ : Program), ∃ (p : Program) (K : ℕ), 1 ≤ K ∧
    ∀ (w : ℕ) (x : List ℕ), K ≤ 2 ^ (w - D) → x.length < 2 ^ (w - D) →
      (∀ y t, RunsTo (w - D) p₀ x y t → ∃ t' ≤ K * (t + 1), RunsTo w p x y t') ∧
      (∀ y T, RunsTo w p x y T → ∃ t ≤ T, RunsTo (w - D) p₀ x y t)
  | 0, p₀ => ⟨p₀, 1, le_rfl, fun w x _ _ =>
      ⟨fun y t h => ⟨t, by omega, by simpa using h⟩,
       fun y T h => ⟨T, le_rfl, by simpa using h⟩⟩⟩
  | D + 1, p₀ => by
      obtain ⟨q, Kq, hKq, hq⟩ := lower D p₀
      obtain ⟨p, Ks, hs⟩ := simulate_sound q idRw
      refine ⟨p, Ks * Kq + 3 * Ks + Ks + Kq + 1, by omega, fun w x hK hx => ?_⟩
      have hwD : w - (D + 1) = w - 1 - D := by omega
      rw [hwD] at hK hx ⊢
      have hle : 2 ^ (w - 1 - D) ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hle' : 2 ^ (w - 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hKs : Ks ≤ 2 ^ (w - 1) := by
        have : Ks ≤ Ks * Kq + 3 * Ks + Ks + Kq + 1 := by omega
        omega
      have hKq' : Kq ≤ 2 ^ (w - 1 - D) := by omega
      obtain ⟨hf, hb⟩ := hs w x hKs (idRw_fits (by omega))
      obtain ⟨hqf, hqb⟩ := hq (w - 1) x hKq' hx
      simp only [idRw_apply, idRw_cost] at hf hb
      refine ⟨fun y t h => ?_, fun y T h => ?_⟩
      · obtain ⟨t₁, ht₁, h₁⟩ := hqf y t h
        obtain ⟨t₂, ht₂, h₂⟩ := hf y t₁ h₁
        refine ⟨t₂, le_trans ht₂ ?_, h₂⟩
        have : Ks * t₁ ≤ Ks * (Kq * (t + 1)) := Nat.mul_le_mul_left _ ht₁
        nlinarith
      · obtain ⟨t₁, ht₁, h₁⟩ := hb y T h
        obtain ⟨t₂, ht₂, h₂⟩ := hqb y t₁ h₁
        exact ⟨t₂, by omega, h₂⟩

end Lax185574Proofs.Simulate
